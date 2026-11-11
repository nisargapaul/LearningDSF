"""SIREN, unbiased coordinate sampling, GKL training and coupling inversion."""

import math
import time
from pathlib import Path
import numpy as np
from scipy.stats import qmc
import torch
from torch import nn
from .physics import channels
from .run import seed_for, read_json, write_json

INTENSITY_SCALE = .1


def resolve_device(device):  # Choose CPU or available GPU.
    return torch.device('cuda' if torch.cuda.is_available() else 'cpu') if str(device) == 'auto' else torch.device(device)


class SineLayer(nn.Module):
    def __init__(self, input_width, output_width, first=False):  # Initialize a SIREN layer.
        super().__init__()
        self.linear = nn.Linear(input_width, output_width)
        self.omega_0 = 30.
        bound = 1/input_width if first else math.sqrt(6/input_width)/30  # SIREN weight scale.
        with torch.no_grad():
            self.linear.weight.uniform_(-bound, bound)
            nn.init.zeros_(self.linear.bias)

    def forward(self, x):  # Apply the sine activation.
        return torch.sin(self.omega_0*self.linear(x))


class FieldINR(nn.Module):
    def __init__(self, depth=5, width=128):  # Build the spectral surrogate.
        super().__init__()
        self.depth, self.width = depth, width
        self.body = nn.Sequential(*[SineLayer(12 if i == 0 else width, width, first=i == 0) for i in range(depth)])
        self.head = nn.Linear(width, 1)
        nn.init.uniform_(self.head.weight, -math.sqrt(6/width)/30, math.sqrt(6/width)/30)
        nn.init.constant_(self.head.bias, -5.)

    def forward(self, x):  # Return nonnegative spectral intensity.
        raw = self.head(self.body(x)).squeeze(-1)
        return INTENSITY_SCALE*torch.expm1(nn.functional.softplus(raw).clamp(max=12.))


def fixed_features(omega, field=0., n_sites=12):  # Encode momentum, frequency, and polarization.
    if field != 0:
        raise ValueError('The INR uses zero-field data only.')
    channel = channels(n_sites)
    scale = np.maximum(abs(channel[:,:2]).max(axis=0), 1.)
    line = np.repeat(np.arange(len(channel)), len(omega))
    return np.column_stack((channel[line,:2]/scale, np.tile(omega/8.,len(channel)), channel[line,2:])).astype(np.float32)


class Coordinates:
    """Uniform Hamiltonians/lines; half-uniform energy sampling with unbiased weights."""
    def __init__(self, directory, budget=None):  # Load a nested training subset.
        directory = Path(directory)
        self.theta, self.omega = np.load(directory/'theta.npy'), np.load(directory/'omega.npy')
        self.n = len(self.theta) if budget is None else budget
        data = []
        for i in range(self.n):
            with np.load(directory/f'shards/{i:05d}.npz') as shard:
                data.append(shard['spectra'].astype(np.float32))
                if i == 0:
                    self.mapping, self.n_sites = shard['mapping'], int(shard['n_sites'])
                np.testing.assert_array_equal(shard['mapping'], self.mapping)
                if int(shard['n_sites']) != self.n_sites:
                    raise ValueError('Mixed system sizes in one dataset.')
        self.spectra = np.stack(data)
        self.mass = self.spectra.sum(axis=-1, dtype=np.float64)
        self.cdf = np.cumsum(self.spectra, axis=-1, dtype=np.float64)
        np.divide(self.cdf, self.mass[:,:,None], out=self.cdf, where=self.mass[:,:,None] > 0)
        self.cdf[:,:,-1] = 1.
        self.fixed = fixed_features(self.omega,n_sites=self.n_sites)

    def sample(self, rng, size, field=0.):  # Mix uniform and peak sampling.
        if field != 0:
            raise ValueError('Finite field in zero-field INR.')
        model = rng.integers(self.n, size=size)
        line = rng.integers(len(self.mapping), size=size)
        unique = self.mapping[line]
        freq = rng.integers(len(self.omega), size=size)
        mass = self.mass[model,unique]
        informative = mass > 1e-24
        ids = np.flatnonzero((rng.random(size) < .5) & informative)  # Half the bins follow spectral weight.
        if len(ids):
            uniform = rng.random(len(ids))
            low, high = np.zeros(len(ids),dtype=int), np.full(len(ids),len(self.omega)-1)
            while np.any(low < high):
                mid = (low+high)//2
                before = self.cdf[model[ids],unique[ids],mid] < uniform
                low, high = np.where(before,mid+1,low), np.where(before,high,mid)
            freq[ids] = low
        target = self.spectra[model,unique,freq]
        probability = np.ones(size)
        probability[informative] = .5+.5*len(self.omega)*target[informative]/mass[informative]
        features = np.column_stack((self.fixed[line*len(self.omega)+freq],self.theta[model])).astype(np.float32)
        return features, target, (1/probability).astype(np.float32)  # Correct back to a uniform-grid objective.


def generalized_kl(prediction, target):  # GKL per spectral bin.
    p = prediction.clamp_min(1e-12)  # GKL(p,y) = p-y+y*log(y/p), with 0*log(0)=0.
    return p-target+torch.where(target > 0, target*(target.clamp_min(1e-12).log()-p.log()), 0.)


def atomic_torch(path, payload):  # Save a complete checkpoint.
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix+'.tmp')
    torch.save(payload, temporary)
    temporary.replace(path)


def load_model(path, device='cpu'):  # Restore trained network weights.
    payload = torch.load(path, map_location='cpu', weights_only=False)
    if (payload.get('field'), payload['depth'], payload['width']) != (0., 5, 128):
        raise ValueError('Expected a zero-field, five-layer width-128 checkpoint.')
    model = FieldINR(payload['depth'], payload['width'])
    model.field = 0.
    model.load_state_dict(payload['model'])
    return model.to(resolve_device(device)).eval(), payload


def checkpoint_path(root, budget, depth, seed):  # Locate a budget/seed checkpoint.
    return Path(root)/'checkpoints'/f'b{budget}_d{depth}_w128_s{seed}.pt'


def train_one(root, config, budget, depth, seed, device='auto'):  # Train and select on validation.
    root, device, field = Path(root), resolve_device(device), float(config['field'])
    path = checkpoint_path(root,budget,depth,seed)
    done, last = path.with_suffix('.json'), path.with_suffix('.last.pt')
    if done.exists():
        record = read_json(done)
        if record.get('field') != field:
            raise ValueError('Completed training record has a different field.')
        return record
    torch.manual_seed(seed_for(30,budget,depth,seed))
    rng = np.random.default_rng(seed_for(31,budget,depth,seed))
    train, validation = Coordinates(root/'data/train',budget), Coordinates(root/'data/validation')
    model = FieldINR(depth).to(device)
    optimizer = torch.optim.Adam(model.parameters(),lr=2e-4,eps=1e-7)
    base_steps, batch_size = config['steps'], config['batch_size']
    every, valid_size = (4,2048) if config['profile'] == 'smoke' else (250,65536)
    valid = [torch.from_numpy(v).to(device) for v in validation.sample(np.random.default_rng(seed_for(32)),valid_size,field)]
    step, target_steps, best_loss, history, elapsed_before = 0, base_steps, float('inf'), [], 0.
    if last.exists():
        state = torch.load(last,map_location='cpu',weights_only=False)
        if state.get('field') != field:
            raise ValueError('Resumable checkpoint has a different field.')
        model.load_state_dict(state['model'])
        # PyTorch restores optimizer tensors onto their parameter devices.
        optimizer.load_state_dict(state['optimizer'])
        step, target_steps, best_loss = state['step'], state['target_steps'], state['best_loss']
        history, elapsed_before, rng.bit_generator.state = state['history'], state['seconds'], state['rng']
    started = time.perf_counter()

    def validation_loss():  # Evaluate the fixed validation sample.
        model.eval()
        value = 0.
        with torch.no_grad():
            for start in range(0,valid_size,batch_size):
                x,y,w = [a[start:start+batch_size] for a in valid]
                value += float((generalized_kl(model(x),y)*w).sum().cpu())
        model.train()
        return value/valid_size/INTENSITY_SCALE

    while step < target_steps:
        if time.time() >= config.get('compute_deadline_unix',float('inf')):
            raise TimeoutError('Compute deadline; the latest checkpoint is resumable.')
        step += 1
        lr = 2e-4*(.02+.98*(1+math.cos(math.pi*(step-1)/target_steps))/2)
        for group in optimizer.param_groups:
            group['lr'] = lr
        x,y,w = [torch.from_numpy(v).to(device) for v in train.sample(rng,batch_size,field)]
        optimizer.zero_grad(set_to_none=True)
        loss = (generalized_kl(model(x),y)*w).mean()/INTENSITY_SCALE
        if not torch.isfinite(loss):
            raise FloatingPointError('Nonfinite training objective.')
        loss.backward()
        optimizer.step()
        if step == 1 or step % every == 0 or step == target_steps:
            value = validation_loss()
            seconds = elapsed_before+time.perf_counter()-started
            history.append(dict(step=step,validation=value,train=float(loss.detach().cpu()),seconds=seconds))
            if value < best_loss:  # Checkpoint selection uses validation data only.
                best_loss = value
                atomic_torch(path,dict(model=model.state_dict(),n_sites=config['n_sites'],
                    training_manifest_sha256=config.get('training_manifest_sha256'),depth=depth,width=128,
                    budget=budget,seed=seed,step=step,validation_loss=best_loss,field=field,
                    coordinate_order=['qx','qy','centered_omega','ax','ay','az','bx','by','bz','J','K','Gamma']))
            if step == base_steps and config['profile'] != 'smoke':
                early = min(history,key=lambda r: abs(r['step']-.75*base_steps))['validation']
                if value < .99*early:  # Extend training if still improving by more than 1%.
                    target_steps = 2*base_steps
            atomic_torch(last,dict(model=model.state_dict(),optimizer=optimizer.state_dict(),step=step,
                target_steps=target_steps,best_loss=best_loss,history=history,rng=rng.bit_generator.state,
                seconds=elapsed_before+time.perf_counter()-started,field=field))
            print(f'train b={budget} s={seed} {step}/{target_steps} val={value:.5g}',flush=True)
    recent = min(history,key=lambda r: abs(r['step']-.75*step))['validation']
    record = dict(n_sites=config['n_sites'],training_manifest_sha256=config.get('training_manifest_sha256'),
        budget=budget,depth=depth,width=128,seed=seed,steps=step,field=field,best_validation=best_loss,
        seconds=elapsed_before+time.perf_counter()-started,convergence_unresolved=bool(history[-1]['validation'] < .99*recent),
        history=history,pilot=False,train_hamiltonians=budget,
        train_diagonalizations=config.get('diagonalizations_per_hamiltonian',6)*budget)
    write_json(done,record)
    return record


class Inverter:
    def __init__(self, model, omega, field, device, n_sites=12):  # Freeze the trained network.
        if hasattr(model,'field') and not np.isclose(model.field,field):
            raise ValueError('Checkpoint and acquisition fields differ.')
        self.device = resolve_device(device)
        self.model = model.to(self.device).eval()
        for parameter in model.parameters():
            parameter.requires_grad_(False)  # Inference optimizes couplings, not network weights.
        self.base = torch.from_numpy(fixed_features(omega,field,n_sites)).to(self.device)
        self.length = len(self.base)

    def predict(self, base, theta):  # Evaluate candidate coupling vectors.
        if theta.ndim == 1:
            theta = theta[None,:]
        features = torch.cat([base[None,:,:].expand(len(theta),-1,-1),
                              theta[:,None,:].expand(-1,len(base),-1)],dim=-1)
        return self.model(features.reshape(-1,12)).reshape(len(theta),len(base))

    def fit(self, counts, gain, config, seed):  # Fit couplings to calibrated spectra.
        """Freeze weights and fit only couplings; floating expected counts are noiseless."""
        started, rng, device = time.perf_counter(), np.random.default_rng(seed), self.device
        flat = np.asarray(counts).ravel()
        if len(flat) != self.length or not np.isfinite(flat).all() or (flat < 0).any() or flat.sum() <= 0:
            raise ValueError('Expected a finite, nonnegative, nonempty full-grid histogram.')
        tensor = lambda x: torch.from_numpy(np.asarray(x,dtype=np.float32)).to(device)
        observed, total = tensor(flat), float(flat.sum())
        positive = np.flatnonzero(flat)
        cdf = np.cumsum(flat[positive],dtype=np.float64)
        cdf /= cdf[-1]
        batch, chunk = (256 if config['profile'] == 'smoke' else 2048), 32768

        def sample(size):  # Sample bins with unbiased weights.
            index = rng.integers(self.length,size=size)
            peak = rng.random(size) < .5
            index[peak] = positive[np.searchsorted(cdf,rng.random(np.sum(peak)))]
            weight = 1/(.5+.5*self.length*flat[index]/total)
            return torch.from_numpy(index).to(device), tensor(weight)

        def objective(theta, index, weight):  # Estimate full-grid GKL.
            prediction = self.predict(self.base[index],theta)*gain
            return (generalized_kl(prediction,observed[index][None,:])*weight[None,:]).mean(dim=1)*self.length/total

        def full(theta, backward=False):  # Evaluate GKL over every bin.
            value = 0.
            for lo in range(0,self.length,chunk):
                # Rebuild tanh for every gradient chunk during L-BFGS.
                parameter = theta() if callable(theta) else theta
                prediction = self.predict(self.base[lo:lo+chunk],parameter)*gain
                part = generalized_kl(prediction,observed[lo:lo+chunk][None,:]).sum()/total
                if backward:
                    part.backward()
                value += float(part.detach().cpu())
            return value

        starts = qmc.Sobol(3,scramble=True,seed=seed).random_base2(
            int(np.ceil(np.log2(config['screening']))))[:config['screening']]*2-1
        check_index, check_weight = sample(1024 if config['profile'] == 'smoke' else 8192)
        with torch.no_grad():
            scores = np.concatenate([objective(tensor(starts[lo:lo+8]),check_index,check_weight).cpu().numpy()
                                     for lo in range(0,len(starts),8)])
        starts = starts[np.argsort(scores)[:config['restarts']]]
        logits = nn.Parameter(torch.atanh(tensor(starts).clamp(-.9999,.9999)))  # tanh enforces [-1,1] bounds.
        optimizer = torch.optim.Adam([logits],lr=.025,eps=1e-7)
        best_units, best_scores = starts.copy(), np.full(len(starts),np.inf)
        for step in range(config['fit_steps']):
            index, weight = sample(batch)
            optimizer.zero_grad(set_to_none=True)
            objective(torch.tanh(logits),index,weight).sum().backward()
            optimizer.step()
            if step % 25 == 0 or step == config['fit_steps']-1:
                with torch.no_grad():
                    units = torch.tanh(logits)
                    values = objective(units,check_index,check_weight).cpu().numpy()
                    improved = values < best_scores
                    best_scores[improved], best_units[improved] = values[improved], units.cpu().numpy()[improved]
        with torch.no_grad():
            full_scores = [full(tensor(theta)) for theta in best_units]
        best, best_full = np.array(best_units[np.argmin(full_scores)],copy=True), min(full_scores)  # Select by data loss.
        if config['polish_steps']:
            parameter = nn.Parameter(torch.atanh(tensor(best).clamp(-.9999,.9999)))
            polishing = torch.optim.LBFGS([parameter],lr=.5,max_iter=config['polish_steps'],
                line_search_fn='strong_wolfe',tolerance_grad=1e-7,tolerance_change=1e-9)

            def closure():  # Polish couplings using full-grid gradients.
                nonlocal best, best_full
                polishing.zero_grad(set_to_none=True)
                value = full(lambda: torch.tanh(parameter),backward=True)
                if value < best_full:
                    best_full, best = value, torch.tanh(parameter).detach().cpu().numpy().copy()
                return torch.tensor(value,device=device)

            polishing.step(closure)
            with torch.no_grad():
                final = torch.tanh(parameter)
                value = full(final)
                if value < best_full:
                    best_full, best = value, final.cpu().numpy().copy()
        return best, dict(seconds=time.perf_counter()-started,objective=best_full,
            **{key: config[key] for key in ('screening','restarts','fit_steps','polish_steps')},
            restart_full_objectives=full_scores)
