"""Strong-field tomography: moments, linear recovery, and saved-data plots."""
import os
for key in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','VECLIB_MAXIMUM_THREADS'):
    os.environ[key] = '1'
os.environ.setdefault('MPLBACKEND','Agg')
import argparse
from concurrent.futures import ProcessPoolExecutor
import csv
import hashlib
import json
from pathlib import Path
import sys
import time
if not __package__:
    sys.path[0] = str(Path(__file__).resolve().parent.parent)
    __package__ = Path(__file__).resolve().parent.name
import numpy as np
from .physics import centered_moments, spectrum_field

HERE = Path(__file__).resolve().parent
DATA, RUNS = HERE/'data', HERE.parent/'runs'/'sf'
TRIALS, QUANTILES = 5000, [.375,.5,.625]
STUDIES = ('field','coefficients','parameters','supplement','known','spectra')

def digest(path):  # Hash inputs and checkpoints.
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def load(group):  # Read one completed study.
    with np.load(DATA/'results.npz') as d:
        return {k[len(group)+1:]:d[k] for k in d.files if k.startswith(group+'_')}

def save(path, **values):  # Replace complete output files atomically.
    path = Path(path); path.parent.mkdir(parents=True,exist_ok=True)
    temporary = path.with_suffix('.tmp.npz')
    np.savez_compressed(temporary,**values); temporary.replace(path)

def quantiles(errors, axis=-1):  # Median and central 25% of errors.
    return np.moveaxis(np.quantile(errors,QUANTILES,axis=axis),0,-1)

def field_summary(d):  # Gaussian moment noise followed by the SF inverse.
    inverse = np.linalg.pinv(d['design'])
    estimates = d['moments']@inverse.T
    rng = np.random.default_rng(20261016)
    rng.normal(size=(TRIALS,15))  # Preserve the shared HT/SF campaign's draw ordering.
    noise = rng.normal(size=(TRIALS,281))@inverse.T
    clean = np.linalg.norm(estimates-d['theta'],axis=1)/np.linalg.norm(d['theta'])
    bands = np.array([quantiles(np.linalg.norm(estimates[:,None]-d['theta']+sigma*noise[None],axis=-1)
                     /np.linalg.norm(d['theta'])) for sigma in d['sigmas']])
    return dict(estimates=estimates,clean=clean,bands=bands,projected_noise=noise)

def coefficient_summary(d):  # Linear full/diagonal recovery from noisy asymptotic coefficients.
    inverse = [np.linalg.pinv(d['design']),np.linalg.pinv(d['design'][d['diagonal']])]
    z = np.random.default_rng(20261016).normal(size=(len(d['theta']),int(d['trials']),len(d['design'])))
    projected = np.stack([z@inverse[0].T,z[...,d['diagonal']]@inverse[1].T],axis=1)
    errors = np.linalg.norm(projected,axis=-1)/np.linalg.norm(d['theta'],axis=1)[:,None,None]
    members = errors.mean(axis=-1)  # Average noise trials within each Hamiltonian.
    rng = np.random.default_rng(20261010); bootstrap = np.empty((5000,2))
    for start in range(0,5000,64):
        stop = min(start+64,5000)
        ids = rng.integers(len(members),size=(stop-start,len(members)))
        bootstrap[start:stop] = members[ids].mean(axis=1)  # Resample Hamiltonians, keeping paired trials.
    low, high = np.quantile(bootstrap,[.375,.625],axis=0)
    return dict(projected_noise=projected,member_means=members[:,None]*d['sigmas'][None,:,None],
                mean=d['sigmas'][:,None]*members.mean(axis=0),low=d['sigmas'][:,None]*low,high=d['sigmas'][:,None]*high)

def parameter_summary(d):  # Known supports; omitted exchanges are zero.
    medians = np.empty((len(d['sigmas']),len(d['counts']),len(d['order'])))
    estimates = np.zeros_like(d['theta']); clean = np.empty(d['theta'].shape[:2])
    for member, order in enumerate(d['order']):
        rng = np.random.default_rng(np.random.SeedSequence([20261015,member]))
        rng.normal(size=(TRIALS,27))  # Skip the paired HT draws, retaining the original SF draws.
        z = rng.normal(size=(TRIALS,len(d['design'])))
        for ip,count in enumerate(d['counts']):
            ids = order[:count]; inverse = np.linalg.pinv(d['design'][:,ids],rcond=1e-12)
            estimate, noise = inverse@d['moments'][ip,member], z@inverse.T
            bias = estimate-d['theta'][ip,member,ids]
            estimates[ip,member,ids] = estimate; clean[ip,member] = np.linalg.norm(bias)
            for level,sigma in enumerate(d['sigmas']):
                medians[level,ip,member] = np.median(np.linalg.norm(bias+sigma*noise,axis=1))
    return dict(estimates=estimates,clean=clean,member_medians=medians,bands=quantiles(medians,axis=2))

def supplement_summary(d, sigmas):  # Two-target field sweep and fixed-field noise sweep.
    inverse = np.linalg.pinv(d['design']); estimates = d['moments']@inverse.T
    norms = np.linalg.norm(d['theta'],axis=1); rng = np.random.default_rng(0)
    bands = np.empty((*estimates.shape[:2],3))
    for k in range(len(d['fields'])):
        noise = rng.normal(0,.05,(TRIALS,len(d['noise_keep'])))[:,d['noise_keep']]@inverse.T
        for case,theta in enumerate(d['theta']):
            bands[case,k] = quantiles(np.linalg.norm(estimates[case,k]+noise-theta,axis=1)/norms[case])
    z = np.random.default_rng(0).normal(size=(TRIALS,len(d['noise_keep'])))[:,d['noise_keep']]
    delta = z@inverse.T; covariance = inverse@inverse.T
    index = np.flatnonzero(d['fields']==32)[0]; noise_bands, rms = [], []
    for case,theta in enumerate(d['theta']):
        bias = estimates[case,index]-theta
        errors = np.linalg.norm(bias+sigmas[:,None,None]*delta,axis=-1)/norms[case]
        noise_bands.append(quantiles(errors))
        rms.append(np.column_stack([np.sqrt(np.mean(errors**2,axis=1)),
            np.sqrt(bias@bias+sigmas**2*np.trace(covariance))/norms[case]]))
    return dict(estimates=estimates,clean=np.linalg.norm(estimates-d['theta'][:,None],axis=-1)/norms[:,None],
                bands=bands,noise_bands=np.array(noise_bands),noise_rms=np.array(rms),
                noise_asymptotes=np.median(np.linalg.norm(delta,axis=1))/norms)

def known_summary(d):  # Subtract the exactly supplied exchanges before fitting.
    errors = np.empty((len(d['theta']),27,TRIALS)); clean = np.empty(errors.shape[:2])
    conditions = np.empty_like(clean); noise_rms = np.empty_like(clean)
    for member,(truth,order,measured) in enumerate(zip(d['theta'],d['order'],d['moments'])):
        noise = np.random.default_rng(20260915+1000+member).normal(0,.05,(TRIALS,len(d['design'])))
        for count in range(1,28):
            unknown,known = order[:count],order[count:]; design = d['design'][:,unknown]
            inverse = np.linalg.pinv(design)
            bias = inverse@(measured-d['design'][:,known]@truth[known])-truth[unknown]
            clean[member,count-1] = np.linalg.norm(bias)/np.linalg.norm(truth)
            errors[member,count-1] = np.linalg.norm(bias+noise@inverse.T,axis=1)/np.linalg.norm(truth)
            conditions[member,count-1] = np.linalg.cond(design)
            noise_rms[member,count-1] = .05*np.linalg.norm(inverse)/np.linalg.norm(truth)
    return dict(clean=clean,conditions=conditions,noise_rms=noise_rms,target_bands=np.quantile(errors,QUANTILES,axis=2),
                bands=quantiles(errors.transpose(1,0,2).reshape(27,-1)),clean_median=np.median(clean,axis=0))

def calculate_cell(task):  # Save or resume one independent forward calculation.
    study,index,folder = task; d = load(study); folder = Path(folder)
    path = folder/f'{study}_{index:04d}.npz'
    signature = digest(DATA/'results.npz')+digest(HERE/'physics.py')+digest(HERE/'run.py')
    if path.exists():
        with np.load(path) as saved:
            if str(saved['signature'])!=signature: raise ValueError(f'Stale checkpoint: {path}')
            return {k:saved[k] for k in saved.files if k not in ('signature','seconds')}
    start = time.perf_counter()
    if study=='spectra':
        values = spectrum_field(d['theta'],d['fields'][index],index)
    else:
        if study=='field': theta,field,kind,seed = d['theta'],d['fields'][index],'jkg',20261015
        elif study=='supplement':
            case,k = divmod(index,len(d['fields']))
            theta,field,kind,seed = d['theta'][case],d['fields'][k],'jkg',17
        elif study=='parameters':
            ip,member = divmod(index,len(d['order']))
            theta,field,kind,seed = d['theta'][ip,member],32.,'general',20260915
        else: theta,field,kind,seed = d['theta'][index],32.,'general',20260915
        moments,residuals = centered_moments(theta,field,kind,seed=seed)
        values = dict(moments=moments,residuals=residuals)
    save(path,signature=np.array(signature),seconds=time.perf_counter()-start,**values)
    return values

def calculate(study, workers=4, index=None, folder=RUNS/'work'):  # Regenerate a study, with resumable forward data.
    d = load(study); folder = Path(folder)
    if folder.resolve()==HERE.resolve() or HERE.resolve() in folder.resolve().parents:
        raise ValueError('Choose a work directory outside the source package.')
    folder.mkdir(parents=True,exist_ok=True)
    if study=='coefficients': result = coefficient_summary(d)
    else:
        count = {'field':len(d.get('fields',[])), 'spectra':len(d.get('fields',[])),
                 'supplement':2*len(d.get('fields',[])), 'parameters':640,'known':64}[study]
        if index is not None and not 0<=index<count: raise ValueError(f'Index must lie in [0,{count}).')
        tasks = [(study,i,folder) for i in (range(count) if index is None else [index])]
        with ProcessPoolExecutor(max_workers=workers) as pool: cells = list(pool.map(calculate_cell,tasks))
        if index is not None:
            print(folder/f'{study}_{index:04d}.npz'); return
        if study=='spectra':
            mass = np.array([c['mass'] for c in cells]); omega = cells[0]['omega']
            cumulative = np.cumsum(mass,axis=1)/mass.sum(axis=1)[:,None]
            bounds = [[omega[np.searchsorted(row,q)] for q in (.001,.999)] for row in cumulative]
            visible = (omega>=np.floor(np.min(bounds))-1)&(omega<=np.ceil(np.max(bounds))+1)
            result = dict(fields=d['fields'],centered_omega=omega[visible],intensity=mass[:,visible]/.05,
                full_mass=mass.sum(axis=1),retained_fraction=mass[:,visible].sum(axis=1)/mass.sum(axis=1),
                exact_moments=np.array([c['exact_moments'] for c in cells]))
        else:
            d['moments'] = np.array([c['moments'] for c in cells]).reshape(d['moments'].shape)
            if study=='supplement': result = supplement_summary(d,load('noise')['sigmas'])
            else: result = {'field':field_summary,'parameters':parameter_summary,'known':known_summary}[study](d)
            result['moments'] = d['moments']
    save(folder/f'{study}_results.npz',**result); print(folder/f'{study}_results.npz')

def plotted_rows():  # Export every computed curve point, including off-axis values.
    rows = []
    def add(study,method,x,q):  # Record a curve and its interval.
        q = np.asarray(q)
        if q.ndim==1: q = np.column_stack([q,q,q])
        rows.extend(dict(study=study,method=method,x=float(t),low=l,center=c,high=h) for t,(l,c,h) in zip(x,q))
    d = load('field'); add('field','noiseless',d['fields'],d['clean'])
    for i,s in enumerate(d['sigmas']): add('field',f'sigma={s:g}',d['fields'],d['bands'][i])
    d = load('coefficients')
    for i,name in enumerate(('full','diagonal')): add('coefficients',name,d['sigmas'],np.column_stack([d[k][:,i] for k in ('low','mean','high')]))
    d = load('parameters')
    for i,s in enumerate(d['sigmas']): add('parameters',f'sigma={s:g}',d['counts'],d['bands'][i])
    d,noise = load('supplement'),load('noise')
    for case in range(2):
        add('supplement',f'case{case}_noiseless',d['fields'],d['clean'][case])
        add('supplement',f'case{case}_noisy',d['fields'],d['bands'][case])
        add('noise',f'case{case}',noise['sigmas'],noise['bands'][case])
    d = load('known'); add('known','noisy',np.arange(1,28),d['bands']); add('known','noiseless',np.arange(1,28),d['clean_median'])
    return rows

def plot(output=RUNS/'figures'):  # Main SF panels and supplementary numerical panels.
    import matplotlib.pyplot as plt
    from matplotlib.colors import LinearSegmentedColormap, LogNorm
    from matplotlib.ticker import NullLocator, NullFormatter
    style = json.loads((DATA/'settings.json').read_text())['figure']; plt.rcParams.update(style['rc'])
    output = Path(output); output.mkdir(parents=True,exist_ok=True)
    rows = plotted_rows()
    def curve(ax,x,q,color,label='',ls='-',marker=''):  # Preserve medians and the stated ribbons.
        assert len(np.unique(x))>=6
        if np.ndim(q)==2:
            ax.fill_between(x,q[:,0],q[:,2],color=color,alpha=.13,lw=0); q=q[:,1]
        ax.plot(x,q,color=color,label=label,ls=ls,marker=marker,ms=2.3,lw=1.25)
    def finish(fig,axes,titles,name):  # Label panels and save vector and preview files.
        for i,(ax,title) in enumerate(zip(axes,titles)):
            ax.set_title(title,fontfamily='sans-serif',fontsize=10,pad=10)
            ax.text(-.14,1.05,f'({chr(97+i)})',transform=ax.transAxes,fontfamily='sans-serif',fontsize=11)
            ax.xaxis.set_minor_locator(NullLocator()); ax.yaxis.set_minor_formatter(NullFormatter())
            ax.grid(which='major',color='#E2E5E9',lw=.45)
        fig.tight_layout(w_pad=2)
        for ext in ('pdf','png'): fig.savefig(output/f'{name}.{ext}',dpi=220,bbox_inches='tight',facecolor='white')
        plt.close(fig)
    fig,axes = plt.subplots(1,3,figsize=(10.8,3.2)); d = load('field')
    for i,s in enumerate(d['sigmas']): curve(axes[0],d['fields'],d['bands'][i],style['colors']['sf'][i],rf'$\sigma={s:g}$','--')
    curve(axes[0],d['fields'],d['clean'],'#23252F','noiseless')
    axes[0].set(xscale='log',yscale='log',xlim=(2,100),ylim=(.001,.2),xlabel=r'$B/J_\star$',ylabel='relative error')
    axes[0].set_xticks([2,8,32,100],['2','8','32','100']); axes[0].legend(loc='upper right')
    axes[0].plot([5,20],[.014,.0035],color='#B98200'); axes[0].text(10,.0032,r'$B^{-1}$',color='#B98200',ha='center')
    d=load('coefficients')
    for i,label in enumerate(('full DSF access','diagonal DSF access')):
        color=style['access_colors']['sf'][i]
        axes[1].plot(d['sigmas'],d['member_means'][:12,:,i].T,color=color,alpha=.16,lw=.45)
        curve(axes[1],d['sigmas'],np.column_stack([d[k][:,i] for k in ('low','mean','high')]),color,label,marker='o')
    axes[1].set(xscale='log',yscale='log',xlabel=r'coefficient noise $\sigma$',ylabel='relative error',ylim=(1e-5,.2)); axes[1].legend(loc='upper left')
    d=load('parameters')
    for i,s in enumerate(d['sigmas']): curve(axes[2],d['counts'],d['bands'][i],style['colors']['sf'][i],rf'$\sigma={s:g}$','--','s')
    axes[2].set(yscale='log',xlabel='$p$ = # parameters',ylabel='relative error',ylim=(.006,.04),xticks=[1,6,12,18,27]); axes[2].legend(loc='lower right')
    finish(fig,axes,['Strong-field protocol','SF inversion stability','SF parameter scaling'],'sf_main')
    fig,axes=plt.subplots(2,2,figsize=(8.5,6)); axes=axes.ravel(); d=load('spectra')
    x,w,z=d['fields'],d['centered_omega'],2*d['intensity']  # Display (Sxx+Syy)/(2*pi); stored values average x/y.
    edges=np.r_[x[0]**2/np.sqrt(x[0]*x[1]),np.sqrt(x[:-1]*x[1:]),x[-1]**2/np.sqrt(x[-2]*x[-1])]
    cmap=LinearSegmentedColormap.from_list('dsf',['#292965','#285AA0','#22ACD0','#26D2BC','#9ADD38','#FFF044','#FF9632','#F02A28'])
    mesh=axes[0].pcolormesh(edges,np.r_[w-.025,w[-1]+.025],z.T,cmap=cmap,norm=LogNorm(2e-3,z.max(),clip=True),rasterized=True)
    axes[0].set(xscale='log',xlim=(.125,32),ylim=(-4,8),xlabel='$B$',ylabel=r'$\omega-2B$'); fig.colorbar(mesh,ax=axes[0],label=r'$\langle S^{xx}+S^{yy}\rangle_{\mathbf{q}}/(2\pi)$')
    d=load('supplement'); colors=['#3279B5','#2E7D4F']
    for case,color in enumerate(colors):
        curve(axes[1],d['fields'],d['clean'][case],color,f'case {case+1}')
        curve(axes[1],d['fields'],d['bands'][case],color,ls='--')
    axes[1].set(xscale='log',yscale='log',xlim=(.5,32),ylim=(.001,.2),xlabel='$B$',ylabel='relative error'); axes[1].legend()
    noise=load('noise'); keep=noise['sigmas']>0
    for case,color in enumerate(colors): curve(axes[2],noise['sigmas'][keep],noise['bands'][case,keep],color,f'case {case+1}')
    axes[2].set(xscale='log',yscale='log',xlim=(.001,1),ylim=(.001,.2),xlabel=r'noise std $\sigma$',ylabel='relative error')
    axes[2].text(.04,.9,'$B=32$',transform=axes[2].transAxes)
    for case in range(2): axes[2].axhline(d['clean'][case,np.flatnonzero(d['fields']==32)[0]],color='#B98200',ls='--',lw=1)
    axes[2].plot([.001,1],.18612942*np.array([.001,1]),color='#B98200',ls='--',lw=1)
    d=load('known'); curve(axes[3],np.arange(1,28),d['bands'],'#3279B5','noisy'); curve(axes[3],np.arange(1,28),d['clean_median'],'#23252F','noiseless')
    axes[3].set(xlabel='$p$ = # unknown couplings',ylabel='relative error',ylim=(0,.06),xticks=[1,6,12,18,27]); axes[3].legend()
    finish(fig,axes,['DSF vs field','Two-target recovery','Noise dependence','Known complementary couplings'],'sf_supplement')
    with (output/'plotted.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0])); writer.writeheader(); writer.writerows(rows)
    print(output)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=('plot','calculate'))
    parser.add_argument('--study',choices=STUDIES,default='field')
    parser.add_argument('--workers',type=int,choices=range(1,5),default=4)
    parser.add_argument('--index',type=int)
    parser.add_argument('--work-dir',type=Path,default=RUNS/'work')
    args=parser.parse_args()
    if args.command=='plot': plot()
    else: calculate(args.study,args.workers,args.index,args.work_dir)
