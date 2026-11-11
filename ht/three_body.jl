# Nineteen-parameter HT tomography from DSF moments.

module HTModel

using LinearAlgebra, Serialization, TOML, DynamicPolynomials, MultivariatePolynomials
import HomotopyContinuation as HC
BLAS.set_num_threads(1)

export words, parameters, pauli_features, selected_features, real_features,
       features, evaluate_exact

const words = split("x xx yy yz zy zz xxx xyy xyz xzy xzz yxy yxz yyx yzx zxy zxz zyx zzx")
@polyvar parameters[1:19]
# A Pauli string uses two bit masks: X=(1,0), Y=(1,1), Z=(0,1).
const Pauli = Tuple{UInt64,UInt64}

function pauli(word, start)
    x, z = UInt64(0), UInt64(0)
    for (j, a) in enumerate(word)
        bit = UInt64(1) << (start + j - 1)
        a in ('x', 'y') && (x |= bit)
        a in ('y', 'z') && (z |= bit)
    end
    (x, z)
end

# Return the product string and its phase in {1, i, -1, -i}.
function multiply(a::Pauli, b::Pauli)
    x, z = xor(a[1], b[1]), xor(a[2], b[2])
    phase = mod(count_ones(a[1] & a[2]) + count_ones(b[1] & b[2]) -
        count_ones(x & z) + 2count_ones(a[2] & b[1]), 4)
    (x, z), (1, im, -1, -im)[phase + 1]
end

function hamiltonian(nsites)
    h = Dict{Pauli,Any}()
    for (word, coupling) in zip(words, parameters), r in 0:(nsites-length(word))
        p = pauli(word, r)
        h[p] = get(h, p, 0) + coupling
    end
    h
end

# [O,H], with exact polynomial coefficients in the nineteen couplings.
function commutator(o, h)
    out = Dict{Pauli,Any}()
    for (p, coupling) in h
        key, a = multiply(o, p)
        _, b = multiply(p, o)
        a == b && continue
        out[key] = get(out, key, 0) + (a - b) * coupling
    end
    out
end

# All coefficients are divided by 2pi; <A>_0 = tr(A)/2^N.
# We use <P Q>_0 = delta(P,Q) for Pauli strings, so no matrices are needed.
# The open interval contains every contributing cluster, without wraparound.
function pauli_features(; nsites=13)
    center = nsites ÷ 2
    @assert 9 <= nsites <= 64
    h = hamiltonian(nsites)
    features = Dict{Tuple{String,String,Int,Int,Int},Any}()
    for a in ["x", "y", "z"], b in ["x", "y", "z"], d in -2:2
        oa, ob = pauli(a, center), pauli(b, center+d)
        ab, phase = multiply(oa, ob)
        # -<O_a O_b H>_0
        features[(a,b,0,d,1)] = -phase * get(h, ab, 0)
        comm = commutator(oa, h)
        # <[O_a,H] O_b>_0
        features[(a,b,1,d,0)] = get(comm, ob, 0)
        # -<[O_a,H] O_b H>_0
        slope = zero(parameters[1])
        for (p, coefficient) in comm
            key, sign = multiply(p, ob)
            slope -= coefficient * sign * get(h, key, 0)
        end
        features[(a,b,1,d,1)] = slope
    end
    features
end

# The manuscript's nineteen equations, in its stated order.
function selected_features(f)
    p(a,b,d) = f[(a,b,1,d,1)]
    r(a,b,d) = real(p(a,b,d))
    [
        (-real(f[(a,b,0,1,1)]) for (a,b) in
            (("x","x"),("y","y"),("z","y"),("y","z"),("z","z")))...,
        r("x","x",2), r("x","x",1), r("x","x",0),
        r("y","y",2), r("y","y",1), r("y","y",0),
        r("z","y",2), r("z","y",1),
        r("y","z",0) + imag(p("y","z",0)),
        r("y","z",1), r("y","z",2),
        r("z","z",2), r("z","z",1), r("z","z",0),
    ]
end

# Remove zero components and proportional copies, retaining their provenance.
function polynomial_signature(p)
    iszero(p) && return "zero"
    cs, ms = coefficients(p), monomials(p)
    join([string(m, ":", c // first(cs)) for (c,m) in zip(cs,ms)], ";")
end

function real_features(f)
    rows = [(poly, string(key, ":", part)) for key in sort(collect(keys(f)))
        for (part, poly) in (("real",real(f[key])), ("imag",imag(f[key]))) if !iszero(poly)]
    rows = unique(row -> polynomial_signature(first(row)), rows)
    first.(rows), last.(rows)
end

evaluate_exact(p, values) = sum(coefficients(subs(p, parameters => values)))
evaluate_exact(p::Number, values) = p

# Generate both maps from the operator algebra above.
function features()
    raw = pauli_features()
    full, labels = real_features(raw)
    (; selected=selected_features(raw), full, labels, raw)
end

# Numerical roots at the saved rational target.
const ROOT = @__DIR__
const DATA = joinpath(ROOT, "data")
const record = TOML.parsefile(joinpath(DATA, "three_body.toml"))["certificate"]
const truth = [parse(BigInt,a)//parse(BigInt,b) for (a,b) in split.(record["target"], "//")]
const data = features()
jacobian(f=data.selected, point=truth) =
    [evaluate_exact(differentiate(p,x), point) for p in f, x in parameters]
# The first five equations give the two-spin couplings directly.
const unknown_indices = [1; 7:19]
const unknown = parameters[unknown_indices]
const equations = [subs(p, parameters[2:6]=>truth[2:6])-evaluate_exact(p,truth) for p in data.selected[6:19]]
output = joinpath(ROOT, "..", "runs", "ht", "three_body", "status")
function save(name, value)
    mkpath(output)
    open(io -> TOML.print(io, value; sorted=true), joinpath(output,name), "w")
end
function saved_roots()
    lines = readlines(joinpath(DATA,"three_body_roots.csv"))
    @assert split(first(lines), ',') == [string(w,"_",p) for w in words[unknown_indices] for p in ("re","im")]
    [complex.(v[1:2:end],v[2:2:end]) for v in [parse.(Float64,split(line,',')) for line in lines[2:end]]]
end

function search()
    result = HC.solve(HC.System(equations; variables=unknown); start_system=:polyhedral,
        only_torus=false, seed=UInt32(20261008), threading=false, show_progress=false)
    mkpath(output)
    serialize(joinpath(output,"search.jls"), result)
    save("search.toml", Dict("tracked_paths"=>HC.ntracked(result), "failed_paths"=>HC.nfailed(result),
        "paths_at_infinity"=>HC.nat_infinity(result), "nonsingular_roots"=>HC.nnonsingular(result)))
    result
end

function degree_diagnostics()
    f = [subs(p,parameters[2:6]=>truth[2:6]) for p in data.selected[6:19]]
    @polyvar c[1:14]
    system = HC.System([f[i]-c[i] for i in 1:14]; variables=unknown, parameters=c)
    target = ComplexF64[evaluate_exact(p,truth) for p in data.selected[6:19]]
    result = HC.monodromy_solve(system,saved_roots(),target; seed=UInt32(20261105),
        max_loops_no_progress=3, timeout=600., threading=false, show_progress=false,
        tracker_options=(max_steps=30000,))
    complete = HC.verify_solution_completeness(system,HC.solutions(result),target;
        trace_tol=1e-8, show_progress=false, parameter_homotopy_options=(threading=false,),
        monodromy_options=(threading=false,timeout=240.,max_loops_no_progress=3,seed=UInt32(20261106)))
    save("degree.toml",Dict("determination"=>"numerical", "selected_generic_degree"=>HC.nsolutions(result),
        "trace_test_passed"=>complete))
end

function main(command)
    global output = joinpath(ROOT, "..", "runs", "ht", "three_body", command)
    command == "status" && return println("Selected nineteen equations: g = 2328 (numerical).")
    command == "degree" && return degree_diagnostics()
    command == "search" && return search()
    command == "check" || error("Usage: three_body.jl [status|check|search|degree]")
    run(`$(Base.julia_cmd()) --startup-file=no --threads=1 --project=$ROOT $(joinpath(ROOT,"test.jl"))`)
end
end # module HTModel

abspath(PROGRAM_FILE) == abspath(@__FILE__) && HTModel.main(isempty(ARGS) ? "status" : only(ARGS))
