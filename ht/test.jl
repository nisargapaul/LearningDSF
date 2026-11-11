using Test, LinearAlgebra, TOML
# Including the library must ignore its caller's command-line arguments.
const caller_args = copy(ARGS)
append!(ARGS, ["unrelated", "arguments"])
include(joinpath(@__DIR__, "three_body.jl"))
empty!(ARGS)
append!(ARGS, caller_args)
using .HTModel
BLAS.set_num_threads(1)
const SINGLE = Dict('i'=>ComplexF64[1 0;0 1], 'x'=>ComplexF64[0 1;1 0],
    'y'=>ComplexF64[0 -im;im 0], 'z'=>ComplexF64[1 0;0 -1])
function dense_pauli(word, start, nsites)
    labels = fill('i',nsites)
    labels[start+1:start+length(word)] = collect(word)
    reduce(kron,[SINGLE[a] for a in labels])
end

@testset "Numerical setup without root searches" begin
    @test endswith(HTModel.output, joinpath("three_body","status"))
    roots = HTModel.saved_roots()
    @test length(roots) == 2328
    @test all(length(r)==14 && all(isfinite,r) for r in roots)
    system = HTModel.HC.System(HTModel.equations; variables=HTModel.unknown)
    point = Float64.(HTModel.truth[HTModel.unknown_indices])
    @test maximum(abs, HTModel.HC.evaluate(system,point)) < 1e-12
    point .+= 1/128
    complete = copy(HTModel.truth)
    complete[HTModel.unknown_indices] .+= 1//128
    @test HTModel.HC.evaluate(system,point) ≈ Float64.(evaluate_exact.(HTModel.equations,Ref(complete)))
end

@testset "Pauli multiplication" begin
    for a in "ixyz", b in "ixyz"
        key, phase = HTModel.multiply(HTModel.pauli(string(a),0), HTModel.pauli(string(b),0))
        c = only([c for c in "ixyz" if HTModel.pauli(string(c),0) == key])
        @test SINGLE[a]*SINGLE[b] == phase*SINGLE[c]
    end
end

@testset "Generated polynomials and independent matrix traces" begin
    data = features()
    record = TOML.parsefile(joinpath(@__DIR__,"data","three_body.toml"))["certificate"]
    @test length(data.selected) == 19
    @test length(data.full) == 21
    @test length(data.raw) == 135
    @test words == record["parameter_words"]
    @test data.labels == record["full_feature_labels"]
    @test data.raw == pauli_features(nsites=9) == pauli_features(nsites=15)
    lines = readlines(joinpath(@__DIR__,"data","three_body_polynomials.txt"))
    printed = [lines[i+1] for i in eachindex(lines) if occursin(r"^(Full|Selected) feature",lines[i])]
    @test [string.(data.full); string.(data.selected)] == printed
    rational(s) = let (a,b)=split(s,"//"); parse(BigInt,a)//parse(BigInt,b); end
    truth = rational.(record["target"])
    @test evaluate_exact.(data.selected,Ref(truth)) == rational.(record["selected_values"])
    nsites, center = 7, 3
    for sample in 1:3
        values = [(-1)^(j+sample)*(j+2sample)//64 for j in 1:19]
        h = zeros(ComplexF64,2^nsites,2^nsites)
        for (word,coupling) in zip(words,values), r in 0:(nsites-length(word))
            h += Float64(coupling)*dense_pauli(word,r,nsites)
        end
        @test tr(h) == 0
        for a in ["x","y","z"], b in ["x","y","z"], d in -2:2
            oa,ob = dense_pauli(a,center,nsites),dense_pauli(b,center+d,nsites)
            comm = oa*h-h*oa
            direct = [-tr(oa*ob*h), tr(comm*ob), -tr(comm*ob*h)] ./ 2^nsites
            for ((n,i),value) in zip([(0,1),(1,0),(1,1)],direct)
                @test isapprox(value, evaluate_exact(data.raw[(a,b,n,d,i)],values);
                    atol=1e-12,rtol=1e-12)
            end
        end
    end
end
