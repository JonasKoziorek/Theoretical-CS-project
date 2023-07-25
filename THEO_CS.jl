### A Pluto.jl notebook ###
# v0.19.27

using Markdown
using InteractiveUtils

# This Pluto notebook uses @bind for interactivity. When running this notebook outside of Pluto, the following 'mock version' of @bind gives bound variables a default value (instead of an error).
macro bind(def, element)
    quote
        local iv = try Base.loaded_modules[Base.PkgId(Base.UUID("6e696c72-6542-2067-7265-42206c756150"), "AbstractPlutoDingetjes")].Bonds.initial_value catch; b -> missing; end
        local el = $(esc(element))
        global $(esc(def)) = Core.applicable(Base.get, el) ? Base.get(el) : iv(el)
        el
    end
end

# ╔═╡ 1c0b6789-7dcb-4005-8adc-e1a4a275629d
using Random, PlutoUI, DataStructures, Graphs, GraphMakie, CairoMakie, GraphRecipes, Plots, LayeredLayouts, Makie.GeometryBasics

# ╔═╡ 5e232da0-3d47-4e2c-9499-ea8e09f337fb
md"""
# TO-DO LIST
* DFA → REGEX
* acceptance for all
* chomsky normal form
* visualization of deriv trees
* CYK algorithms
* push down automata
* simplifying CFGs
* CFG not ambiguous + parser?
"""

# ╔═╡ 295638ba-a435-42db-aa5a-838a47d594ab
md"""
# Introduction
We will be implementing algorithms from the first 6 chapters from the _Introduction to Automata Theory, Languages and Computation by John E. Hopcroft and Jeffrey D. Ullman_. The aim of this work is to show that modern programming languages can get very close to mathematics that mathematicians see in the books. Nowdays it is becoming easy for scientists to easily convert mathematics into code with almost the same syntax.
"""

# ╔═╡ e7d3ed3d-6eeb-4783-a0d4-864dd258588a
md"""
Let's start with declaring the abstract type of Finite Automata which will be the base for all the special types.
"""

# ╔═╡ 52e6d1e7-064a-4cea-940d-31626ba11444
abstract type FA end # FA = finite automata

# ╔═╡ 481ffec9-8a37-4d49-b18b-a73f1a9f20ce
md"""
We shall also intoduce aliases that better fit the vocabulary in the book.
"""

# ╔═╡ b00a1e34-dc4d-47e7-a364-ea68f9a3e8ca
begin
	Word = String
	Symbol = Char 
	State = String # for states such as q1
	const 𝜖 = ""
	Language = Set{Word}
end

# ╔═╡ 42bbc7bb-2619-4e2f-8feb-b6db95725a1f
md"""
# Deterministic Finite Automata (DFA)

## Formal Definition
Formally represented by 5-tuple (Q, Σ, δ, q0, F) where:

* Q = set of possible states
* Σ = finite input alphabet
* δ: Q × Σ → Q is a transition function
* q0 ∈ Q is an initial state
* F ⊆ Q is a set of final states 

We will represent this structure in code as follows:
"""


# ╔═╡ d9e6f3d2-b56d-4587-8324-385d11d732fe
struct DFA <: FA # DFA = deterministic finite automata
	Q :: Set{State}
	Σ :: Set{Symbol}
	δ :: Dict{Tuple{State,Symbol}, State}
	q0 :: State
	F :: Set{State}
end

# ╔═╡ 5f52b01e-243a-475a-9583-afc7bc31bd60
md"""
## String Acceptance

Let's construct the transition function δ for a DFA that accepts a current state and a symbol and moves the automata to the next state.
"""

# ╔═╡ 37decd55-6f2b-4344-a20c-a893227c0f13
function δ(automata::DFA, state::State, symbol::Symbol)
	return automata.δ[(state, symbol)]
end

# ╔═╡ 4bc35f6c-c01b-46be-834b-e00c050cfb2a
md"""
We can simply extend the transition function δ such that it accepts words.
"""

# ╔═╡ 554b1c89-d99b-4da3-a2b0-485e7f907b9f
function δ(automata::DFA, state::State, word::Word)
	if length(word) > 1
		prefix = word[1:end-1]
		suffix = last(word)
		return δ(automata, δ(automata, state, prefix) , suffix)
	else
		return δ(automata, state, first(word))
	end
end

# ╔═╡ 3c3da943-5661-4fa3-a3f0-dbd90ed63a1f
md"""
DFA _accepts_ a word if and only if the δ($q_0$, w) $\in$ F for $w \in Σ^*$. We can check whether a word is accepted algorithmically this way:
"""

# ╔═╡ 81de4891-4cc5-4711-91c3-5fbd7253ee18
function accepts(automata::DFA, word::String)
	state = automata.q0
	result = δ(automata, state, word)
	if result in automata.F
		return true
	else
		return false
	end
end

# ╔═╡ 0fe503e3-1209-439b-98ab-8aa3ec9e8ec3
md"""
## Visualization
"""

# ╔═╡ 4e0dc9a3-6e73-4c6b-9337-29fd0504f4a0
function transition_diagram(dfa::DFA)
	states = collect(dfa.Q)
	size = length(states)
	sorted = sort(states)
	indexof(a) = findfirst(x->x==a, sorted)
	edges = []
	elabels = []
	g = SimpleDiGraph(size)
	
	for key in keys(dfa.δ)
		# δ(q, a) = p
		q = indexof(key[1])
		a = key[2]
		p = indexof(dfa.δ[key])
		if (q,p) ∉ edges
			push!(edges, (q,p))
			push!(elabels, string(a))
		else
			index = findfirst(x->x==(q,p), edges)
			elabels[index] = elabels[index] * ", " * a
		end
	end
	[add_edge!(g, edge...) for edge in edges]

	perm = sortperm(edges)
	elabels = elabels[perm]

	nodecolor = [:white for i=1:nv(g)]
	nodecolor[indexof(dfa.q0)] = :green
	for fstate in dfa.F
		nodecolor[indexof(fstate)] = :red
	end
	
	f, ax, p = GraphMakie.graphplot(g,
		arrow_shift=:end, 
		arrow_size=20,
		ilabels=sorted,
		elabels=elabels,
		node_color=nodecolor
	)
	hidedecorations!(ax); hidespines!(ax); ax.aspect = DataAspect()
	return f
end

# ╔═╡ 9981bbc9-8853-42db-95af-2b6b4573e563
md"""
## Example Definition

### Example from fig 2.2 on page 16

"""

# ╔═╡ c8542af2-5580-4216-acf1-b411352b30e4
begin
	dfa1 = DFA(
		Set(["q0", "q1", "q2", "q3"]),
		Set(['0', '1']),
		Dict(
			("q0", '1') => "q1",
			("q1", '1') => "q0",
			("q0", '0') => "q2",
			("q2", '0') => "q0",
			("q1", '0') => "q3",
			("q3", '0') => "q1",
			("q2", '1') => "q3",
			("q3", '1') => "q2",
		),
		"q0",
		Set(["q0"])
	)
end

# ╔═╡ 335a3b2f-b203-47d9-9424-eb3d7e721034
md"""
### Other example
"""

# ╔═╡ 7239c4f3-554a-40aa-b8f3-a61089ab0343
begin
	Q1 = Set(["1", "2", "3", "4", "5"])
	Σ1 = Set(['a', 'b', 'c', 'd'])
	δ1 = Dict(
		("1", 'a') => "2",
		("5", 'b') => "3",
		("4", 'd') => "1",
		("3", 'c') => "4",
		("2", 'b') => "5",		
	)
	q01 = "1"
	F1 = Set(["2"])
	dfa2 = DFA(Q1, Σ1, δ1, q01, F1)
end

# ╔═╡ a020300f-054f-40f2-bbc0-f2519bcb5aac
md"""
# Nondeterminictic Finite Automata (NFA)

## Formal Definition
Formally represented by 5-tuple (Q, Σ, δ, q0, F) where:

* Q = set of possible states
* Σ = finite input alphabet
* δ: Q × Σ → $2^Q$ is a transition function
* q0 ∈ Q is an initial state
* F ⊆ Q is a set of final states 

We will represent this structure in code as follows:
"""

# ╔═╡ 76c842d6-18ab-47c6-8c3d-9b0ac302c755
struct NFA <: FA # DFA = deterministic finite automata
	Q :: Set{State}
	Σ :: Set{Symbol}
	δ :: Dict{Tuple{State,Symbol}, Set{State}}
	q0 :: State
	F :: Set{State}
end

# ╔═╡ 5f3aa8cb-f05b-4e99-a3c2-17b935fdba32
md"""
## Visualisation
"""

# ╔═╡ 109f33e8-bc1c-4b07-b17a-e3e71224195f
function transition_diagram(dfa::NFA)
	states = collect(dfa.Q)
	size = length(states)
	sorted = sort(states)
	indexof(a) = findfirst(x->x==a, sorted)
	edges = []
	elabels = []
	g = SimpleDiGraph(size)
	
	for key in keys(dfa.δ)
		# δ(q, a) = p
		q = indexof(key[1])
		a = key[2]
		possible_states = dfa.δ[key]
		for p in possible_states
			p = indexof(p)
			if (q,p) ∉ edges
				push!(edges, (q,p))
				push!(elabels, string(a))
			else
				index = findfirst(x->x==(q,p), edges)
				elabels[index] = elabels[index] * ", " * a
			end
		end
	end
	[add_edge!(g, edge...) for edge in edges]

	perm = sortperm(edges)
	elabels = elabels[perm]

	nodecolor = [:white for i=1:nv(g)]
	nodecolor[indexof(dfa.q0)] = :green
	for fstate in dfa.F
		nodecolor[indexof(fstate)] = :red
	end
	
	f, ax, p = GraphMakie.graphplot(g,
		arrow_shift=:end, 
		arrow_size=20,
		ilabels=sorted,
		elabels=elabels,
		node_color=nodecolor
	)
	hidedecorations!(ax); hidespines!(ax); ax.aspect = DataAspect()
	return f
end

# ╔═╡ 46b9e722-b97c-41a9-b8ed-3d9342bbbafe
md"""
## NFA → DFA conversion
"""

# ╔═╡ 8c4234ce-c204-4931-a355-bc73e91c6823
md"""
# Nondeterminictic Finite Automata with 𝜖-moves (𝜖-NFA)

## Formal Definition
Formally represented by 5-tuple (Q, Σ, δ, q0, F) where:

* Q = set of possible states
* Σ = finite input alphabet
* δ: Q × (Σ ∪ {𝜖}) → $2^Q$ is a transition function
* q0 ∈ Q is an initial state
* F ⊆ Q is a set of final states 

We will represent this structure in code as follows:
"""
# 𝜖 is \itepsilon

# ╔═╡ a7a06841-d2b3-4265-8549-44b3a08e5302
struct 𝜖NFA <: FA
	Q :: Set{State}
	Σ :: Set{Symbol}
	δ :: Dict{
			Union{Tuple{State,Symbol}, Tuple{State, Word}}, # either char as Symbol or empty string as Word
			Set{State}
	}
	q0 :: State
	F :: Set{State}
end
# 𝜖 is \itepsilon

# ╔═╡ d469fdc5-7eb2-494c-bfb7-a9ee3087106b
md"""
## Visualisation
"""

# ╔═╡ 439f0d7f-69f5-4252-826d-f143a2196564
function transition_diagram(dfa::𝜖NFA)
	states = collect(dfa.Q)
	size = length(states)
	sorted = sort(states)
	indexof(a) = findfirst(x->x==a, sorted)
	edges = []
	elabels = []
	g = SimpleDiGraph(size)
	
	for key in keys(dfa.δ)
		# δ(q, a) = p
		q = indexof(key[1])
		a = key[2]
		if a == ""
			a = "𝜖"
		end
		possible_states = dfa.δ[key]
		for p in possible_states
			p = indexof(p)
			if (q,p) ∉ edges
				push!(edges, (q,p))
				push!(elabels, string(a))
			else
				index = findfirst(x->x==(q,p), edges)
				elabels[index] = elabels[index] * ", " * a
			end
		end
	end
	[add_edge!(g, edge...) for edge in edges]

	perm = sortperm(edges)
	elabels = elabels[perm]

	nodecolor = [:white for i=1:nv(g)]
	nodecolor[indexof(dfa.q0)] = :green
	for fstate in dfa.F
		nodecolor[indexof(fstate)] = :red
	end
	
	f, ax, p = GraphMakie.graphplot(g,
		arrow_shift=:end, 
		arrow_size=20,
		ilabels=sorted,
		elabels=elabels,
		node_color=nodecolor
	)
	hidedecorations!(ax); hidespines!(ax); ax.aspect = DataAspect()
	return f
end

# ╔═╡ 7782fffd-0699-410d-bf59-0fdc2046a1cf
md"""
## 𝜖NFA → NFA conversion
"""

# ╔═╡ ca1a1e92-e576-4938-a914-08abb1ed8ebe
begin
	function 𝜖Closure(enfa::𝜖NFA, state::State)
		key = filter(key -> key[1] == state && key[2]==𝜖, keys(enfa.δ))
		if length(collect(key)) == 1
			𝜖transitions = enfa.δ[first(key)]
			return 𝜖transitions
		else
			return Set([])
		end
	end
	
	function 𝜖CLOSURE(enfa::𝜖NFA, state::State)
		closure = Set([state])
		len = 1
		prev_len = -1
		while len != prev_len
			prev_len = len
			for i in collect(closure)
				closure = union(closure, 𝜖Closure(enfa, i))
			end
			len = length(collect(closure))
		end
		return closure
	end

	function 𝜖CLOSURE(enfa::𝜖NFA, states::Set{State})
		return union([𝜖CLOSURE(enfa, state) for state in collect(states)]...)
	end

	function convert(::Type{NFA}, enfa::𝜖NFA)
		Q = enfa.Q
		Σ = enfa.Σ
		δ = Dict()
		for q in collect(Q)
			for a in collect(Σ)
				first_closure = [enfa.δ[(r, a)] for r in collect(𝜖CLOSURE(enfa, q)) if (r,a) in keys(enfa.δ)]
				
				if length(first_closure) != 0
					δ[(q,a)] = 𝜖CLOSURE(enfa, union(first_closure...))		
				end
			end
		end
		q0 = enfa.q0
		
		intersection = intersect(enfa.Q, 𝜖CLOSURE(enfa, enfa.q0))
		if length(intersection) != 0
			F = union(enfa.F, Set([enfa.q0]))
		else
			F = enfa.F
		end
		return NFA(Q, Σ, δ, q0, F)
	end
	
end

# ╔═╡ 083ec2ad-4409-4522-97b9-5c34bda0c7a6
md"""
## Example definition
"""

# ╔═╡ 30e842dc-5531-45c2-b19d-87cc809d9daf
begin
	Q2 = Set(["a", "b", "c"])
	Σ2 = Set(['0', '1', '2'])
	δ2 = Dict(
		("a", 𝜖) => Set(["a", "b"]),
		("c", '1') => Set(["c", "a"]),
		("b", '0') => Set(["a", "c"])	
	)
	q02 = "b"
	F2 = Set(["b", "c"])
	enfa = 𝜖NFA(Q2, Σ2, δ2, q02, F2)
end

# ╔═╡ 8604a238-25d4-466f-ba58-dbdd2fe657c5
md"""
# Regular Expressions (REGEX)

## Abstract Syntax Tree Representation and Parser
"""

# ╔═╡ 3699204b-7ae6-4af5-afa8-f7501e5d8451
module REGEX

abstract type RegExpr end
Word = String
Language = Set{Word}

struct Epsilon <: RegExpr
	lang :: Language

	Epsilon() = new(Set([""]))
end

struct KleeneClosure <: RegExpr
	lang :: RegExpr
end

struct Concatenation <: RegExpr
	lang1 :: RegExpr
	lang2 :: RegExpr
end

struct Union <: RegExpr
	lang1 :: RegExpr
	lang2 :: RegExpr
end

struct Symbol <: RegExpr
	symbol :: Word

	Symbol(a::Char) = new(string(a))
	Symbol(a::String) = new(a)
end

parse(expr :: String) = expression(remove_space(expr))[2]
move(word::String) = last(word,length(word)-1)
remove_space(a) = filter(x -> !isspace(x), a)


function expression(word::Word)
	word, lang = product(word)
	while length(word) > 0 && first(word) == '+'
		word = move(word)
		word, lang2 = product(word)
		lang = REGEX.Union(lang, lang2)
	end
	return word, lang
end

function product(word::Word)
	word, lang = term(word)
	while length(word) > 0 && first(word) == '⋅'
		word = move(word)
		word, lang2 = term(word)
		lang = REGEX.Concatenation(lang, lang2)
	end
	return word, lang
end

function term(word::Word)
	lang = Epsilon()
	if length(word) > 0
		fst = first(word)
		if isdigit(fst) || islowercase(fst) || isuppercase(fst)
			if fst == '𝜖'
				lang = REGEX.Epsilon()
			else
				lang = REGEX.Symbol(string(fst))
			end
			word = move(word)
		elseif first(word) == '('
			word = move(word)
			word, lang = expression(word)
			if first(word) == ')'
				word = move(word)
			else
				error("Parse error.")
			end
		end
	end
	while length(word) > 0 && first(word) == '*'
		word = move(word)
		lang = REGEX.KleeneClosure(lang)
	end
	return word, lang
end

end

# ╔═╡ 1e30ab88-74e4-46cc-929b-5b9ba37104cf
remove_space(a) = REGEX.remove_space(a)

# ╔═╡ 30bc37f0-7bd8-4b23-a747-3ff348377a33
md"""
## Parsing Example
"""

# ╔═╡ 0d0459f6-f921-4d4d-ac7c-fb121b9b4058
begin
a = "a⋅A⋅(0+A)*+𝜖"
c = REGEX.parse(a)
end

# ╔═╡ 9aa9375b-0047-44ff-b8c7-7f686429b9a1
begin

# 𝜖NFA
rename_key(key, subs) = (subs[key[1]], key[2])
rename_keys(keys, subs) = [rename_key(key, subs) for key in keys]
rename_val(val, subs) = Set([subs[state] for state in val])
rename_vals(vals, subs) = [rename_val(val, subs) for val in collect(vals)]

function rename_transitions(transitions, subs)
	Dict(rename_keys(
		keys(transitions), subs) .=> rename_vals(values(transitions), subs)
	)
end

function rename(fa::FA, char::String, start::Int)
	states = sort(collect(fa.Q))
	len = length(states)
	nvect = ["$(char)$(i+start)" for i = 1:len]
	subs = Dict(zip(states, nvect))
	Q = Set([subs[state] for state in collect(fa.Q)])
	Σ = fa.Σ
	δ = rename_transitions(fa.δ, subs)
	q0 = subs[fa.q0]
	F = Set([subs[state] for state in collect(fa.F)])
	type_ = typeof(fa)
	return type_(Q, Σ, δ, q0, F)
end

rename(fa::FA, char::String) = rename(fa, char, 0)
	
end

# ╔═╡ e78147a2-25b1-4a99-93d8-e911a750767b
begin
	parse_state_name(state::State) = split(remove_space(state)[2:end-1], ',')
	function code_state_name(states::Set{State})
		states = sort(collect(states))
		new_state = "[" * join([state * ", " for state in states])
		new_state = new_state[1:end-2] * "]"
		return new_state
		
	end

	function conv_δ(nfa::NFA, state::State, symbol::Symbol)
		states = parse_state_name(state)
		new_states = [nfa.δ[(state, symbol)] for state in states if (state, symbol) in keys(nfa.δ)]
		if length(new_states) == 0
			return ""
		else
			new_states = union(new_states...)
			return code_state_name(new_states)
		end
	end

	function check_final_state(nfa::NFA, state::State)
		for f in collect(nfa.F)
			if f ∈ parse_state_name(state)
				return true
			end
		end
		return false
	end
	
	function make_deterministic(nfa::NFA, q0::State)
		Q = Set([])
		F = Set([])
		δ = Dict()
		stack = Stack{State}()
		push!(stack, q0)
		
		while length(stack) != 0
			state = pop!(stack)
			if state ∉ Q
				push!(Q, state)
				if check_final_state(nfa, state)
					push!(F, state)
				end
				for a in nfa.Σ
					new_state = conv_δ(nfa, state, a)
					if new_state != ""
						push!(stack, new_state)
						δ[(state, a)] = new_state
					end
				end
			end
		end
		return Q, δ, F
	end
	
	function convert(::Type{DFA}, nfa::NFA)
		nfa = rename(nfa, "q", -1)
		Σ = nfa.Σ
		q0 = "[q0]"
		Q, δ, F = make_deterministic(nfa, q0)
		return DFA(Q, Σ, δ, q0, F)
	end
end

# ╔═╡ 64342e14-0fa3-4967-92d5-ea093e5a2000
md"""
## Conversions

### REGEX → 𝜖NFA conversion
"""

# ╔═╡ d0282bb1-0527-4de8-9a26-6c61d7075b56
begin
	
function convert(::Type{𝜖NFA}, expr::REGEX.Epsilon)
	Q = Set(["q0"])
	Σ = Set([])
	δ = Dict()
	q0 = "q0"
	F = Q
	return 𝜖NFA(Q, Σ, δ, q0, F)
end

function convert(::Type{𝜖NFA}, expr::REGEX.Symbol)
	a = expr.symbol[1]
	Q = Set(["q0", "qf"])
	Σ = Set([a])
	δ = Dict(("q0", a) => Set(["qf"]))
	q0 = "q0"
	F = Set(["qf"])
	return 𝜖NFA(Q, Σ, δ, q0, F)
end

function convert(::Type{𝜖NFA}, expr::REGEX.Concatenation)
	a = convert(𝜖NFA, expr.lang1)
	b = convert(𝜖NFA, expr.lang2)
	len_a = length(a.Q)
	len_b = length(b.Q)

	a = rename(a, "q")
	b = rename(b, "q", len_a)

	Q = union(a.Q, b.Q)
	Σ = union(a.Σ, b.Σ)
	δ = merge(a.δ, b.δ, Dict((first(collect(a.F)) , 𝜖) => Set([b.q0])))
	q0 = a.q0
	F = b.F
	return 𝜖NFA(Q, Σ, δ, q0, F)
end

function convert(::Type{𝜖NFA}, expr::REGEX.Union)
	a = convert(𝜖NFA, expr.lang1)
	b = convert(𝜖NFA, expr.lang2)
	len_a = length(a.Q)
	len_b = length(b.Q)

	a = rename(a, "q")
	b = rename(b, "q", len_a)
	last_state = len_a+len_b+1
	
	Q = union(a.Q, b.Q, Set(["q0", "q$(last_state)"]))
	Σ = union(a.Σ, b.Σ)
	δ = merge(a.δ, b.δ, 
		Dict(
			("q0" , 𝜖) => Set([a.q0, b.q0]),
			(first(collect(a.F)) , 𝜖) => Set(["q$(last_state)"]),
			(first(collect(b.F)) , 𝜖) => Set(["q$(last_state)"]),
		)
	)
	q0 = "q0"
	F = Set(["q$(last_state)"])
	return 𝜖NFA(Q, Σ, δ, q0, F)
end

function convert(::Type{𝜖NFA}, expr::REGEX.KleeneClosure)
	a = convert(𝜖NFA, expr.lang)
	len_a = length(a.Q)

	a = rename(a, "q")

	Q = union(a.Q, Set(["q0", "q$(len_a+1)"]))
	Σ = a.Σ
	δ = merge(a.δ, 
		Dict(
			("q0" , 𝜖) => Set([a.q0, "q$(len_a+1)"]),
			(first(collect(a.F)) , 𝜖) => Set([a.q0, "q$(len_a+1)"]),
		)
	)
	q0 = "q0"
	F = Set(["q$(len_a+1)"])
	return 𝜖NFA(Q, Σ, δ, q0, F)
end	
	
end

# ╔═╡ 2b97b515-2aba-40a6-a16b-27c2d0411d86
md"""
### REGEX → NFA conversion
"""

# ╔═╡ 6a6c3e7c-c61e-429a-a00a-b8c121ff313e
convert(::Type{NFA}, expr::REGEX.RegExpr) = convert(NFA, convert(𝜖NFA, expr))

# ╔═╡ fad612c2-c63e-4114-9b77-28c0e8858848
md"""
### REGEX → DFA conversion
"""

# ╔═╡ 566bb40d-1527-4796-9d49-cd7ce7aa8c93
convert(::Type{DFA}, expr::REGEX.RegExpr) = convert(DFA, convert(NFA, expr))

# ╔═╡ dcaf893d-51fa-4a58-8eff-7b2e8e952d0b
md"""
## Conversion Examples
"""

# ╔═╡ bd549b0d-0266-404d-9f4b-592120957aa5
md"""
### REGEX → 𝜖NFA
"""

# ╔═╡ 6c67f721-9d8b-42df-aecc-93ab5307e2d7
q1 = convert(𝜖NFA, REGEX.parse("(A+B+C)*"))

# ╔═╡ ec032c49-0f42-4367-b4ea-04c147b86374
md"""
### REGEX → NFA
"""

# ╔═╡ e5423ff9-a1d1-4b6d-ade4-e5926f56d2b0
q2 = convert(NFA, REGEX.parse("A+B"))

# ╔═╡ 746aacbb-1462-455a-9b6e-686469685674
md"""
### REGEX → DFA
"""

# ╔═╡ f451b75f-220f-4ccf-b67a-d336bcb09a7e
q3 = convert(DFA, REGEX.parse("(A+B)*"))

# ╔═╡ df4186f1-a2d5-4fde-8561-cb45c7da44d7
# function Base.show(io::IO, expr::Language)
# 	expr = sort(collect(expr))
# 	res = "{"
# 	for elem in 1:length(expr)-1
# 		res *= expr[elem] * ", "
# 	end
# 	res *= last(expr) * "}"
# 	print(res)
# end

# ╔═╡ 69960128-6005-46f2-a472-b00ab0d6abe7
# function Base.show(io::IO, expr::KleeneClosure)
# 	if isa(expr.lang, Language)
# 		print(collect(expr.lang))
# 	else
# 		print("{$(expr.lang)}*")
# 	end
# end

# ╔═╡ 0df007a2-7553-43a6-991f-815704a29985
# function Base.show(io::IO, expr::Epsilon)
# 	print(collect(expr.lang))
# end

# ╔═╡ 08d2ba43-fd3c-481e-b18b-f100bccd033e
# function Base.show(io::IO, expr::Concatenation)
# 	print("$(string(expr.lang1))$(string(expr.lang2))")
# end

# ╔═╡ 1788b455-4444-4a7e-b830-a439dc9fba6a
# function Base.show(io::IO, expr::LangUnion)
# 	print("$(string(expr.lang1))+$(string(expr.lang2))")
# end

# ╔═╡ d460c908-d7eb-49b4-8924-44bab234cd43
md"""
# Conversion examples from textbook
"""

# ╔═╡ 5c46bd5b-ce78-430e-8ced-7e579fd6c831
md"""
## NFA → DFA conversion example Example 2.5 page 23
"""

# ╔═╡ 7d7c03f0-bc9e-4272-8b36-730aea4f1f4d
nfa2 = NFA(
	Set(["q0", "q1"]),
	Set(['0', '1']),
	Dict(
		("q0", '0') => Set(["q0", "q1"]),
		("q0", '1') => Set(["q1"]),
		("q1", '1') => Set(["q0", "q1"])
	),
	"q0",
	Set(["q1"])
)

# ╔═╡ 1547e812-f21b-4078-80f7-2bd51aa55f36
dfa3 = convert(DFA, nfa2)

# ╔═╡ fa58d471-5e56-4e9e-9c44-d0d22ac4e188
md"""
## 𝜖NFA → NFA conversion Example 2.9 page 27
"""

# ╔═╡ bcf35e8f-a58e-45fb-9fe8-45e06ab76962
enfa3 = 𝜖NFA(
	Set(["q0", "q1", "q2"]),
	Set(['0', '1', '2']),
	Dict(
		("q0", '0') => Set(["q0"]),
		("q0", 𝜖) => Set(["q1"]),
		("q1", '1') => Set(["q1"]),
		("q1", 𝜖) => Set(["q2"]),
		("q2", '2') => Set(["q2"]),		
	),
	"q0",
	Set(["q2"])
)

# ╔═╡ 97e74c33-ce44-4582-bf78-b148ef938f2d
nfa1 = convert(NFA, enfa3)

# ╔═╡ d5e8a30e-7c02-4488-9b76-c433bfc47af3
md"""
Feed automata with symbol: $(@bind answer TextField())
"""

# ╔═╡ ab37b446-9ae2-43f2-8ad2-23c955bef5e2
graph

# ╔═╡ 22c87b83-e604-47cf-9cc5-c62bb596dad0
δ(automata, 1, "c")

# ╔═╡ ac26115c-994c-4d26-8cd3-1d0173ff0963
md"""
# Context Free Grammars (CFG)
Formally represented by 4-tuple (V, T, P, S) where:

* V = finite set of variables
* T = finite set of terminals
* P = finite set of productions
* S = a special variable called start symbol

V and T are disjoint sets.
Production p ∈ P is of the form A → α where A ∈ V, α ∈ $(V ∪ T)^*$.
"""

# ╔═╡ d60401e4-68c1-46eb-a058-198bc07cc038
md"""
Let's define some aliases for our new object:
"""

# ╔═╡ 2595d95d-e078-4797-89f0-a5fea224958d
begin
	Productions = Dict{Word, Vector{Vector{Word}}}
end;

# ╔═╡ a671e43e-b047-40be-aa86-033cb2d9f189
md"""
We will represent CFG in code as follows:
"""

# ╔═╡ acecd610-61b1-4a9d-b25c-7621cf1118aa
struct CFG
	V :: Set{Word}
	T :: Set{Word}
	P :: Productions
	S :: Word
end

# ╔═╡ d3d284f6-bd4c-409a-b7df-6273cc80205d
md"""
Here is a construction of a CFG in example 4.4 on page 83:
"""

# ╔═╡ 521ce74b-50b7-486b-9ffe-c5af10eeacea
begin
	variables = Set(["S", "A"])
	terminals = Set(["a", "b"])
	productions = Dict([
		"S" => [["a", "A", "S"], ["a"]],
		"A" => [["S","b","A"], ["S", "S"], ["b","a"]]
	])
	start_symbol = "S"
	G = CFG(variables, terminals, productions, start_symbol)
end

# ╔═╡ a3f1a607-2a83-4fcf-b82d-d5ed77a278ba
function deriv(cfg::CFG, word::Word, prod::Tuple{Word, Int64})
	var = prod[1]
	index = findfirst(var, word)[1]
	return word[1:index-1] * join(cfg.P[var][prod[2]]) * word[index+1:end]
end

# ╔═╡ a9838ecf-a01a-43ea-a954-c17449d8217e
word = "Saa"

# ╔═╡ a030d112-051c-483d-8363-82447c965e28
deriv(G, word, ("S", 1))

# ╔═╡ 4a6b124f-ab81-4703-b281-87e76a224406
md"""
# Derivation Tree
"""

# ╔═╡ 1b0808e4-5183-419d-a0d2-cc47bf6f91d2
struct DerivTree
	name :: Word
	children :: Vector{DerivTree}
end

# ╔═╡ 2a61b7ea-0030-4df5-98c4-9184b44c3768
md"""
Example of derivation tree from example 4.4 on page 83:
"""

# ╔═╡ 82272fb8-ffe1-4842-b969-c4528ae80aaa
begin
	DT = DerivTree
	dtG = DT("S", 
		[
			DT("a",[]),
			DT("A", [
				DT("S",[
					DT("a", []),
				]),
				DT("b", []),
				DT("A", [
					DT("b", []),
					DT("a", [])
				])
			]),
			DT("S", [
				DT("a",[])
			])
		]
	)
end

# ╔═╡ 1189bc98-6e15-4a71-92b2-1fc2e9be1657
function size(DT::DerivTree)
	arr = [size(x) for x in DT.children]
	if length(arr) == 0
		return 1
	else
		return 1 + sum(arr)
	end
end

# ╔═╡ 6920938e-35c1-4ad6-afdc-7074b6c14864
begin
	function transition_diagram(automata::DFA, state::Int64 = automata.q0)
		Random.seed!(123)
		Q_size = first(size(automata.δ))
		colors = [:white for i in 1:Q_size]
		colors[state] = :gray
		graphplot(
			plot_format(automata);
			fontsize = 15,
			nodeshape = :circle,
			names = 1:Q_size,
			edgelabel = label_edges(automata),
			nodecolor = colors,
			axis_buffer = 0.5,
			self_edge_size = 0.17,
			method = :stress
		)	
	end

	function plot_format(automata::DFA)
		graph = automata.δ
		(m,n) = size(graph)
		vect = [[] for i in 1:automata.Q]
		[push!(vect[i], graph[i,j]) for i = 1:m, j = 1:n  if graph[i,j] != 0]
		return vect
	end

	function label_edges(automata::DFA)
		labels = Dict{Tuple{Int64, Int64, Int64}, Char}()
		graph = automata.δ
		(m,n) = size(graph)
		vect = [[] for i in 1:automata.Q]
		elems = []
		names = []
		for i = 1:m
			matches = findall(x -> x != 0, graph[i,:])
			for e in 1:length(matches)
				j = matches[e]
				push!(elems, (i, graph[i,j]))
				push!(names, automata.Σ[j])
			end
		end
		
		counter = []
		for (i,elem) in enumerate(elems)
			count_ = count(==(elem), counter)
			push!(counter, elem)
			labels[(elem[1], elem[2], count_+1)] = names[i]
		end
		
		return labels
	end
end;

# ╔═╡ ecf0379f-d0f4-471c-8d9a-5a0caf6e7c0d
transition_diagram(dfa1)

# ╔═╡ 19ecd9aa-7a18-47a9-bbab-905e4b605298
transition_diagram(dfa2)

# ╔═╡ 7aeabc41-fbc3-4dac-b2b1-bea71ae1b7da
transition_diagram(enfa)

# ╔═╡ a7437e1e-86ae-4049-b54e-d4bed317a3df
transition_diagram(q1)

# ╔═╡ 32c4dc42-6ab6-40c4-ba3f-f27d049fc2c4
transition_diagram(q2)

# ╔═╡ 757a3ba9-9900-4783-b81c-84649a0dd721
transition_diagram(q3)

# ╔═╡ b8d98eb6-7c33-429d-8f16-127df3b9295a
transition_diagram(nfa2)

# ╔═╡ 9f9a9106-93e2-466a-bd84-007ae0f1f968
transition_diagram(dfa3)

# ╔═╡ 19e1a879-f5d9-48cc-8de6-5d8a4cbe7e66
transition_diagram(enfa3)

# ╔═╡ e8a774be-b3e6-4895-be4e-d1eb17770925
transition_diagram(nfa1)

# ╔═╡ 38eeeab0-7390-4ecb-8649-a215db54bdf9
begin
	current_state = automata.q0
	function show_step(automata, state::String)
		global current_state
		if length(state) > 0
			new_state = δ(automata, current_state,state)
			if new_state != 0
				try
					current_state = new_state
				catch e
					if e isa BoundsError
						println("Move $(num) is not valid.")
					else
						rethrow(e)
					end
				end
			end
		end
		transition_diagram(automata, current_state)
	end
	show_step(automata, answer)
end

# ╔═╡ af24a85b-10dc-4191-9f9c-1feb5b087c9b
label_edges(automata)

# ╔═╡ 7e817f5c-dcce-4c83-8447-e2387cc270e3
function flatten(DT::DerivTree)
	arr = [DT.name]
	for x in DT.children
		append!(arr, flatten(x))
	end
	return arr
end

# ╔═╡ 8761ec2b-a55a-4306-bffa-207653f1236e
flatten(dtG)

# ╔═╡ 31584ad2-69ee-4e51-a953-7b6ed0f6e669
function make_graph!(g, DT::DerivTree, index=1)
	children = DT.children
	sizes = [size(d) for d in children]
	# @info "" DT.name children
	for i in 1:length(children)
		p = i==1 ? 0 : sum(sizes[1:i-1])
		q = index+1 + p
		# @info "" sum(sizes[1:i-1]) (index, q)
		add_edge!(g, index, q)
		make_graph!(g, children[i], q)
	end
end

# ╔═╡ 3bf34379-4cfc-4821-a86b-3585ada6d032
function visualize(DT::DerivTree)
	default(size=(800, 800))
	g = SimpleDiGraph(size(dtG))
	make_graph!(g, DT)

	
	xs, ys, paths = solve_positions(Zarate(), g)
	f, ax, p = GraphMakie.graphplot(g,
		layout = Point.(zip(xs,ys)),
		arrow_shift=:end, 
		arrow_size=20,
		# ilabels=["$i. $(flatten(dtG)[i])" for i=1:size(dtG)],
		ilabels=["$(flatten(dtG)[i])" for i=1:size(dtG)],
	)
	hidedecorations!(ax); hidespines!(ax); ax.aspect = DataAspect()
	f
	# Random.seed!(1234)
	# @info "" [x for x in vertices(g)] [x for x in edges(g)]
	# GraphRecipes.graphplot(g, names=flatten(dtG), method=:tree, fontsize=10, nodeshape=:rect)
end

# ╔═╡ e7d21766-9690-4ede-9eca-fdb1af86f246
visualize(dtG)

# ╔═╡ 4d1cc7d4-95c3-466a-9d0d-234031ca7782
md"""
Wow, that was quite tedious. Fortunately parsers can do this for us and break down input strings to their parse tree representations automatically. Let's see which string does this derivation tree yield:
"""

# ╔═╡ afe11549-6acc-42c7-a7f4-f0e1d7cd1692
function yield(dt::DerivTree)
	if length(dt.children) == 0
		return dt.name
	else
		return join([yield(child) for child in dt.children])
	end
end

# ╔═╡ 7423ca4f-cc69-4979-8d7f-706a41c2e283
yield(dtG)

# ╔═╡ 13a5455e-57e4-4189-ba03-afaa20da4182
function plot(dt::DerivTree)
end

# ╔═╡ 99405ef9-7d99-401f-ab77-45846a5c6259
function minimize(dfa::DFA)	
	
	F = sort(collect(dfa.F))
	Q = sort(collect(dfa.Q))
	Σ = sort(collect(dfa.Σ))
	Q_F = filter(x->x ∉ F, Q)

	Q_len = length(Q)
	
	indexify(arr) = [(findfirst(x->x==p, Q), findfirst(x->x==q, Q)) for (p,q) in arr]
	indexify2(arr) = [findfirst(x->x==p, Q) for p in arr]
	
	marked = isone.(zeros(Q_len, Q_len))
	
	FQ_F = indexify([(p, q) for p in F for q in Q_F])
	FF = indexify([(p, q) for p in F for q in F])
	Q_FQ_F = indexify([(p, q) for p in Q_F for q in Q_F])
	FFQ_FQ_F = append!(FF, Q_FQ_F)

	FQ_F2 = indexify2(append!([p for p in F], [p for p in Q_F]))
	lists = Array{Vector}(undef, length(FQ_F2), length(FQ_F2), length(Σ))
	for ind in [(i,j) for i=1:length(FQ_F2) for j=1:length(FQ_F2)]
		for a in Σ
			lists[ind..., findfirst(x->x==a, Σ)] = []
		end
	end
		
# ----------------------------step 1----------------------------
	for ind in FQ_F
		marked[ind[1], ind[2]] = 1
		marked[ind[2], ind[1]] = 1
	end

# ----------------------------step 2----------------------------
	for (p,q) in FFQ_FQ_F
		if p != q
			mark = false
# ----------------------------step 3----------------------------
			for a in Σ
				(r,s) = (dfa.δ[(Q[p], a)], dfa.δ[(Q[q], a)])
				(r,s) = (findfirst(x->x==r, Q), findfirst(x->x==s, Q))
				if marked[r,s] == 1
# ----------------------------step 4----------------------------
					marked[p, q] = 1
					marked[q, p] = 1
					for ind in lists[p, q, findfirst(x->x==a, Σ)]
						marked[ind[1], ind[2]] = 1
						marked[ind[2], ind[1]] = 1
					end
					mark = true
				end
			end
			if mark == false
# ----------------------------step 6----------------------------
				for a in Σ
					if dfa.δ[(Q[p], a)] != dfa.δ[(Q[q], a)]
# ----------------------------step 7----------------------------
						push!(lists[p, q, findfirst(x->x==a, Σ)], (p,q))
					end
				end
			end
		end
	end

	subs = Dict()
	for i=1:Q_len
		for j=1:Q_len
			if j<i && marked[i,j] == 0
				subs[Q[i]] = subs[Q[j]] = code_state_name(Set([Q[i], Q[j]]))
			end
		end
	end
	insubs(x) = x ∈ keys(subs) ? subs[x] : "[$x]"

	Q = Set([insubs(x) for x in Q])
	F = Set([insubs(x) for x in F])
	q0 = insubs(dfa.q0)
	δ = Dict(
		[(insubs(a), b) for (a,b) in keys(dfa.δ)] .=> [insubs(x) for x in values(dfa.δ)]
	)
	
	return DFA(Q, dfa.Σ, δ, q0, F)
end

# ╔═╡ fd93a667-1e96-47f2-b648-8342cc1b1cc2
dfa = DFA(
	Set(["a", "b", "c", "d", "e", "f", "g", "h"]),
	Set(['0', '1']),
	Dict(
		("a", '0') => "b",
		("a", '1') => "f",
		
		("b", '1') => "c",
		("b", '0') => "g",

		("c", '1') => "c",
		("c", '0') => "a",

		("d", '1') => "g",
		("d", '0') => "c",
		
		("e", '1') => "f",
		("e", '0') => "h",

		("f", '1') => "g",
		("f", '0') => "c",

		("g", '1') => "e",
		("g", '0') => "g",

		("h", '1') => "c",
		("h", '0') => "g",

	),
	"a",
	Set(["c"])
)

# ╔═╡ 214b88e7-6d5b-4cda-b631-e10d356cefc9
transition_diagram(dfa)

# ╔═╡ f6eeb61f-de47-4b9f-9906-84045543690e
min_dfa = minimize(dfa)

# ╔═╡ 031cba54-13fb-4aae-8de8-a7fd2fdacaa3
transition_diagram(min_dfa)

# ╔═╡ 00000000-0000-0000-0000-000000000001
PLUTO_PROJECT_TOML_CONTENTS = """
[deps]
CairoMakie = "13f3f980-e62b-5c42-98c6-ff1f3baf88f0"
DataStructures = "864edb3b-99cc-5e75-8d2d-829cb0a9cfe8"
GraphMakie = "1ecd5474-83a3-4783-bb4f-06765db800d2"
GraphRecipes = "bd48cda9-67a9-57be-86fa-5b3c104eda73"
Graphs = "86223c79-3864-5bf0-83f7-82e725a168b6"
LayeredLayouts = "f4a74d36-062a-4d48-97cd-1356bad1de4e"
Makie = "ee78f7c6-11fb-53f2-987a-cfe4a2b5a57a"
Plots = "91a5bcdd-55d7-5caf-9e0b-520d859cae80"
PlutoUI = "7f904dfe-b85e-4ff6-b463-dae2292396a8"
Random = "9a3f8284-a2c9-5f02-9a11-845980a1fd5c"

[compat]
CairoMakie = "~0.10.7"
DataStructures = "~0.18.14"
GraphMakie = "~0.5.5"
GraphRecipes = "~0.5.12"
Graphs = "~1.8.0"
LayeredLayouts = "~0.2.9"
Makie = "~0.19.7"
Plots = "~1.38.16"
PlutoUI = "~0.7.51"
"""

# ╔═╡ 00000000-0000-0000-0000-000000000002
PLUTO_MANIFEST_TOML_CONTENTS = """
# This file is machine-generated - editing it directly is not advised

julia_version = "1.9.2"
manifest_format = "2.0"
project_hash = "3669d29010aa61123dc0bfb391402aed73071005"

[[deps.AbstractFFTs]]
deps = ["LinearAlgebra"]
git-tree-sha1 = "cad4c758c0038eea30394b1b671526921ca85b21"
uuid = "621f4979-c628-5d54-868e-fcf4e3e8185c"
version = "1.4.0"
weakdeps = ["ChainRulesCore"]

    [deps.AbstractFFTs.extensions]
    AbstractFFTsChainRulesCoreExt = "ChainRulesCore"

[[deps.AbstractLattices]]
git-tree-sha1 = "f35684b7349da49fcc8a9e520e30e45dbb077166"
uuid = "398f06c4-4d28-53ec-89ca-5b2656b7603d"
version = "0.2.1"

[[deps.AbstractPlutoDingetjes]]
deps = ["Pkg"]
git-tree-sha1 = "8eaf9f1b4921132a4cff3f36a1d9ba923b14a481"
uuid = "6e696c72-6542-2067-7265-42206c756150"
version = "1.1.4"

[[deps.AbstractTrees]]
git-tree-sha1 = "faa260e4cb5aba097a73fab382dd4b5819d8ec8c"
uuid = "1520ce14-60c1-5f80-bbc7-55ef81b5835c"
version = "0.4.4"

[[deps.Adapt]]
deps = ["LinearAlgebra", "Requires"]
git-tree-sha1 = "cc37d689f599e8df4f464b2fa3870ff7db7492ef"
uuid = "79e6a3ab-5dfb-504d-930d-738a2a938a0e"
version = "3.6.1"
weakdeps = ["StaticArrays"]

    [deps.Adapt.extensions]
    AdaptStaticArraysExt = "StaticArrays"

[[deps.Animations]]
deps = ["Colors"]
git-tree-sha1 = "e81c509d2c8e49592413bfb0bb3b08150056c79d"
uuid = "27a7e980-b3e6-11e9-2bcd-0b925532e340"
version = "0.4.1"

[[deps.ArgTools]]
uuid = "0dad84c5-d112-42e6-8d28-ef12dabb789f"
version = "1.1.1"

[[deps.ArnoldiMethod]]
deps = ["LinearAlgebra", "Random", "StaticArrays"]
git-tree-sha1 = "62e51b39331de8911e4a7ff6f5aaf38a5f4cc0ae"
uuid = "ec485272-7323-5ecc-a04f-4719b315124d"
version = "0.2.0"

[[deps.ArrayInterface]]
deps = ["Adapt", "LinearAlgebra", "Requires", "SparseArrays", "SuiteSparse"]
git-tree-sha1 = "f83ec24f76d4c8f525099b2ac475fc098138ec31"
uuid = "4fba245c-0d91-5ea0-9b3e-6abc04ee57a9"
version = "7.4.11"

    [deps.ArrayInterface.extensions]
    ArrayInterfaceBandedMatricesExt = "BandedMatrices"
    ArrayInterfaceBlockBandedMatricesExt = "BlockBandedMatrices"
    ArrayInterfaceCUDAExt = "CUDA"
    ArrayInterfaceGPUArraysCoreExt = "GPUArraysCore"
    ArrayInterfaceStaticArraysCoreExt = "StaticArraysCore"
    ArrayInterfaceTrackerExt = "Tracker"

    [deps.ArrayInterface.weakdeps]
    BandedMatrices = "aae01518-5342-5314-be14-df237901396f"
    BlockBandedMatrices = "ffab5731-97b5-5995-9138-79e8c1846df0"
    CUDA = "052768ef-5323-5732-b1bb-66c8b64840ba"
    GPUArraysCore = "46192b85-c4d5-4398-a991-12ede77f4527"
    StaticArraysCore = "1e83bf80-4336-4d27-bf5d-d5a4f845583c"
    Tracker = "9f7883ad-71c0-57eb-9f7f-b5c9e6d3789c"

[[deps.Artifacts]]
uuid = "56f22d72-fd6d-98f1-02f0-08ddc0907c33"

[[deps.Automa]]
deps = ["ScanByte", "TranscodingStreams"]
git-tree-sha1 = "48e54446df62fdf9ef76959c32dc33f3cff659ee"
uuid = "67c07d97-cdcb-5c2c-af73-a7f9c32a568b"
version = "0.8.3"

[[deps.AxisAlgorithms]]
deps = ["LinearAlgebra", "Random", "SparseArrays", "WoodburyMatrices"]
git-tree-sha1 = "66771c8d21c8ff5e3a93379480a2307ac36863f7"
uuid = "13072b0f-2c55-5437-9ae7-d433b7a33950"
version = "1.0.1"

[[deps.AxisArrays]]
deps = ["Dates", "IntervalSets", "IterTools", "RangeArrays"]
git-tree-sha1 = "16351be62963a67ac4083f748fdb3cca58bfd52f"
uuid = "39de3d68-74b9-583c-8d2d-e117c070f3a9"
version = "0.4.7"

[[deps.Base64]]
uuid = "2a0f44e3-6c83-55bd-87e4-b1978d98bd5f"

[[deps.BenchmarkTools]]
deps = ["JSON", "Logging", "Printf", "Profile", "Statistics", "UUIDs"]
git-tree-sha1 = "d9a9701b899b30332bbcb3e1679c41cce81fb0e8"
uuid = "6e4b80f9-dd63-53aa-95a3-0cdb28fa8baf"
version = "1.3.2"

[[deps.BitFlags]]
git-tree-sha1 = "43b1a4a8f797c1cddadf60499a8a077d4af2cd2d"
uuid = "d1d4a3ce-64b1-5f1a-9ba4-7e7e69966f35"
version = "0.1.7"

[[deps.Bzip2_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "19a35467a82e236ff51bc17a3a44b69ef35185a2"
uuid = "6e34b625-4abd-537c-b88f-471c36dfa7a0"
version = "1.0.8+0"

[[deps.CEnum]]
git-tree-sha1 = "eb4cb44a499229b3b8426dcfb5dd85333951ff90"
uuid = "fa961155-64e5-5f13-b03f-caf6b980ea82"
version = "0.4.2"

[[deps.CRC32c]]
uuid = "8bf52ea8-c179-5cab-976a-9e18b702a9bc"

[[deps.CRlibm]]
deps = ["CRlibm_jll"]
git-tree-sha1 = "32abd86e3c2025db5172aa182b982debed519834"
uuid = "96374032-68de-5a5b-8d9e-752f78720389"
version = "1.0.1"

[[deps.CRlibm_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "e329286945d0cfc04456972ea732551869af1cfc"
uuid = "4e9b3aee-d8a1-5a3d-ad8b-7d824db253f0"
version = "1.0.1+0"

[[deps.Cairo]]
deps = ["Cairo_jll", "Colors", "Glib_jll", "Graphics", "Libdl", "Pango_jll"]
git-tree-sha1 = "d0b3f8b4ad16cb0a2988c6788646a5e6a17b6b1b"
uuid = "159f3aea-2a34-519c-b102-8c37f9878175"
version = "1.0.5"

[[deps.CairoMakie]]
deps = ["Base64", "Cairo", "Colors", "FFTW", "FileIO", "FreeType", "GeometryBasics", "LinearAlgebra", "Makie", "PrecompileTools", "SHA"]
git-tree-sha1 = "e041782fed7614b1726fa250f2bf24fd5c789689"
uuid = "13f3f980-e62b-5c42-98c6-ff1f3baf88f0"
version = "0.10.7"

[[deps.Cairo_jll]]
deps = ["Artifacts", "Bzip2_jll", "CompilerSupportLibraries_jll", "Fontconfig_jll", "FreeType2_jll", "Glib_jll", "JLLWrappers", "LZO_jll", "Libdl", "Pixman_jll", "Pkg", "Xorg_libXext_jll", "Xorg_libXrender_jll", "Zlib_jll", "libpng_jll"]
git-tree-sha1 = "4b859a208b2397a7a623a03449e4636bdb17bcf2"
uuid = "83423d85-b0ee-5818-9007-b63ccbeb887a"
version = "1.16.1+1"

[[deps.Calculus]]
deps = ["LinearAlgebra"]
git-tree-sha1 = "f641eb0a4f00c343bbc32346e1217b86f3ce9dad"
uuid = "49dc2e85-a5d0-5ad3-a950-438e2897f1b9"
version = "0.5.1"

[[deps.ChainRulesCore]]
deps = ["Compat", "LinearAlgebra", "SparseArrays"]
git-tree-sha1 = "c6d890a52d2c4d55d326439580c3b8d0875a77d9"
uuid = "d360d2e6-b24c-11e9-a2a3-2a2ae2dbcce4"
version = "1.15.7"

[[deps.CodecBzip2]]
deps = ["Bzip2_jll", "Libdl", "TranscodingStreams"]
git-tree-sha1 = "2e62a725210ce3c3c2e1a3080190e7ca491f18d7"
uuid = "523fee87-0ab8-5b00-afb7-3ecf72e48cfd"
version = "0.7.2"

[[deps.CodecZlib]]
deps = ["TranscodingStreams", "Zlib_jll"]
git-tree-sha1 = "02aa26a4cf76381be7f66e020a3eddeb27b0a092"
uuid = "944b1d66-785c-5afd-91f1-9de20f533193"
version = "0.7.2"

[[deps.ColorBrewer]]
deps = ["Colors", "JSON", "Test"]
git-tree-sha1 = "61c5334f33d91e570e1d0c3eb5465835242582c4"
uuid = "a2cac450-b92f-5266-8821-25eda20663c8"
version = "0.4.0"

[[deps.ColorSchemes]]
deps = ["ColorTypes", "ColorVectorSpace", "Colors", "FixedPointNumbers", "PrecompileTools", "Random"]
git-tree-sha1 = "be6ab11021cd29f0344d5c4357b163af05a48cba"
uuid = "35d6a980-a343-548e-a6ea-1d62b119f2f4"
version = "3.21.0"

[[deps.ColorTypes]]
deps = ["FixedPointNumbers", "Random"]
git-tree-sha1 = "eb7f0f8307f71fac7c606984ea5fb2817275d6e4"
uuid = "3da002f7-5984-5a60-b8a6-cbb66c0b333f"
version = "0.11.4"

[[deps.ColorVectorSpace]]
deps = ["ColorTypes", "FixedPointNumbers", "LinearAlgebra", "SpecialFunctions", "Statistics", "TensorCore"]
git-tree-sha1 = "600cc5508d66b78aae350f7accdb58763ac18589"
uuid = "c3611d14-8923-5661-9e6a-0046d554d3a4"
version = "0.9.10"

[[deps.Colors]]
deps = ["ColorTypes", "FixedPointNumbers", "Reexport"]
git-tree-sha1 = "fc08e5930ee9a4e03f84bfb5211cb54e7769758a"
uuid = "5ae59095-9a9b-59fe-a467-6f913c188581"
version = "0.12.10"

[[deps.Combinatorics]]
git-tree-sha1 = "08c8b6831dc00bfea825826be0bc8336fc369860"
uuid = "861a8166-3701-5b0c-9a16-15d98fcdc6aa"
version = "1.0.2"

[[deps.CommonSubexpressions]]
deps = ["MacroTools", "Test"]
git-tree-sha1 = "7b8a93dba8af7e3b42fecabf646260105ac373f7"
uuid = "bbf7d656-a473-5ed7-a52c-81e309532950"
version = "0.3.0"

[[deps.Compat]]
deps = ["UUIDs"]
git-tree-sha1 = "7a60c856b9fa189eb34f5f8a6f6b5529b7942957"
uuid = "34da2185-b29b-5c13-b0c7-acf172513d20"
version = "4.6.1"
weakdeps = ["Dates", "LinearAlgebra"]

    [deps.Compat.extensions]
    CompatLinearAlgebraExt = "LinearAlgebra"

[[deps.CompilerSupportLibraries_jll]]
deps = ["Artifacts", "Libdl"]
uuid = "e66e0078-7015-5450-92f7-15fbd957f2ae"
version = "1.0.5+0"

[[deps.ConcurrentUtilities]]
deps = ["Serialization", "Sockets"]
git-tree-sha1 = "5372dbbf8f0bdb8c700db5367132925c0771ef7e"
uuid = "f0e56b4a-5159-44fe-b623-3e5288b988bb"
version = "2.2.1"

[[deps.ConstructionBase]]
deps = ["LinearAlgebra"]
git-tree-sha1 = "fe2838a593b5f776e1597e086dcd47560d94e816"
uuid = "187b0558-2788-49d3-abe0-74a17ed4e7c9"
version = "1.5.3"
weakdeps = ["IntervalSets", "StaticArrays"]

    [deps.ConstructionBase.extensions]
    ConstructionBaseIntervalSetsExt = "IntervalSets"
    ConstructionBaseStaticArraysExt = "StaticArrays"

[[deps.Contour]]
git-tree-sha1 = "d05d9e7b7aedff4e5b51a029dced05cfb6125781"
uuid = "d38c429a-6771-53c6-b99e-75d170b6e991"
version = "0.6.2"

[[deps.DataAPI]]
git-tree-sha1 = "e8119c1a33d267e16108be441a287a6981ba1630"
uuid = "9a962f9c-6df0-11e9-0e5d-c546b8b5ee8a"
version = "1.14.0"

[[deps.DataStructures]]
deps = ["Compat", "InteractiveUtils", "OrderedCollections"]
git-tree-sha1 = "cf25ccb972fec4e4817764d01c82386ae94f77b4"
uuid = "864edb3b-99cc-5e75-8d2d-829cb0a9cfe8"
version = "0.18.14"

[[deps.DataValueInterfaces]]
git-tree-sha1 = "bfc1187b79289637fa0ef6d4436ebdfe6905cbd6"
uuid = "e2d170a0-9d28-54be-80f0-106bbe20a464"
version = "1.0.0"

[[deps.Dates]]
deps = ["Printf"]
uuid = "ade2ca70-3891-5945-98fb-dc099432e06a"

[[deps.DelaunayTriangulation]]
deps = ["DataStructures", "EnumX", "ExactPredicates", "Random", "SimpleGraphs"]
git-tree-sha1 = "a1d8532de83f8ce964235eff1edeff9581144d02"
uuid = "927a84f5-c5f4-47a5-9785-b46e178433df"
version = "0.7.2"
weakdeps = ["MakieCore"]

    [deps.DelaunayTriangulation.extensions]
    DelaunayTriangulationMakieCoreExt = "MakieCore"

[[deps.DelimitedFiles]]
deps = ["Mmap"]
git-tree-sha1 = "9e2f36d3c96a820c678f2f1f1782582fcf685bae"
uuid = "8bb1440f-4735-579b-a4ab-409b98df4dab"
version = "1.9.1"

[[deps.DiffResults]]
deps = ["StaticArraysCore"]
git-tree-sha1 = "782dd5f4561f5d267313f23853baaaa4c52ea621"
uuid = "163ba53b-c6d8-5494-b064-1a9d43ac40c5"
version = "1.1.0"

[[deps.DiffRules]]
deps = ["IrrationalConstants", "LogExpFunctions", "NaNMath", "Random", "SpecialFunctions"]
git-tree-sha1 = "23163d55f885173722d1e4cf0f6110cdbaf7e272"
uuid = "b552c78f-8df3-52c6-915a-8e097449b14b"
version = "1.15.1"

[[deps.Distributed]]
deps = ["Random", "Serialization", "Sockets"]
uuid = "8ba89e20-285c-5b6f-9357-94700520ee1b"

[[deps.Distributions]]
deps = ["FillArrays", "LinearAlgebra", "PDMats", "Printf", "QuadGK", "Random", "SparseArrays", "SpecialFunctions", "Statistics", "StatsAPI", "StatsBase", "StatsFuns", "Test"]
git-tree-sha1 = "e76a3281de2719d7c81ed62c6ea7057380c87b1d"
uuid = "31c24e10-a181-5473-b8eb-7969acd0382f"
version = "0.25.98"

    [deps.Distributions.extensions]
    DistributionsChainRulesCoreExt = "ChainRulesCore"
    DistributionsDensityInterfaceExt = "DensityInterface"

    [deps.Distributions.weakdeps]
    ChainRulesCore = "d360d2e6-b24c-11e9-a2a3-2a2ae2dbcce4"
    DensityInterface = "b429d917-457f-4dbc-8f4c-0cc954292b1d"

[[deps.DocStringExtensions]]
deps = ["LibGit2"]
git-tree-sha1 = "2fb1e02f2b635d0845df5d7c167fec4dd739b00d"
uuid = "ffbed154-4ef7-542d-bbb7-c09d3a79fcae"
version = "0.9.3"

[[deps.Downloads]]
deps = ["ArgTools", "FileWatching", "LibCURL", "NetworkOptions"]
uuid = "f43a241f-c20a-4ad4-852c-f6b1247861c6"
version = "1.6.0"

[[deps.DualNumbers]]
deps = ["Calculus", "NaNMath", "SpecialFunctions"]
git-tree-sha1 = "5837a837389fccf076445fce071c8ddaea35a566"
uuid = "fa6b7ba4-c1ee-5f82-b5fc-ecf0adba8f74"
version = "0.6.8"

[[deps.ECOS]]
deps = ["CEnum", "ECOS_jll", "MathOptInterface"]
git-tree-sha1 = "d1c761af75addf7a29dbb95e488efe57cd9140bd"
uuid = "e2685f51-7e38-5353-a97d-a921fd2c8199"
version = "1.1.1"

[[deps.ECOS_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "5f84034ddd642cf595e57d46ea2f085321c260e4"
uuid = "c2c64177-6a8e-5dca-99a7-64895ad7445f"
version = "200.0.800+0"

[[deps.EarCut_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "e3290f2d49e661fbd94046d7e3726ffcb2d41053"
uuid = "5ae413db-bbd1-5e63-b57d-d24a61df00f5"
version = "2.2.4+0"

[[deps.EnumX]]
git-tree-sha1 = "bdb1942cd4c45e3c678fd11569d5cccd80976237"
uuid = "4e289a0a-7415-4d19-859d-a7e5c4648b56"
version = "1.0.4"

[[deps.ErrorfreeArithmetic]]
git-tree-sha1 = "d6863c556f1142a061532e79f611aa46be201686"
uuid = "90fa49ef-747e-5e6f-a989-263ba693cf1a"
version = "0.5.2"

[[deps.ExactPredicates]]
deps = ["IntervalArithmetic", "Random", "StaticArraysCore", "Test"]
git-tree-sha1 = "276e83bc8b21589b79303b9985c321024ffdf59c"
uuid = "429591f6-91af-11e9-00e2-59fbe8cec110"
version = "2.2.5"

[[deps.ExceptionUnwrapping]]
deps = ["Test"]
git-tree-sha1 = "e90caa41f5a86296e014e148ee061bd6c3edec96"
uuid = "460bff9d-24e4-43bc-9d9f-a8973cb893f4"
version = "0.1.9"

[[deps.Expat_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "bad72f730e9e91c08d9427d5e8db95478a3c323d"
uuid = "2e619515-83b5-522b-bb60-26c02a35a201"
version = "2.4.8+0"

[[deps.Extents]]
git-tree-sha1 = "5e1e4c53fa39afe63a7d356e30452249365fba99"
uuid = "411431e0-e8b7-467b-b5e0-f676ba4f2910"
version = "0.1.1"

[[deps.FFMPEG]]
deps = ["FFMPEG_jll"]
git-tree-sha1 = "b57e3acbe22f8484b4b5ff66a7499717fe1a9cc8"
uuid = "c87230d0-a227-11e9-1b43-d7ebe4e7570a"
version = "0.4.1"

[[deps.FFMPEG_jll]]
deps = ["Artifacts", "Bzip2_jll", "FreeType2_jll", "FriBidi_jll", "JLLWrappers", "LAME_jll", "Libdl", "Ogg_jll", "OpenSSL_jll", "Opus_jll", "PCRE2_jll", "Pkg", "Zlib_jll", "libaom_jll", "libass_jll", "libfdk_aac_jll", "libvorbis_jll", "x264_jll", "x265_jll"]
git-tree-sha1 = "74faea50c1d007c85837327f6775bea60b5492dd"
uuid = "b22a6f82-2f65-5046-a5b2-351ab43fb4e5"
version = "4.4.2+2"

[[deps.FFTW]]
deps = ["AbstractFFTs", "FFTW_jll", "LinearAlgebra", "MKL_jll", "Preferences", "Reexport"]
git-tree-sha1 = "b4fbdd20c889804969571cc589900803edda16b7"
uuid = "7a1cc6ca-52ef-59f5-83cd-3a7055c09341"
version = "1.7.1"

[[deps.FFTW_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "c6033cc3892d0ef5bb9cd29b7f2f0331ea5184ea"
uuid = "f5851436-0d7a-5f13-b9de-f02708fd171a"
version = "3.3.10+0"

[[deps.FastRounding]]
deps = ["ErrorfreeArithmetic", "LinearAlgebra"]
git-tree-sha1 = "6344aa18f654196be82e62816935225b3b9abe44"
uuid = "fa42c844-2597-5d31-933b-ebd51ab2693f"
version = "0.3.1"

[[deps.FileIO]]
deps = ["Pkg", "Requires", "UUIDs"]
git-tree-sha1 = "299dc33549f68299137e51e6d49a13b5b1da9673"
uuid = "5789e2e9-d7fb-5bc7-8068-2c6fae9b9549"
version = "1.16.1"

[[deps.FileWatching]]
uuid = "7b1f6079-737a-58dc-b8bc-7a2ca5c1b5ee"

[[deps.FillArrays]]
deps = ["LinearAlgebra", "Random", "SparseArrays", "Statistics"]
git-tree-sha1 = "f0af9b12329a637e8fba7d6543f915fff6ba0090"
uuid = "1a297f60-69ca-5386-bcde-b61e274b549b"
version = "1.4.2"

[[deps.FiniteDiff]]
deps = ["ArrayInterface", "LinearAlgebra", "Requires", "Setfield", "SparseArrays"]
git-tree-sha1 = "c6e4a1fbe73b31a3dea94b1da449503b8830c306"
uuid = "6a86dc24-6348-571c-b903-95158fe2bd41"
version = "2.21.1"

    [deps.FiniteDiff.extensions]
    FiniteDiffBandedMatricesExt = "BandedMatrices"
    FiniteDiffBlockBandedMatricesExt = "BlockBandedMatrices"
    FiniteDiffStaticArraysExt = "StaticArrays"

    [deps.FiniteDiff.weakdeps]
    BandedMatrices = "aae01518-5342-5314-be14-df237901396f"
    BlockBandedMatrices = "ffab5731-97b5-5995-9138-79e8c1846df0"
    StaticArrays = "90137ffa-7385-5640-81b9-e52037218182"

[[deps.FixedPointNumbers]]
deps = ["Statistics"]
git-tree-sha1 = "335bfdceacc84c5cdf16aadc768aa5ddfc5383cc"
uuid = "53c48c17-4a7d-5ca2-90c5-79b7896eea93"
version = "0.8.4"

[[deps.Fontconfig_jll]]
deps = ["Artifacts", "Bzip2_jll", "Expat_jll", "FreeType2_jll", "JLLWrappers", "Libdl", "Libuuid_jll", "Pkg", "Zlib_jll"]
git-tree-sha1 = "21efd19106a55620a188615da6d3d06cd7f6ee03"
uuid = "a3f928ae-7b40-5064-980b-68af3947d34b"
version = "2.13.93+0"

[[deps.Formatting]]
deps = ["Printf"]
git-tree-sha1 = "8339d61043228fdd3eb658d86c926cb282ae72a8"
uuid = "59287772-0a20-5a39-b81b-1366585eb4c0"
version = "0.4.2"

[[deps.ForwardDiff]]
deps = ["CommonSubexpressions", "DiffResults", "DiffRules", "LinearAlgebra", "LogExpFunctions", "NaNMath", "Preferences", "Printf", "Random", "SpecialFunctions"]
git-tree-sha1 = "00e252f4d706b3d55a8863432e742bf5717b498d"
uuid = "f6369f11-7733-5829-9624-2563aa707210"
version = "0.10.35"
weakdeps = ["StaticArrays"]

    [deps.ForwardDiff.extensions]
    ForwardDiffStaticArraysExt = "StaticArrays"

[[deps.FreeType]]
deps = ["CEnum", "FreeType2_jll"]
git-tree-sha1 = "cabd77ab6a6fdff49bfd24af2ebe76e6e018a2b4"
uuid = "b38be410-82b0-50bf-ab77-7b57e271db43"
version = "4.0.0"

[[deps.FreeType2_jll]]
deps = ["Artifacts", "Bzip2_jll", "JLLWrappers", "Libdl", "Pkg", "Zlib_jll"]
git-tree-sha1 = "87eb71354d8ec1a96d4a7636bd57a7347dde3ef9"
uuid = "d7e528f0-a631-5988-bf34-fe36492bcfd7"
version = "2.10.4+0"

[[deps.FreeTypeAbstraction]]
deps = ["ColorVectorSpace", "Colors", "FreeType", "GeometryBasics"]
git-tree-sha1 = "38a92e40157100e796690421e34a11c107205c86"
uuid = "663a7486-cb36-511b-a19d-713bb74d65c9"
version = "0.10.0"

[[deps.FriBidi_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "aa31987c2ba8704e23c6c8ba8a4f769d5d7e4f91"
uuid = "559328eb-81f9-559d-9380-de523a88c83c"
version = "1.0.10+0"

[[deps.Future]]
deps = ["Random"]
uuid = "9fa8497b-333b-5362-9e8d-4d0656e87820"

[[deps.GLFW_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Libglvnd_jll", "Pkg", "Xorg_libXcursor_jll", "Xorg_libXi_jll", "Xorg_libXinerama_jll", "Xorg_libXrandr_jll"]
git-tree-sha1 = "d972031d28c8c8d9d7b41a536ad7bb0c2579caca"
uuid = "0656b61e-2033-5cc2-a64a-77c0f6c09b89"
version = "3.3.8+0"

[[deps.GPUArraysCore]]
deps = ["Adapt"]
git-tree-sha1 = "1cd7f0af1aa58abc02ea1d872953a97359cb87fa"
uuid = "46192b85-c4d5-4398-a991-12ede77f4527"
version = "0.1.4"

[[deps.GR]]
deps = ["Artifacts", "Base64", "DelimitedFiles", "Downloads", "GR_jll", "HTTP", "JSON", "Libdl", "LinearAlgebra", "Pkg", "Preferences", "Printf", "Random", "Serialization", "Sockets", "TOML", "Tar", "Test", "UUIDs", "p7zip_jll"]
git-tree-sha1 = "d73afa4a2bb9de56077242d98cf763074ab9a970"
uuid = "28b8d3ca-fb5f-59d9-8090-bfdbd6d07a71"
version = "0.72.9"

[[deps.GR_jll]]
deps = ["Artifacts", "Bzip2_jll", "Cairo_jll", "FFMPEG_jll", "Fontconfig_jll", "GLFW_jll", "JLLWrappers", "JpegTurbo_jll", "Libdl", "Libtiff_jll", "Pixman_jll", "Qt6Base_jll", "Zlib_jll", "libpng_jll"]
git-tree-sha1 = "f61f768bf090d97c532d24b64e07b237e9bb7b6b"
uuid = "d2c73de3-f751-5644-a686-071e5b155ba9"
version = "0.72.9+0"

[[deps.GeoInterface]]
deps = ["Extents"]
git-tree-sha1 = "0eb6de0b312688f852f347171aba888658e29f20"
uuid = "cf35fbd7-0cd7-5166-be24-54bfbe79505f"
version = "1.3.0"

[[deps.GeometryBasics]]
deps = ["EarCut_jll", "GeoInterface", "IterTools", "LinearAlgebra", "StaticArrays", "StructArrays", "Tables"]
git-tree-sha1 = "659140c9375afa2f685e37c1a0b9c9a60ef56b40"
uuid = "5c1252a2-5f33-56bf-86c9-59e7332b4326"
version = "0.4.7"

[[deps.GeometryTypes]]
deps = ["ColorTypes", "FixedPointNumbers", "LinearAlgebra", "StaticArrays"]
git-tree-sha1 = "d796f7be0383b5416cd403420ce0af083b0f9b28"
uuid = "4d00f742-c7ba-57c2-abde-4428a4b178cb"
version = "0.8.5"

[[deps.Gettext_jll]]
deps = ["Artifacts", "CompilerSupportLibraries_jll", "JLLWrappers", "Libdl", "Libiconv_jll", "Pkg", "XML2_jll"]
git-tree-sha1 = "9b02998aba7bf074d14de89f9d37ca24a1a0b046"
uuid = "78b55507-aeef-58d4-861c-77aaff3498b1"
version = "0.21.0+0"

[[deps.Glib_jll]]
deps = ["Artifacts", "Gettext_jll", "JLLWrappers", "Libdl", "Libffi_jll", "Libiconv_jll", "Libmount_jll", "PCRE2_jll", "Pkg", "Zlib_jll"]
git-tree-sha1 = "d3b3624125c1474292d0d8ed0f65554ac37ddb23"
uuid = "7746bdde-850d-59dc-9ae8-88ece973131d"
version = "2.74.0+2"

[[deps.GraphMakie]]
deps = ["DataStructures", "GeometryBasics", "Graphs", "LinearAlgebra", "Makie", "NetworkLayout", "PolynomialRoots", "SimpleTraits", "StaticArrays"]
git-tree-sha1 = "969a8bbc241342557197272b6bf31c24768ccedb"
uuid = "1ecd5474-83a3-4783-bb4f-06765db800d2"
version = "0.5.5"

[[deps.GraphRecipes]]
deps = ["AbstractTrees", "GeometryTypes", "Graphs", "InteractiveUtils", "Interpolations", "LinearAlgebra", "NaNMath", "NetworkLayout", "PlotUtils", "RecipesBase", "SparseArrays", "Statistics"]
git-tree-sha1 = "e5f13c467f99f6b348020369c519cd6c8b56f75d"
uuid = "bd48cda9-67a9-57be-86fa-5b3c104eda73"
version = "0.5.12"

[[deps.Graphics]]
deps = ["Colors", "LinearAlgebra", "NaNMath"]
git-tree-sha1 = "d61890399bc535850c4bf08e4e0d3a7ad0f21cbd"
uuid = "a2bd30eb-e257-5431-a919-1863eab51364"
version = "1.1.2"

[[deps.Graphite2_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "344bf40dcab1073aca04aa0df4fb092f920e4011"
uuid = "3b182d85-2403-5c21-9c21-1e1f0cc25472"
version = "1.3.14+0"

[[deps.Graphs]]
deps = ["ArnoldiMethod", "Compat", "DataStructures", "Distributed", "Inflate", "LinearAlgebra", "Random", "SharedArrays", "SimpleTraits", "SparseArrays", "Statistics"]
git-tree-sha1 = "1cf1d7dcb4bc32d7b4a5add4232db3750c27ecb4"
uuid = "86223c79-3864-5bf0-83f7-82e725a168b6"
version = "1.8.0"

[[deps.GridLayoutBase]]
deps = ["GeometryBasics", "InteractiveUtils", "Observables"]
git-tree-sha1 = "678d136003ed5bceaab05cf64519e3f956ffa4ba"
uuid = "3955a311-db13-416c-9275-1d80ed98e5e9"
version = "0.9.1"

[[deps.Grisu]]
git-tree-sha1 = "53bb909d1151e57e2484c3d1b53e19552b887fb2"
uuid = "42e2da0e-8278-4e71-bc24-59509adca0fe"
version = "1.0.2"

[[deps.HTTP]]
deps = ["Base64", "CodecZlib", "ConcurrentUtilities", "Dates", "ExceptionUnwrapping", "Logging", "LoggingExtras", "MbedTLS", "NetworkOptions", "OpenSSL", "Random", "SimpleBufferStream", "Sockets", "URIs", "UUIDs"]
git-tree-sha1 = "cb56ccdd481c0dd7f975ad2b3b62d9eda088f7e2"
uuid = "cd3eb016-35fb-5094-929b-558a96fad6f3"
version = "1.9.14"

[[deps.HarfBuzz_jll]]
deps = ["Artifacts", "Cairo_jll", "Fontconfig_jll", "FreeType2_jll", "Glib_jll", "Graphite2_jll", "JLLWrappers", "Libdl", "Libffi_jll", "Pkg"]
git-tree-sha1 = "129acf094d168394e80ee1dc4bc06ec835e510a3"
uuid = "2e76f6c2-a576-52d4-95c1-20adfe4de566"
version = "2.8.1+1"

[[deps.HiGHS]]
deps = ["HiGHS_jll", "MathOptInterface", "PrecompileTools", "SparseArrays"]
git-tree-sha1 = "bbd4ab443dfac4c9d5c5b40dd45f598dfad2e26a"
uuid = "87dc4568-4c63-4d18-b0c0-bb2238e4078b"
version = "1.5.2"

[[deps.HiGHS_jll]]
deps = ["Artifacts", "CompilerSupportLibraries_jll", "JLLWrappers", "Libdl"]
git-tree-sha1 = "216e7198aeb256e7c7921ef2937d7e1e589ba6fd"
uuid = "8fd58aa0-07eb-5a78-9b36-339c94fd15ea"
version = "1.5.3+0"

[[deps.HypergeometricFunctions]]
deps = ["DualNumbers", "LinearAlgebra", "OpenLibm_jll", "SpecialFunctions"]
git-tree-sha1 = "83e95aaab9dc184a6dcd9c4c52aa0dc26cd14a1d"
uuid = "34004b35-14d8-5ef3-9330-4cdb6864b03a"
version = "0.3.21"

[[deps.Hyperscript]]
deps = ["Test"]
git-tree-sha1 = "8d511d5b81240fc8e6802386302675bdf47737b9"
uuid = "47d2ed2b-36de-50cf-bf87-49c2cf4b8b91"
version = "0.0.4"

[[deps.HypertextLiteral]]
deps = ["Tricks"]
git-tree-sha1 = "c47c5fa4c5308f27ccaac35504858d8914e102f9"
uuid = "ac1192a8-f4b3-4bfe-ba22-af5b92cd3ab2"
version = "0.9.4"

[[deps.IOCapture]]
deps = ["Logging", "Random"]
git-tree-sha1 = "f7be53659ab06ddc986428d3a9dcc95f6fa6705a"
uuid = "b5f81e59-6552-4d32-b1f0-c071b021bf89"
version = "0.2.2"

[[deps.ImageAxes]]
deps = ["AxisArrays", "ImageBase", "ImageCore", "Reexport", "SimpleTraits"]
git-tree-sha1 = "2e4520d67b0cef90865b3ef727594d2a58e0e1f8"
uuid = "2803e5a7-5153-5ecf-9a86-9b4c37f5f5ac"
version = "0.6.11"

[[deps.ImageBase]]
deps = ["ImageCore", "Reexport"]
git-tree-sha1 = "b51bb8cae22c66d0f6357e3bcb6363145ef20835"
uuid = "c817782e-172a-44cc-b673-b171935fbb9e"
version = "0.1.5"

[[deps.ImageCore]]
deps = ["AbstractFFTs", "ColorVectorSpace", "Colors", "FixedPointNumbers", "Graphics", "MappedArrays", "MosaicViews", "OffsetArrays", "PaddedViews", "Reexport"]
git-tree-sha1 = "acf614720ef026d38400b3817614c45882d75500"
uuid = "a09fc81d-aa75-5fe9-8630-4744c3626534"
version = "0.9.4"

[[deps.ImageIO]]
deps = ["FileIO", "IndirectArrays", "JpegTurbo", "LazyModules", "Netpbm", "OpenEXR", "PNGFiles", "QOI", "Sixel", "TiffImages", "UUIDs"]
git-tree-sha1 = "bca20b2f5d00c4fbc192c3212da8fa79f4688009"
uuid = "82e4d734-157c-48bb-816b-45c225c6df19"
version = "0.6.7"

[[deps.ImageMetadata]]
deps = ["AxisArrays", "ImageAxes", "ImageBase", "ImageCore"]
git-tree-sha1 = "355e2b974f2e3212a75dfb60519de21361ad3cb7"
uuid = "bc367c6b-8a6b-528e-b4bd-a4b897500b49"
version = "0.9.9"

[[deps.Imath_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl"]
git-tree-sha1 = "3d09a9f60edf77f8a4d99f9e015e8fbf9989605d"
uuid = "905a6f67-0a94-5f89-b386-d35d92009cd1"
version = "3.1.7+0"

[[deps.IndirectArrays]]
git-tree-sha1 = "012e604e1c7458645cb8b436f8fba789a51b257f"
uuid = "9b13fd28-a010-5f03-acff-a1bbcff69959"
version = "1.0.0"

[[deps.Inflate]]
git-tree-sha1 = "5cd07aab533df5170988219191dfad0519391428"
uuid = "d25df0c9-e2be-5dd7-82c8-3ad0b3e990b9"
version = "0.1.3"

[[deps.IntegerMathUtils]]
git-tree-sha1 = "b8ffb903da9f7b8cf695a8bead8e01814aa24b30"
uuid = "18e54dd8-cb9d-406c-a71d-865a43cbb235"
version = "0.1.2"

[[deps.IntelOpenMP_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "0cb9352ef2e01574eeebdb102948a58740dcaf83"
uuid = "1d5cc7b8-4909-519e-a0f8-d0f5ad9712d0"
version = "2023.1.0+0"

[[deps.InteractiveUtils]]
deps = ["Markdown"]
uuid = "b77e0a4c-d291-57a0-90e8-8db25a27a240"

[[deps.Interpolations]]
deps = ["Adapt", "AxisAlgorithms", "ChainRulesCore", "LinearAlgebra", "OffsetArrays", "Random", "Ratios", "Requires", "SharedArrays", "SparseArrays", "StaticArrays", "WoodburyMatrices"]
git-tree-sha1 = "721ec2cf720536ad005cb38f50dbba7b02419a15"
uuid = "a98d9a8b-a2ab-59e6-89dd-64a1c18fca59"
version = "0.14.7"

[[deps.IntervalArithmetic]]
deps = ["CRlibm", "FastRounding", "LinearAlgebra", "Markdown", "Random", "RecipesBase", "RoundingEmulator", "SetRounding", "StaticArrays"]
git-tree-sha1 = "5ab7744289be503d76a944784bac3f2df7b809af"
uuid = "d1acc4aa-44c8-5952-acd4-ba5d80a2a253"
version = "0.20.9"

[[deps.IntervalSets]]
deps = ["Dates", "Random", "Statistics"]
git-tree-sha1 = "16c0cc91853084cb5f58a78bd209513900206ce6"
uuid = "8197267c-284f-5f27-9208-e0e47529a953"
version = "0.7.4"

[[deps.IrrationalConstants]]
git-tree-sha1 = "630b497eafcc20001bba38a4651b327dcfc491d2"
uuid = "92d709cd-6900-40b7-9082-c6be49f344b6"
version = "0.2.2"

[[deps.Isoband]]
deps = ["isoband_jll"]
git-tree-sha1 = "f9b6d97355599074dc867318950adaa6f9946137"
uuid = "f1662d9f-8043-43de-a69a-05efc1cc6ff4"
version = "0.1.1"

[[deps.IterTools]]
git-tree-sha1 = "fa6287a4469f5e048d763df38279ee729fbd44e5"
uuid = "c8e1da08-722c-5040-9ed9-7db0dc04731e"
version = "1.4.0"

[[deps.IteratorInterfaceExtensions]]
git-tree-sha1 = "a3f24677c21f5bbe9d2a714f95dcd58337fb2856"
uuid = "82899510-4779-5014-852e-03e436cf321d"
version = "1.0.0"

[[deps.JLFzf]]
deps = ["Pipe", "REPL", "Random", "fzf_jll"]
git-tree-sha1 = "f377670cda23b6b7c1c0b3893e37451c5c1a2185"
uuid = "1019f520-868f-41f5-a6de-eb00f4b6a39c"
version = "0.1.5"

[[deps.JLLWrappers]]
deps = ["Preferences"]
git-tree-sha1 = "abc9885a7ca2052a736a600f7fa66209f96506e1"
uuid = "692b3bcd-3c85-4b1f-b108-f13ce0eb3210"
version = "1.4.1"

[[deps.JSON]]
deps = ["Dates", "Mmap", "Parsers", "Unicode"]
git-tree-sha1 = "31e996f0a15c7b280ba9f76636b3ff9e2ae58c9a"
uuid = "682c06a0-de6a-54ab-a142-c8b1cf79cde6"
version = "0.21.4"

[[deps.JpegTurbo]]
deps = ["CEnum", "FileIO", "ImageCore", "JpegTurbo_jll", "TOML"]
git-tree-sha1 = "327713faef2a3e5c80f96bf38d1fa26f7a6ae29e"
uuid = "b835a17e-a41a-41e7-81f0-2f016b05efe0"
version = "0.1.3"

[[deps.JpegTurbo_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl"]
git-tree-sha1 = "6f2675ef130a300a112286de91973805fcc5ffbc"
uuid = "aacddb02-875f-59d6-b918-886e6ef4fbf8"
version = "2.1.91+0"

[[deps.JuMP]]
deps = ["LinearAlgebra", "MathOptInterface", "MutableArithmetics", "OrderedCollections", "Printf", "SnoopPrecompile", "SparseArrays"]
git-tree-sha1 = "b0ded4f36829f7cfd4400b11289faf9b4f0b795a"
uuid = "4076af6c-e467-56ae-b986-b466b2749572"
version = "1.12.0"

[[deps.KernelDensity]]
deps = ["Distributions", "DocStringExtensions", "FFTW", "Interpolations", "StatsBase"]
git-tree-sha1 = "90442c50e202a5cdf21a7899c66b240fdef14035"
uuid = "5ab0869b-81aa-558d-bb23-cbf5423bbe9b"
version = "0.6.7"

[[deps.LAME_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "f6250b16881adf048549549fba48b1161acdac8c"
uuid = "c1c5ebd0-6772-5130-a774-d5fcae4a789d"
version = "3.100.1+0"

[[deps.LERC_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "bf36f528eec6634efc60d7ec062008f171071434"
uuid = "88015f11-f218-50d7-93a8-a6af411a945d"
version = "3.0.0+1"

[[deps.LZO_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "e5b909bcf985c5e2605737d2ce278ed791b89be6"
uuid = "dd4b983a-f0e5-5f8d-a1b7-129d4a5fb1ac"
version = "2.10.1+0"

[[deps.LaTeXStrings]]
git-tree-sha1 = "f2355693d6778a178ade15952b7ac47a4ff97996"
uuid = "b964fa9f-0449-5b57-a5c2-d3ea65f4040f"
version = "1.3.0"

[[deps.Latexify]]
deps = ["Formatting", "InteractiveUtils", "LaTeXStrings", "MacroTools", "Markdown", "OrderedCollections", "Printf", "Requires"]
git-tree-sha1 = "f428ae552340899a935973270b8d98e5a31c49fe"
uuid = "23fbe1c1-3f47-55db-b15f-69d7ec21a316"
version = "0.16.1"

    [deps.Latexify.extensions]
    DataFramesExt = "DataFrames"
    SymEngineExt = "SymEngine"

    [deps.Latexify.weakdeps]
    DataFrames = "a93c6f00-e57d-5684-b7b6-d8193f3e46c0"
    SymEngine = "123dc426-2d89-5057-bbad-38513e3affd8"

[[deps.LayeredLayouts]]
deps = ["Dates", "ECOS", "Graphs", "HiGHS", "IterTools", "JuMP", "Random"]
git-tree-sha1 = "4027b534d46d614e11a37ee33e46d9741e5a3367"
uuid = "f4a74d36-062a-4d48-97cd-1356bad1de4e"
version = "0.2.9"

[[deps.LazyArtifacts]]
deps = ["Artifacts", "Pkg"]
uuid = "4af54fe1-eca0-43a8-85a7-787d91b784e3"

[[deps.LazyModules]]
git-tree-sha1 = "a560dd966b386ac9ae60bdd3a3d3a326062d3c3e"
uuid = "8cdb02fc-e678-4876-92c5-9defec4f444e"
version = "0.3.1"

[[deps.LibCURL]]
deps = ["LibCURL_jll", "MozillaCACerts_jll"]
uuid = "b27032c2-a3e7-50c8-80cd-2d36dbcbfd21"
version = "0.6.3"

[[deps.LibCURL_jll]]
deps = ["Artifacts", "LibSSH2_jll", "Libdl", "MbedTLS_jll", "Zlib_jll", "nghttp2_jll"]
uuid = "deac9b47-8bc7-5906-a0fe-35ac56dc84c0"
version = "7.84.0+0"

[[deps.LibGit2]]
deps = ["Base64", "NetworkOptions", "Printf", "SHA"]
uuid = "76f85450-5226-5b5a-8eaa-529ad045b433"

[[deps.LibSSH2_jll]]
deps = ["Artifacts", "Libdl", "MbedTLS_jll"]
uuid = "29816b5a-b9ab-546f-933c-edad1886dfa8"
version = "1.10.2+0"

[[deps.Libdl]]
uuid = "8f399da3-3557-5675-b5ff-fb832c97cbdb"

[[deps.Libffi_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "0b4a5d71f3e5200a7dff793393e09dfc2d874290"
uuid = "e9f186c6-92d2-5b65-8a66-fee21dc1b490"
version = "3.2.2+1"

[[deps.Libgcrypt_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Libgpg_error_jll", "Pkg"]
git-tree-sha1 = "64613c82a59c120435c067c2b809fc61cf5166ae"
uuid = "d4300ac3-e22c-5743-9152-c294e39db1e4"
version = "1.8.7+0"

[[deps.Libglvnd_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg", "Xorg_libX11_jll", "Xorg_libXext_jll"]
git-tree-sha1 = "6f73d1dd803986947b2c750138528a999a6c7733"
uuid = "7e76a0d4-f3c7-5321-8279-8d96eeed0f29"
version = "1.6.0+0"

[[deps.Libgpg_error_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "c333716e46366857753e273ce6a69ee0945a6db9"
uuid = "7add5ba3-2f88-524e-9cd5-f83b8a55f7b8"
version = "1.42.0+0"

[[deps.Libiconv_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "c7cb1f5d892775ba13767a87c7ada0b980ea0a71"
uuid = "94ce4f54-9a6c-5748-9c1c-f9c7231a4531"
version = "1.16.1+2"

[[deps.Libmount_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "9c30530bf0effd46e15e0fdcf2b8636e78cbbd73"
uuid = "4b2f31a3-9ecc-558c-b454-b3730dcb73e9"
version = "2.35.0+0"

[[deps.Libtiff_jll]]
deps = ["Artifacts", "JLLWrappers", "JpegTurbo_jll", "LERC_jll", "Libdl", "XZ_jll", "Zlib_jll", "Zstd_jll"]
git-tree-sha1 = "2da088d113af58221c52828a80378e16be7d037a"
uuid = "89763e89-9b03-5906-acba-b20f662cd828"
version = "4.5.1+1"

[[deps.Libuuid_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "7f3efec06033682db852f8b3bc3c1d2b0a0ab066"
uuid = "38a345b3-de98-5d2b-a5d3-14cd9215e700"
version = "2.36.0+0"

[[deps.LightXML]]
deps = ["Libdl", "XML2_jll"]
git-tree-sha1 = "e129d9391168c677cd4800f5c0abb1ed8cb3794f"
uuid = "9c8b4983-aa76-5018-a973-4c85ecc9e179"
version = "0.9.0"

[[deps.LineSearches]]
deps = ["LinearAlgebra", "NLSolversBase", "NaNMath", "Parameters", "Printf"]
git-tree-sha1 = "7bbea35cec17305fc70a0e5b4641477dc0789d9d"
uuid = "d3d80556-e9d4-5f37-9878-2ab0fcc64255"
version = "7.2.0"

[[deps.LinearAlgebra]]
deps = ["Libdl", "OpenBLAS_jll", "libblastrampoline_jll"]
uuid = "37e2e46d-f89d-539d-b4ee-838fcccc9c8e"

[[deps.LinearAlgebraX]]
deps = ["LinearAlgebra", "Mods", "Permutations", "Primes", "SimplePolynomials"]
git-tree-sha1 = "558a338f1eeabe933f9c2d4052aa7c2c707c3d52"
uuid = "9b3f67b0-2d00-526e-9884-9e4938f8fb88"
version = "0.1.12"

[[deps.LogExpFunctions]]
deps = ["DocStringExtensions", "IrrationalConstants", "LinearAlgebra"]
git-tree-sha1 = "0a1b7c2863e44523180fdb3146534e265a91870b"
uuid = "2ab3a3ac-af41-5b50-aa03-7779005ae688"
version = "0.3.23"

    [deps.LogExpFunctions.extensions]
    LogExpFunctionsChainRulesCoreExt = "ChainRulesCore"
    LogExpFunctionsChangesOfVariablesExt = "ChangesOfVariables"
    LogExpFunctionsInverseFunctionsExt = "InverseFunctions"

    [deps.LogExpFunctions.weakdeps]
    ChainRulesCore = "d360d2e6-b24c-11e9-a2a3-2a2ae2dbcce4"
    ChangesOfVariables = "9e997f8a-9a97-42d5-a9f1-ce6bfc15e2c0"
    InverseFunctions = "3587e190-3f89-42d0-90ee-14403ec27112"

[[deps.Logging]]
uuid = "56ddb016-857b-54e1-b83d-db4d58db5568"

[[deps.LoggingExtras]]
deps = ["Dates", "Logging"]
git-tree-sha1 = "cedb76b37bc5a6c702ade66be44f831fa23c681e"
uuid = "e6f89c97-d47a-5376-807f-9c37f3926c36"
version = "1.0.0"

[[deps.MIMEs]]
git-tree-sha1 = "65f28ad4b594aebe22157d6fac869786a255b7eb"
uuid = "6c6e2e6c-3030-632d-7369-2d6c69616d65"
version = "0.1.4"

[[deps.MKL_jll]]
deps = ["Artifacts", "IntelOpenMP_jll", "JLLWrappers", "LazyArtifacts", "Libdl", "Pkg"]
git-tree-sha1 = "154d7aaa82d24db6d8f7e4ffcfe596f40bff214b"
uuid = "856f044c-d86e-5d09-b602-aeab76dc8ba7"
version = "2023.1.0+0"

[[deps.MacroTools]]
deps = ["Markdown", "Random"]
git-tree-sha1 = "42324d08725e200c23d4dfb549e0d5d89dede2d2"
uuid = "1914dd2f-81c6-5fcd-8719-6d5c9610ff09"
version = "0.5.10"

[[deps.Makie]]
deps = ["Animations", "Base64", "ColorBrewer", "ColorSchemes", "ColorTypes", "Colors", "Contour", "DelaunayTriangulation", "Distributions", "DocStringExtensions", "Downloads", "FFMPEG", "FileIO", "FixedPointNumbers", "Formatting", "FreeType", "FreeTypeAbstraction", "GeometryBasics", "GridLayoutBase", "ImageIO", "InteractiveUtils", "IntervalSets", "Isoband", "KernelDensity", "LaTeXStrings", "LinearAlgebra", "MacroTools", "MakieCore", "Markdown", "Match", "MathTeXEngine", "Observables", "OffsetArrays", "Packing", "PlotUtils", "PolygonOps", "PrecompileTools", "Printf", "REPL", "Random", "RelocatableFolders", "Setfield", "ShaderAbstractions", "Showoff", "SignedDistanceFields", "SparseArrays", "StableHashTraits", "Statistics", "StatsBase", "StatsFuns", "StructArrays", "TriplotBase", "UnicodeFun"]
git-tree-sha1 = "729640354756782c89adba8857085a69e19be7ab"
uuid = "ee78f7c6-11fb-53f2-987a-cfe4a2b5a57a"
version = "0.19.7"

[[deps.MakieCore]]
deps = ["Observables"]
git-tree-sha1 = "87a85ff81583bd392642869557cb633532989517"
uuid = "20f20a25-4f0e-4fdf-b5d1-57303727442b"
version = "0.6.4"

[[deps.MappedArrays]]
git-tree-sha1 = "2dab0221fe2b0f2cb6754eaa743cc266339f527e"
uuid = "dbb5928d-eab1-5f90-85c2-b9b0edb7c900"
version = "0.4.2"

[[deps.Markdown]]
deps = ["Base64"]
uuid = "d6f4376e-aef5-505a-96c1-9c027394607a"

[[deps.Match]]
git-tree-sha1 = "1d9bc5c1a6e7ee24effb93f175c9342f9154d97f"
uuid = "7eb4fadd-790c-5f42-8a69-bfa0b872bfbf"
version = "1.2.0"

[[deps.MathOptInterface]]
deps = ["BenchmarkTools", "CodecBzip2", "CodecZlib", "DataStructures", "ForwardDiff", "JSON", "LinearAlgebra", "MutableArithmetics", "NaNMath", "OrderedCollections", "PrecompileTools", "Printf", "SparseArrays", "SpecialFunctions", "Test", "Unicode"]
git-tree-sha1 = "5c5cd501ae1d76d3ccd7c7e6b4325a15dde7f31c"
uuid = "b8f27783-ece8-5eb3-8dc8-9495eed66fee"
version = "1.18.0"

[[deps.MathTeXEngine]]
deps = ["AbstractTrees", "Automa", "DataStructures", "FreeTypeAbstraction", "GeometryBasics", "LaTeXStrings", "REPL", "RelocatableFolders", "Test", "UnicodeFun"]
git-tree-sha1 = "8f52dbaa1351ce4cb847d95568cb29e62a307d93"
uuid = "0a4f8689-d25c-4efe-a92b-7142dfc1aa53"
version = "0.5.6"

[[deps.MbedTLS]]
deps = ["Dates", "MbedTLS_jll", "MozillaCACerts_jll", "Random", "Sockets"]
git-tree-sha1 = "03a9b9718f5682ecb107ac9f7308991db4ce395b"
uuid = "739be429-bea8-5141-9913-cc70e7f3736d"
version = "1.1.7"

[[deps.MbedTLS_jll]]
deps = ["Artifacts", "Libdl"]
uuid = "c8ffd9c3-330d-5841-b78e-0817d7145fa1"
version = "2.28.2+0"

[[deps.Measures]]
git-tree-sha1 = "c13304c81eec1ed3af7fc20e75fb6b26092a1102"
uuid = "442fdcdd-2543-5da2-b0f3-8c86c306513e"
version = "0.3.2"

[[deps.Missings]]
deps = ["DataAPI"]
git-tree-sha1 = "f66bdc5de519e8f8ae43bdc598782d35a25b1272"
uuid = "e1d29d7a-bbdc-5cf2-9ac0-f12de2c33e28"
version = "1.1.0"

[[deps.Mmap]]
uuid = "a63ad114-7e13-5084-954f-fe012c677804"

[[deps.Mods]]
git-tree-sha1 = "61be59e4daffff43a8cec04b5e0dc773cbb5db3a"
uuid = "7475f97c-0381-53b1-977b-4c60186c8d62"
version = "1.3.3"

[[deps.MosaicViews]]
deps = ["MappedArrays", "OffsetArrays", "PaddedViews", "StackViews"]
git-tree-sha1 = "7b86a5d4d70a9f5cdf2dacb3cbe6d251d1a61dbe"
uuid = "e94cdb99-869f-56ef-bcf0-1ae2bcbe0389"
version = "0.3.4"

[[deps.MozillaCACerts_jll]]
uuid = "14a3606d-f60d-562e-9121-12d972cd8159"
version = "2022.10.11"

[[deps.Multisets]]
git-tree-sha1 = "8d852646862c96e226367ad10c8af56099b4047e"
uuid = "3b2b4ff1-bcff-5658-a3ee-dbcf1ce5ac09"
version = "0.4.4"

[[deps.MutableArithmetics]]
deps = ["LinearAlgebra", "SparseArrays", "Test"]
git-tree-sha1 = "964cb1a7069723727025ae295408747a0b36a854"
uuid = "d8a4904e-b15c-11e9-3269-09a3773c0cb0"
version = "1.3.0"

[[deps.NLSolversBase]]
deps = ["DiffResults", "Distributed", "FiniteDiff", "ForwardDiff"]
git-tree-sha1 = "a0b464d183da839699f4c79e7606d9d186ec172c"
uuid = "d41bc354-129a-5804-8e4c-c37616107c6c"
version = "7.8.3"

[[deps.NaNMath]]
deps = ["OpenLibm_jll"]
git-tree-sha1 = "0877504529a3e5c3343c6f8b4c0381e57e4387e4"
uuid = "77ba4419-2d1f-58cd-9bb1-8ffee604a2e3"
version = "1.0.2"

[[deps.Netpbm]]
deps = ["FileIO", "ImageCore", "ImageMetadata"]
git-tree-sha1 = "d92b107dbb887293622df7697a2223f9f8176fcd"
uuid = "f09324ee-3d7c-5217-9330-fc30815ba969"
version = "1.1.1"

[[deps.NetworkLayout]]
deps = ["GeometryBasics", "LinearAlgebra", "Random", "Requires", "SparseArrays", "StaticArrays"]
git-tree-sha1 = "2bfd8cd7fba3e46ce48139ae93904ee848153660"
uuid = "46757867-2c16-5918-afeb-47bfcb05e46a"
version = "0.4.5"

[[deps.NetworkOptions]]
uuid = "ca575930-c2e3-43a9-ace4-1e988b2c1908"
version = "1.2.0"

[[deps.Observables]]
git-tree-sha1 = "6862738f9796b3edc1c09d0890afce4eca9e7e93"
uuid = "510215fc-4207-5dde-b226-833fc4488ee2"
version = "0.5.4"

[[deps.OffsetArrays]]
deps = ["Adapt"]
git-tree-sha1 = "82d7c9e310fe55aa54996e6f7f94674e2a38fcb4"
uuid = "6fe1bfb0-de20-5000-8ca7-80f57d26f881"
version = "1.12.9"

[[deps.Ogg_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "887579a3eb005446d514ab7aeac5d1d027658b8f"
uuid = "e7412a2a-1a6e-54c0-be00-318e2571c051"
version = "1.3.5+1"

[[deps.OpenBLAS_jll]]
deps = ["Artifacts", "CompilerSupportLibraries_jll", "Libdl"]
uuid = "4536629a-c528-5b80-bd46-f80d51c5b363"
version = "0.3.21+4"

[[deps.OpenEXR]]
deps = ["Colors", "FileIO", "OpenEXR_jll"]
git-tree-sha1 = "327f53360fdb54df7ecd01e96ef1983536d1e633"
uuid = "52e1d378-f018-4a11-a4be-720524705ac7"
version = "0.3.2"

[[deps.OpenEXR_jll]]
deps = ["Artifacts", "Imath_jll", "JLLWrappers", "Libdl", "Zlib_jll"]
git-tree-sha1 = "a4ca623df1ae99d09bc9868b008262d0c0ac1e4f"
uuid = "18a262bb-aa17-5467-a713-aee519bc75cb"
version = "3.1.4+0"

[[deps.OpenLibm_jll]]
deps = ["Artifacts", "Libdl"]
uuid = "05823500-19ac-5b8b-9628-191a04bc5112"
version = "0.8.1+0"

[[deps.OpenSSL]]
deps = ["BitFlags", "Dates", "MozillaCACerts_jll", "OpenSSL_jll", "Sockets"]
git-tree-sha1 = "51901a49222b09e3743c65b8847687ae5fc78eb2"
uuid = "4d8831e6-92b7-49fb-bdf8-b643e874388c"
version = "1.4.1"

[[deps.OpenSSL_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "9ff31d101d987eb9d66bd8b176ac7c277beccd09"
uuid = "458c3c95-2e84-50aa-8efc-19380b2a3a95"
version = "1.1.20+0"

[[deps.OpenSpecFun_jll]]
deps = ["Artifacts", "CompilerSupportLibraries_jll", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "13652491f6856acfd2db29360e1bbcd4565d04f1"
uuid = "efe28fd5-8261-553b-a9e1-b2916fc3738e"
version = "0.5.5+0"

[[deps.Optim]]
deps = ["Compat", "FillArrays", "ForwardDiff", "LineSearches", "LinearAlgebra", "NLSolversBase", "NaNMath", "Parameters", "PositiveFactorizations", "Printf", "SparseArrays", "StatsBase"]
git-tree-sha1 = "e3a6546c1577bfd701771b477b794a52949e7594"
uuid = "429524aa-4258-5aef-a3af-852621145aeb"
version = "1.7.6"

[[deps.Opus_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "51a08fb14ec28da2ec7a927c4337e4332c2a4720"
uuid = "91d4177d-7536-5919-b921-800302f37372"
version = "1.3.2+0"

[[deps.OrderedCollections]]
git-tree-sha1 = "d321bf2de576bf25ec4d3e4360faca399afca282"
uuid = "bac558e1-5e72-5ebc-8fee-abe8a469f55d"
version = "1.6.0"

[[deps.PCRE2_jll]]
deps = ["Artifacts", "Libdl"]
uuid = "efcefdf7-47ab-520b-bdef-62a2eaa19f15"
version = "10.42.0+0"

[[deps.PDMats]]
deps = ["LinearAlgebra", "SparseArrays", "SuiteSparse"]
git-tree-sha1 = "67eae2738d63117a196f497d7db789821bce61d1"
uuid = "90014a1f-27ba-587c-ab20-58faa44d9150"
version = "0.11.17"

[[deps.PNGFiles]]
deps = ["Base64", "CEnum", "ImageCore", "IndirectArrays", "OffsetArrays", "libpng_jll"]
git-tree-sha1 = "9b02b27ac477cad98114584ff964e3052f656a0f"
uuid = "f57f5aa1-a3ce-4bc8-8ab9-96f992907883"
version = "0.4.0"

[[deps.Packing]]
deps = ["GeometryBasics"]
git-tree-sha1 = "ec3edfe723df33528e085e632414499f26650501"
uuid = "19eb6ba3-879d-56ad-ad62-d5c202156566"
version = "0.5.0"

[[deps.PaddedViews]]
deps = ["OffsetArrays"]
git-tree-sha1 = "0fac6313486baae819364c52b4f483450a9d793f"
uuid = "5432bcbf-9aad-5242-b902-cca2824c8663"
version = "0.5.12"

[[deps.Pango_jll]]
deps = ["Artifacts", "Cairo_jll", "Fontconfig_jll", "FreeType2_jll", "FriBidi_jll", "Glib_jll", "HarfBuzz_jll", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "84a314e3926ba9ec66ac097e3635e270986b0f10"
uuid = "36c8627f-9965-5494-a995-c6b170f724f3"
version = "1.50.9+0"

[[deps.Parameters]]
deps = ["OrderedCollections", "UnPack"]
git-tree-sha1 = "34c0e9ad262e5f7fc75b10a9952ca7692cfc5fbe"
uuid = "d96e819e-fc66-5662-9728-84c9c7592b0a"
version = "0.12.3"

[[deps.Parsers]]
deps = ["Dates", "SnoopPrecompile"]
git-tree-sha1 = "478ac6c952fddd4399e71d4779797c538d0ff2bf"
uuid = "69de0a69-1ddd-5017-9359-2bf0b02dc9f0"
version = "2.5.8"

[[deps.Permutations]]
deps = ["Combinatorics", "LinearAlgebra", "Random"]
git-tree-sha1 = "6e6cab1c54ae2382bcc48866b91cf949cea703a1"
uuid = "2ae35dd2-176d-5d53-8349-f30d82d94d4f"
version = "0.4.16"

[[deps.Pipe]]
git-tree-sha1 = "6842804e7867b115ca9de748a0cf6b364523c16d"
uuid = "b98c9c47-44ae-5843-9183-064241ee97a0"
version = "1.3.0"

[[deps.Pixman_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "b4f5d02549a10e20780a24fce72bea96b6329e29"
uuid = "30392449-352a-5448-841d-b1acce4e97dc"
version = "0.40.1+0"

[[deps.Pkg]]
deps = ["Artifacts", "Dates", "Downloads", "FileWatching", "LibGit2", "Libdl", "Logging", "Markdown", "Printf", "REPL", "Random", "SHA", "Serialization", "TOML", "Tar", "UUIDs", "p7zip_jll"]
uuid = "44cfe95a-1eb2-52ea-b672-e2afdf69b78f"
version = "1.9.2"

[[deps.PkgVersion]]
deps = ["Pkg"]
git-tree-sha1 = "f6cf8e7944e50901594838951729a1861e668cb8"
uuid = "eebad327-c553-4316-9ea0-9fa01ccd7688"
version = "0.3.2"

[[deps.PlotThemes]]
deps = ["PlotUtils", "Statistics"]
git-tree-sha1 = "1f03a2d339f42dca4a4da149c7e15e9b896ad899"
uuid = "ccf2f8ad-2431-5c83-bf29-c5338b663b6a"
version = "3.1.0"

[[deps.PlotUtils]]
deps = ["ColorSchemes", "Colors", "Dates", "PrecompileTools", "Printf", "Random", "Reexport", "Statistics"]
git-tree-sha1 = "f92e1315dadf8c46561fb9396e525f7200cdc227"
uuid = "995b91a9-d308-5afd-9ec6-746e21dbc043"
version = "1.3.5"

[[deps.Plots]]
deps = ["Base64", "Contour", "Dates", "Downloads", "FFMPEG", "FixedPointNumbers", "GR", "JLFzf", "JSON", "LaTeXStrings", "Latexify", "LinearAlgebra", "Measures", "NaNMath", "Pkg", "PlotThemes", "PlotUtils", "PrecompileTools", "Preferences", "Printf", "REPL", "Random", "RecipesBase", "RecipesPipeline", "Reexport", "RelocatableFolders", "Requires", "Scratch", "Showoff", "SparseArrays", "Statistics", "StatsBase", "UUIDs", "UnicodeFun", "UnitfulLatexify", "Unzip"]
git-tree-sha1 = "75ca67b2c6512ad2d0c767a7cfc55e75075f8bbc"
uuid = "91a5bcdd-55d7-5caf-9e0b-520d859cae80"
version = "1.38.16"

    [deps.Plots.extensions]
    FileIOExt = "FileIO"
    GeometryBasicsExt = "GeometryBasics"
    IJuliaExt = "IJulia"
    ImageInTerminalExt = "ImageInTerminal"
    UnitfulExt = "Unitful"

    [deps.Plots.weakdeps]
    FileIO = "5789e2e9-d7fb-5bc7-8068-2c6fae9b9549"
    GeometryBasics = "5c1252a2-5f33-56bf-86c9-59e7332b4326"
    IJulia = "7073ff75-c697-5162-941a-fcdaad2a7d2a"
    ImageInTerminal = "d8c32880-2388-543b-8c61-d9f865259254"
    Unitful = "1986cc42-f94f-5a68-af5c-568840ba703d"

[[deps.PlutoUI]]
deps = ["AbstractPlutoDingetjes", "Base64", "ColorTypes", "Dates", "FixedPointNumbers", "Hyperscript", "HypertextLiteral", "IOCapture", "InteractiveUtils", "JSON", "Logging", "MIMEs", "Markdown", "Random", "Reexport", "URIs", "UUIDs"]
git-tree-sha1 = "b478a748be27bd2f2c73a7690da219d0844db305"
uuid = "7f904dfe-b85e-4ff6-b463-dae2292396a8"
version = "0.7.51"

[[deps.PolygonOps]]
git-tree-sha1 = "77b3d3605fc1cd0b42d95eba87dfcd2bf67d5ff6"
uuid = "647866c9-e3ac-4575-94e7-e3d426903924"
version = "0.1.2"

[[deps.PolynomialRoots]]
git-tree-sha1 = "5f807b5345093487f733e520a1b7395ee9324825"
uuid = "3a141323-8675-5d76-9d11-e1df1406c778"
version = "1.0.0"

[[deps.Polynomials]]
deps = ["LinearAlgebra", "RecipesBase"]
git-tree-sha1 = "3aa2bb4982e575acd7583f01531f241af077b163"
uuid = "f27b6e38-b328-58d1-80ce-0feddd5e7a45"
version = "3.2.13"
weakdeps = ["ChainRulesCore", "MakieCore", "MutableArithmetics"]

    [deps.Polynomials.extensions]
    PolynomialsChainRulesCoreExt = "ChainRulesCore"
    PolynomialsMakieCoreExt = "MakieCore"
    PolynomialsMutableArithmeticsExt = "MutableArithmetics"

[[deps.PositiveFactorizations]]
deps = ["LinearAlgebra"]
git-tree-sha1 = "17275485f373e6673f7e7f97051f703ed5b15b20"
uuid = "85a6dd25-e78a-55b7-8502-1745935b8125"
version = "0.2.4"

[[deps.PrecompileTools]]
deps = ["Preferences"]
git-tree-sha1 = "2e47054ffe7d0a8872e977c0d09eb4b3d162ebde"
uuid = "aea7be01-6a6a-4083-8856-8a6e6704d82a"
version = "1.0.2"

[[deps.Preferences]]
deps = ["TOML"]
git-tree-sha1 = "47e5f437cc0e7ef2ce8406ce1e7e24d44915f88d"
uuid = "21216c6a-2e73-6563-6e65-726566657250"
version = "1.3.0"

[[deps.Primes]]
deps = ["IntegerMathUtils"]
git-tree-sha1 = "4c9f306e5d6603ae203c2000dd460d81a5251489"
uuid = "27ebfcd6-29c5-5fa9-bf4b-fb8fc14df3ae"
version = "0.5.4"

[[deps.Printf]]
deps = ["Unicode"]
uuid = "de0858da-6303-5e67-8744-51eddeeeb8d7"

[[deps.Profile]]
deps = ["Printf"]
uuid = "9abbd945-dff8-562f-b5e8-e1ebf5ef1b79"

[[deps.ProgressMeter]]
deps = ["Distributed", "Printf"]
git-tree-sha1 = "d7a7aef8f8f2d537104f170139553b14dfe39fe9"
uuid = "92933f4c-e287-5a05-a399-4b506db050ca"
version = "1.7.2"

[[deps.QOI]]
deps = ["ColorTypes", "FileIO", "FixedPointNumbers"]
git-tree-sha1 = "18e8f4d1426e965c7b532ddd260599e1510d26ce"
uuid = "4b34888f-f399-49d4-9bb3-47ed5cae4e65"
version = "1.0.0"

[[deps.Qt6Base_jll]]
deps = ["Artifacts", "CompilerSupportLibraries_jll", "Fontconfig_jll", "Glib_jll", "JLLWrappers", "Libdl", "Libglvnd_jll", "OpenSSL_jll", "Pkg", "Xorg_libXext_jll", "Xorg_libXrender_jll", "Xorg_libxcb_jll", "Xorg_xcb_util_image_jll", "Xorg_xcb_util_keysyms_jll", "Xorg_xcb_util_renderutil_jll", "Xorg_xcb_util_wm_jll", "Zlib_jll", "xkbcommon_jll"]
git-tree-sha1 = "364898e8f13f7eaaceec55fd3d08680498c0aa6e"
uuid = "c0090381-4147-56d7-9ebc-da0b1113ec56"
version = "6.4.2+3"

[[deps.QuadGK]]
deps = ["DataStructures", "LinearAlgebra"]
git-tree-sha1 = "6ec7ac8412e83d57e313393220879ede1740f9ee"
uuid = "1fd47b50-473d-5c70-9696-f719f8f3bcdc"
version = "2.8.2"

[[deps.REPL]]
deps = ["InteractiveUtils", "Markdown", "Sockets", "Unicode"]
uuid = "3fa0cd96-eef1-5676-8a61-b3b8758bbffb"

[[deps.Random]]
deps = ["SHA", "Serialization"]
uuid = "9a3f8284-a2c9-5f02-9a11-845980a1fd5c"

[[deps.RangeArrays]]
git-tree-sha1 = "b9039e93773ddcfc828f12aadf7115b4b4d225f5"
uuid = "b3c3ace0-ae52-54e7-9d0b-2c1406fd6b9d"
version = "0.3.2"

[[deps.Ratios]]
deps = ["Requires"]
git-tree-sha1 = "6d7bb727e76147ba18eed998700998e17b8e4911"
uuid = "c84ed2f1-dad5-54f0-aa8e-dbefe2724439"
version = "0.4.4"
weakdeps = ["FixedPointNumbers"]

    [deps.Ratios.extensions]
    RatiosFixedPointNumbersExt = "FixedPointNumbers"

[[deps.RecipesBase]]
deps = ["PrecompileTools"]
git-tree-sha1 = "5c3d09cc4f31f5fc6af001c250bf1278733100ff"
uuid = "3cdcf5f2-1ef4-517c-9805-6587b60abb01"
version = "1.3.4"

[[deps.RecipesPipeline]]
deps = ["Dates", "NaNMath", "PlotUtils", "PrecompileTools", "RecipesBase"]
git-tree-sha1 = "45cf9fd0ca5839d06ef333c8201714e888486342"
uuid = "01d81517-befc-4cb6-b9ec-a95719d0359c"
version = "0.6.12"

[[deps.Reexport]]
git-tree-sha1 = "45e428421666073eab6f2da5c9d310d99bb12f9b"
uuid = "189a3867-3050-52da-a836-e630ba90ab69"
version = "1.2.2"

[[deps.RelocatableFolders]]
deps = ["SHA", "Scratch"]
git-tree-sha1 = "90bc7a7c96410424509e4263e277e43250c05691"
uuid = "05181044-ff0b-4ac5-8273-598c1e38db00"
version = "1.0.0"

[[deps.Requires]]
deps = ["UUIDs"]
git-tree-sha1 = "838a3a4188e2ded87a4f9f184b4b0d78a1e91cb7"
uuid = "ae029012-a4dd-5104-9daa-d747884805df"
version = "1.3.0"

[[deps.RingLists]]
deps = ["Random"]
git-tree-sha1 = "9712ebc42e91850f35272b48eb840e60c0270ec0"
uuid = "286e9d63-9694-5540-9e3c-4e6708fa07b2"
version = "0.2.7"

[[deps.Rmath]]
deps = ["Random", "Rmath_jll"]
git-tree-sha1 = "f65dcb5fa46aee0cf9ed6274ccbd597adc49aa7b"
uuid = "79098fc4-a85e-5d69-aa6a-4863f24498fa"
version = "0.7.1"

[[deps.Rmath_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "6ed52fdd3382cf21947b15e8870ac0ddbff736da"
uuid = "f50d1b31-88e8-58de-be2c-1cc44531875f"
version = "0.4.0+0"

[[deps.RoundingEmulator]]
git-tree-sha1 = "40b9edad2e5287e05bd413a38f61a8ff55b9557b"
uuid = "5eaf0fd0-dfba-4ccb-bf02-d820a40db705"
version = "0.2.1"

[[deps.SHA]]
uuid = "ea8e919c-243c-51af-8825-aaa63cd721ce"
version = "0.7.0"

[[deps.SIMD]]
deps = ["PrecompileTools"]
git-tree-sha1 = "0e270732477b9e551d884e6b07e23bb2ec947790"
uuid = "fdea26ae-647d-5447-a871-4b548cad5224"
version = "3.4.5"

[[deps.ScanByte]]
deps = ["Libdl", "SIMD"]
git-tree-sha1 = "d49e35f413186528f1d7cc675e67d0ed16fd7800"
uuid = "7b38b023-a4d7-4c5e-8d43-3f3097f304eb"
version = "0.4.0"

[[deps.Scratch]]
deps = ["Dates"]
git-tree-sha1 = "30449ee12237627992a99d5e30ae63e4d78cd24a"
uuid = "6c6a2e73-6563-6170-7368-637461726353"
version = "1.2.0"

[[deps.Serialization]]
uuid = "9e88b42a-f829-5b0c-bbe9-9e923198166b"

[[deps.SetRounding]]
git-tree-sha1 = "d7a25e439d07a17b7cdf97eecee504c50fedf5f6"
uuid = "3cc68bcd-71a2-5612-b932-767ffbe40ab0"
version = "0.2.1"

[[deps.Setfield]]
deps = ["ConstructionBase", "Future", "MacroTools", "StaticArraysCore"]
git-tree-sha1 = "e2cc6d8c88613c05e1defb55170bf5ff211fbeac"
uuid = "efcf1570-3423-57d1-acb7-fd33fddbac46"
version = "1.1.1"

[[deps.ShaderAbstractions]]
deps = ["ColorTypes", "FixedPointNumbers", "GeometryBasics", "LinearAlgebra", "Observables", "StaticArrays", "StructArrays", "Tables"]
git-tree-sha1 = "0d15c3e7b2003f4451714f08ffec2b77badc2dc4"
uuid = "65257c39-d410-5151-9873-9b3e5be5013e"
version = "0.3.0"

[[deps.SharedArrays]]
deps = ["Distributed", "Mmap", "Random", "Serialization"]
uuid = "1a1011a3-84de-559e-8e89-a11a2f7dc383"

[[deps.Showoff]]
deps = ["Dates", "Grisu"]
git-tree-sha1 = "91eddf657aca81df9ae6ceb20b959ae5653ad1de"
uuid = "992d4aef-0814-514b-bc4d-f2e9a6c4116f"
version = "1.0.3"

[[deps.SignedDistanceFields]]
deps = ["Random", "Statistics", "Test"]
git-tree-sha1 = "d263a08ec505853a5ff1c1ebde2070419e3f28e9"
uuid = "73760f76-fbc4-59ce-8f25-708e95d2df96"
version = "0.4.0"

[[deps.SimpleBufferStream]]
git-tree-sha1 = "874e8867b33a00e784c8a7e4b60afe9e037b74e1"
uuid = "777ac1f9-54b0-4bf8-805c-2214025038e7"
version = "1.1.0"

[[deps.SimpleGraphs]]
deps = ["AbstractLattices", "Combinatorics", "DataStructures", "IterTools", "LightXML", "LinearAlgebra", "LinearAlgebraX", "Optim", "Primes", "Random", "RingLists", "SimplePartitions", "SimplePolynomials", "SimpleRandom", "SparseArrays", "Statistics"]
git-tree-sha1 = "b608903049d11cc557c45e03b3a53e9260579c19"
uuid = "55797a34-41de-5266-9ec1-32ac4eb504d3"
version = "0.8.4"

[[deps.SimplePartitions]]
deps = ["AbstractLattices", "DataStructures", "Permutations"]
git-tree-sha1 = "dcc02923a53f316ab97da8ef3136e80b4543dbf1"
uuid = "ec83eff0-a5b5-5643-ae32-5cbf6eedec9d"
version = "0.3.0"

[[deps.SimplePolynomials]]
deps = ["Mods", "Multisets", "Polynomials", "Primes"]
git-tree-sha1 = "d073c45302132b324ca653e1053966b4beacc2a5"
uuid = "cc47b68c-3164-5771-a705-2bc0097375a0"
version = "0.2.11"

[[deps.SimpleRandom]]
deps = ["Distributions", "LinearAlgebra", "Random"]
git-tree-sha1 = "3a6fb395e37afab81aeea85bae48a4db5cd7244a"
uuid = "a6525b86-64cd-54fa-8f65-62fc48bdc0e8"
version = "0.3.1"

[[deps.SimpleTraits]]
deps = ["InteractiveUtils", "MacroTools"]
git-tree-sha1 = "5d7e3f4e11935503d3ecaf7186eac40602e7d231"
uuid = "699a6c99-e7fa-54fc-8d76-47d257e15c1d"
version = "0.9.4"

[[deps.Sixel]]
deps = ["Dates", "FileIO", "ImageCore", "IndirectArrays", "OffsetArrays", "REPL", "libsixel_jll"]
git-tree-sha1 = "2da10356e31327c7096832eb9cd86307a50b1eb6"
uuid = "45858cf5-a6b0-47a3-bbea-62219f50df47"
version = "0.1.3"

[[deps.SnoopPrecompile]]
deps = ["Preferences"]
git-tree-sha1 = "e760a70afdcd461cf01a575947738d359234665c"
uuid = "66db9d55-30c0-4569-8b51-7e840670fc0c"
version = "1.0.3"

[[deps.Sockets]]
uuid = "6462fe0b-24de-5631-8697-dd941f90decc"

[[deps.SortingAlgorithms]]
deps = ["DataStructures"]
git-tree-sha1 = "a4ada03f999bd01b3a25dcaa30b2d929fe537e00"
uuid = "a2af1166-a08f-5f64-846c-94a0d3cef48c"
version = "1.1.0"

[[deps.SparseArrays]]
deps = ["Libdl", "LinearAlgebra", "Random", "Serialization", "SuiteSparse_jll"]
uuid = "2f01184e-e22b-5df5-ae63-d93ebab69eaf"

[[deps.SpecialFunctions]]
deps = ["IrrationalConstants", "LogExpFunctions", "OpenLibm_jll", "OpenSpecFun_jll"]
git-tree-sha1 = "ef28127915f4229c971eb43f3fc075dd3fe91880"
uuid = "276daf66-3868-5448-9aa4-cd146d93841b"
version = "2.2.0"
weakdeps = ["ChainRulesCore"]

    [deps.SpecialFunctions.extensions]
    SpecialFunctionsChainRulesCoreExt = "ChainRulesCore"

[[deps.StableHashTraits]]
deps = ["CRC32c", "Compat", "Dates", "SHA", "Tables", "TupleTools", "UUIDs"]
git-tree-sha1 = "0b8b801b8f03a329a4e86b44c5e8a7d7f4fe10a3"
uuid = "c5dd0088-6c3f-4803-b00e-f31a60c170fa"
version = "0.3.1"

[[deps.StackViews]]
deps = ["OffsetArrays"]
git-tree-sha1 = "46e589465204cd0c08b4bd97385e4fa79a0c770c"
uuid = "cae243ae-269e-4f55-b966-ac2d0dc13c15"
version = "0.1.1"

[[deps.StaticArrays]]
deps = ["LinearAlgebra", "Random", "StaticArraysCore", "Statistics"]
git-tree-sha1 = "c262c8e978048c2b095be1672c9bee55b4619521"
uuid = "90137ffa-7385-5640-81b9-e52037218182"
version = "1.5.24"

[[deps.StaticArraysCore]]
git-tree-sha1 = "6b7ba252635a5eff6a0b0664a41ee140a1c9e72a"
uuid = "1e83bf80-4336-4d27-bf5d-d5a4f845583c"
version = "1.4.0"

[[deps.Statistics]]
deps = ["LinearAlgebra", "SparseArrays"]
uuid = "10745b16-79ce-11e8-11f9-7d13ad32a3b2"
version = "1.9.0"

[[deps.StatsAPI]]
deps = ["LinearAlgebra"]
git-tree-sha1 = "45a7769a04a3cf80da1c1c7c60caf932e6f4c9f7"
uuid = "82ae8749-77ed-4fe6-ae5f-f523153014b0"
version = "1.6.0"

[[deps.StatsBase]]
deps = ["DataAPI", "DataStructures", "LinearAlgebra", "LogExpFunctions", "Missings", "Printf", "Random", "SortingAlgorithms", "SparseArrays", "Statistics", "StatsAPI"]
git-tree-sha1 = "d1bf48bfcc554a3761a133fe3a9bb01488e06916"
uuid = "2913bbd2-ae8a-5f71-8c99-4fb6c76f3a91"
version = "0.33.21"

[[deps.StatsFuns]]
deps = ["HypergeometricFunctions", "IrrationalConstants", "LogExpFunctions", "Reexport", "Rmath", "SpecialFunctions"]
git-tree-sha1 = "f625d686d5a88bcd2b15cd81f18f98186fdc0c9a"
uuid = "4c63d2b9-4356-54db-8cca-17b64c39e42c"
version = "1.3.0"

    [deps.StatsFuns.extensions]
    StatsFunsChainRulesCoreExt = "ChainRulesCore"
    StatsFunsInverseFunctionsExt = "InverseFunctions"

    [deps.StatsFuns.weakdeps]
    ChainRulesCore = "d360d2e6-b24c-11e9-a2a3-2a2ae2dbcce4"
    InverseFunctions = "3587e190-3f89-42d0-90ee-14403ec27112"

[[deps.StructArrays]]
deps = ["Adapt", "DataAPI", "GPUArraysCore", "StaticArraysCore", "Tables"]
git-tree-sha1 = "521a0e828e98bb69042fec1809c1b5a680eb7389"
uuid = "09ab397b-f2b6-538f-b94a-2f83cf4a842a"
version = "0.6.15"

[[deps.SuiteSparse]]
deps = ["Libdl", "LinearAlgebra", "Serialization", "SparseArrays"]
uuid = "4607b0f0-06f3-5cda-b6b1-a6196a1729e9"

[[deps.SuiteSparse_jll]]
deps = ["Artifacts", "Libdl", "Pkg", "libblastrampoline_jll"]
uuid = "bea87d4a-7f5b-5778-9afe-8cc45184846c"
version = "5.10.1+6"

[[deps.TOML]]
deps = ["Dates"]
uuid = "fa267f1f-6049-4f14-aa54-33bafae1ed76"
version = "1.0.3"

[[deps.TableTraits]]
deps = ["IteratorInterfaceExtensions"]
git-tree-sha1 = "c06b2f539df1c6efa794486abfb6ed2022561a39"
uuid = "3783bdb8-4a98-5b6b-af9a-565f29a5fe9c"
version = "1.0.1"

[[deps.Tables]]
deps = ["DataAPI", "DataValueInterfaces", "IteratorInterfaceExtensions", "LinearAlgebra", "OrderedCollections", "TableTraits", "Test"]
git-tree-sha1 = "1544b926975372da01227b382066ab70e574a3ec"
uuid = "bd369af6-aec1-5ad0-b16a-f7cc5008161c"
version = "1.10.1"

[[deps.Tar]]
deps = ["ArgTools", "SHA"]
uuid = "a4e569a6-e804-4fa4-b0f3-eef7a1d5b13e"
version = "1.10.0"

[[deps.TensorCore]]
deps = ["LinearAlgebra"]
git-tree-sha1 = "1feb45f88d133a655e001435632f019a9a1bcdb6"
uuid = "62fd8b95-f654-4bbd-a8a5-9c27f68ccd50"
version = "0.1.1"

[[deps.Test]]
deps = ["InteractiveUtils", "Logging", "Random", "Serialization"]
uuid = "8dfed614-e22c-5e08-85e1-65c5234f0b40"

[[deps.TiffImages]]
deps = ["ColorTypes", "DataStructures", "DocStringExtensions", "FileIO", "FixedPointNumbers", "IndirectArrays", "Inflate", "Mmap", "OffsetArrays", "PkgVersion", "ProgressMeter", "UUIDs"]
git-tree-sha1 = "8621f5c499a8aa4aa970b1ae381aae0ef1576966"
uuid = "731e570b-9d59-4bfa-96dc-6df516fadf69"
version = "0.6.4"

[[deps.TranscodingStreams]]
deps = ["Random", "Test"]
git-tree-sha1 = "9a6ae7ed916312b41236fcef7e0af564ef934769"
uuid = "3bb67fe8-82b1-5028-8e26-92a6c54297fa"
version = "0.9.13"

[[deps.Tricks]]
git-tree-sha1 = "aadb748be58b492045b4f56166b5188aa63ce549"
uuid = "410a4b4d-49e4-4fbc-ab6d-cb71b17b3775"
version = "0.1.7"

[[deps.TriplotBase]]
git-tree-sha1 = "4d4ed7f294cda19382ff7de4c137d24d16adc89b"
uuid = "981d1d27-644d-49a2-9326-4793e63143c3"
version = "0.1.0"

[[deps.TupleTools]]
git-tree-sha1 = "3c712976c47707ff893cf6ba4354aa14db1d8938"
uuid = "9d95972d-f1c8-5527-a6e0-b4b365fa01f6"
version = "1.3.0"

[[deps.URIs]]
git-tree-sha1 = "074f993b0ca030848b897beff716d93aca60f06a"
uuid = "5c2747f8-b7ea-4ff2-ba2e-563bfd36b1d4"
version = "1.4.2"

[[deps.UUIDs]]
deps = ["Random", "SHA"]
uuid = "cf7118a7-6976-5b1a-9a39-7adc72f591a4"

[[deps.UnPack]]
git-tree-sha1 = "387c1f73762231e86e0c9c5443ce3b4a0a9a0c2b"
uuid = "3a884ed6-31ef-47d7-9d2a-63182c4928ed"
version = "1.0.2"

[[deps.Unicode]]
uuid = "4ec0a83e-493e-50e2-b9ac-8f72acf5a8f5"

[[deps.UnicodeFun]]
deps = ["REPL"]
git-tree-sha1 = "53915e50200959667e78a92a418594b428dffddf"
uuid = "1cfade01-22cf-5700-b092-accc4b62d6e1"
version = "0.4.1"

[[deps.Unitful]]
deps = ["Dates", "LinearAlgebra", "Random"]
git-tree-sha1 = "c4d2a349259c8eba66a00a540d550f122a3ab228"
uuid = "1986cc42-f94f-5a68-af5c-568840ba703d"
version = "1.15.0"

    [deps.Unitful.extensions]
    ConstructionBaseUnitfulExt = "ConstructionBase"
    InverseFunctionsUnitfulExt = "InverseFunctions"

    [deps.Unitful.weakdeps]
    ConstructionBase = "187b0558-2788-49d3-abe0-74a17ed4e7c9"
    InverseFunctions = "3587e190-3f89-42d0-90ee-14403ec27112"

[[deps.UnitfulLatexify]]
deps = ["LaTeXStrings", "Latexify", "Unitful"]
git-tree-sha1 = "e2d817cc500e960fdbafcf988ac8436ba3208bfd"
uuid = "45397f5d-5981-4c77-b2b3-fc36d6e9b728"
version = "1.6.3"

[[deps.Unzip]]
git-tree-sha1 = "ca0969166a028236229f63514992fc073799bb78"
uuid = "41fe7b60-77ed-43a1-b4f0-825fd5a5650d"
version = "0.2.0"

[[deps.Wayland_jll]]
deps = ["Artifacts", "Expat_jll", "JLLWrappers", "Libdl", "Libffi_jll", "Pkg", "XML2_jll"]
git-tree-sha1 = "ed8d92d9774b077c53e1da50fd81a36af3744c1c"
uuid = "a2964d1f-97da-50d4-b82a-358c7fce9d89"
version = "1.21.0+0"

[[deps.Wayland_protocols_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "4528479aa01ee1b3b4cd0e6faef0e04cf16466da"
uuid = "2381bf8a-dfd0-557d-9999-79630e7b1b91"
version = "1.25.0+0"

[[deps.WoodburyMatrices]]
deps = ["LinearAlgebra", "SparseArrays"]
git-tree-sha1 = "de67fa59e33ad156a590055375a30b23c40299d3"
uuid = "efce3f68-66dc-5838-9240-27a6d6f5f9b6"
version = "0.5.5"

[[deps.XML2_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Libiconv_jll", "Pkg", "Zlib_jll"]
git-tree-sha1 = "93c41695bc1c08c46c5899f4fe06d6ead504bb73"
uuid = "02c8fc9c-b97f-50b9-bbe4-9be30ff0a78a"
version = "2.10.3+0"

[[deps.XSLT_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Libgcrypt_jll", "Libgpg_error_jll", "Libiconv_jll", "Pkg", "XML2_jll", "Zlib_jll"]
git-tree-sha1 = "91844873c4085240b95e795f692c4cec4d805f8a"
uuid = "aed1982a-8fda-507f-9586-7b0439959a61"
version = "1.1.34+0"

[[deps.XZ_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl"]
git-tree-sha1 = "2222b751598bd9f4885c9ce9cd23e83404baa8ce"
uuid = "ffd25f8a-64ca-5728-b0f7-c24cf3aae800"
version = "5.4.3+1"

[[deps.Xorg_libX11_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg", "Xorg_libxcb_jll", "Xorg_xtrans_jll"]
git-tree-sha1 = "5be649d550f3f4b95308bf0183b82e2582876527"
uuid = "4f6342f7-b3d2-589e-9d20-edeb45f2b2bc"
version = "1.6.9+4"

[[deps.Xorg_libXau_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "4e490d5c960c314f33885790ed410ff3a94ce67e"
uuid = "0c0b7dd1-d40b-584c-a123-a41640f87eec"
version = "1.0.9+4"

[[deps.Xorg_libXcursor_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg", "Xorg_libXfixes_jll", "Xorg_libXrender_jll"]
git-tree-sha1 = "12e0eb3bc634fa2080c1c37fccf56f7c22989afd"
uuid = "935fb764-8cf2-53bf-bb30-45bb1f8bf724"
version = "1.2.0+4"

[[deps.Xorg_libXdmcp_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "4fe47bd2247248125c428978740e18a681372dd4"
uuid = "a3789734-cfe1-5b06-b2d0-1dd0d9d62d05"
version = "1.1.3+4"

[[deps.Xorg_libXext_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg", "Xorg_libX11_jll"]
git-tree-sha1 = "b7c0aa8c376b31e4852b360222848637f481f8c3"
uuid = "1082639a-0dae-5f34-9b06-72781eeb8cb3"
version = "1.3.4+4"

[[deps.Xorg_libXfixes_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg", "Xorg_libX11_jll"]
git-tree-sha1 = "0e0dc7431e7a0587559f9294aeec269471c991a4"
uuid = "d091e8ba-531a-589c-9de9-94069b037ed8"
version = "5.0.3+4"

[[deps.Xorg_libXi_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg", "Xorg_libXext_jll", "Xorg_libXfixes_jll"]
git-tree-sha1 = "89b52bc2160aadc84d707093930ef0bffa641246"
uuid = "a51aa0fd-4e3c-5386-b890-e753decda492"
version = "1.7.10+4"

[[deps.Xorg_libXinerama_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg", "Xorg_libXext_jll"]
git-tree-sha1 = "26be8b1c342929259317d8b9f7b53bf2bb73b123"
uuid = "d1454406-59df-5ea1-beac-c340f2130bc3"
version = "1.1.4+4"

[[deps.Xorg_libXrandr_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg", "Xorg_libXext_jll", "Xorg_libXrender_jll"]
git-tree-sha1 = "34cea83cb726fb58f325887bf0612c6b3fb17631"
uuid = "ec84b674-ba8e-5d96-8ba1-2a689ba10484"
version = "1.5.2+4"

[[deps.Xorg_libXrender_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg", "Xorg_libX11_jll"]
git-tree-sha1 = "19560f30fd49f4d4efbe7002a1037f8c43d43b96"
uuid = "ea2f1a96-1ddc-540d-b46f-429655e07cfa"
version = "0.9.10+4"

[[deps.Xorg_libpthread_stubs_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "6783737e45d3c59a4a4c4091f5f88cdcf0908cbb"
uuid = "14d82f49-176c-5ed1-bb49-ad3f5cbd8c74"
version = "0.1.0+3"

[[deps.Xorg_libxcb_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg", "XSLT_jll", "Xorg_libXau_jll", "Xorg_libXdmcp_jll", "Xorg_libpthread_stubs_jll"]
git-tree-sha1 = "daf17f441228e7a3833846cd048892861cff16d6"
uuid = "c7cfdc94-dc32-55de-ac96-5a1b8d977c5b"
version = "1.13.0+3"

[[deps.Xorg_libxkbfile_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Xorg_libX11_jll"]
git-tree-sha1 = "730eeca102434283c50ccf7d1ecdadf521a765a4"
uuid = "cc61e674-0454-545c-8b26-ed2c68acab7a"
version = "1.1.2+0"

[[deps.Xorg_xcb_util_image_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg", "Xorg_xcb_util_jll"]
git-tree-sha1 = "0fab0a40349ba1cba2c1da699243396ff8e94b97"
uuid = "12413925-8142-5f55-bb0e-6d7ca50bb09b"
version = "0.4.0+1"

[[deps.Xorg_xcb_util_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg", "Xorg_libxcb_jll"]
git-tree-sha1 = "e7fd7b2881fa2eaa72717420894d3938177862d1"
uuid = "2def613f-5ad1-5310-b15b-b15d46f528f5"
version = "0.4.0+1"

[[deps.Xorg_xcb_util_keysyms_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg", "Xorg_xcb_util_jll"]
git-tree-sha1 = "d1151e2c45a544f32441a567d1690e701ec89b00"
uuid = "975044d2-76e6-5fbe-bf08-97ce7c6574c7"
version = "0.4.0+1"

[[deps.Xorg_xcb_util_renderutil_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg", "Xorg_xcb_util_jll"]
git-tree-sha1 = "dfd7a8f38d4613b6a575253b3174dd991ca6183e"
uuid = "0d47668e-0667-5a69-a72c-f761630bfb7e"
version = "0.3.9+1"

[[deps.Xorg_xcb_util_wm_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg", "Xorg_xcb_util_jll"]
git-tree-sha1 = "e78d10aab01a4a154142c5006ed44fd9e8e31b67"
uuid = "c22f9ab0-d5fe-5066-847c-f4bb1cd4e361"
version = "0.4.1+1"

[[deps.Xorg_xkbcomp_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Xorg_libxkbfile_jll"]
git-tree-sha1 = "330f955bc41bb8f5270a369c473fc4a5a4e4d3cb"
uuid = "35661453-b289-5fab-8a00-3d9160c6a3a4"
version = "1.4.6+0"

[[deps.Xorg_xkeyboard_config_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Xorg_xkbcomp_jll"]
git-tree-sha1 = "691634e5453ad362044e2ad653e79f3ee3bb98c3"
uuid = "33bec58e-1273-512f-9401-5d533626f822"
version = "2.39.0+0"

[[deps.Xorg_xtrans_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "79c31e7844f6ecf779705fbc12146eb190b7d845"
uuid = "c5fb5394-a638-5e4d-96e5-b29de1b5cf10"
version = "1.4.0+3"

[[deps.Zlib_jll]]
deps = ["Libdl"]
uuid = "83775a58-1f1d-513f-b197-d71354ab007a"
version = "1.2.13+0"

[[deps.Zstd_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl"]
git-tree-sha1 = "49ce682769cd5de6c72dcf1b94ed7790cd08974c"
uuid = "3161d3a3-bdf6-5164-811a-617609db77b4"
version = "1.5.5+0"

[[deps.fzf_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "868e669ccb12ba16eaf50cb2957ee2ff61261c56"
uuid = "214eeab7-80f7-51ab-84ad-2988db7cef09"
version = "0.29.0+0"

[[deps.isoband_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "51b5eeb3f98367157a7a12a1fb0aa5328946c03c"
uuid = "9a68df92-36a6-505f-a73e-abb412b6bfb4"
version = "0.2.3+0"

[[deps.libaom_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "3a2ea60308f0996d26f1e5354e10c24e9ef905d4"
uuid = "a4ae2306-e953-59d6-aa16-d00cac43593b"
version = "3.4.0+0"

[[deps.libass_jll]]
deps = ["Artifacts", "Bzip2_jll", "FreeType2_jll", "FriBidi_jll", "HarfBuzz_jll", "JLLWrappers", "Libdl", "Pkg", "Zlib_jll"]
git-tree-sha1 = "5982a94fcba20f02f42ace44b9894ee2b140fe47"
uuid = "0ac62f75-1d6f-5e53-bd7c-93b484bb37c0"
version = "0.15.1+0"

[[deps.libblastrampoline_jll]]
deps = ["Artifacts", "Libdl"]
uuid = "8e850b90-86db-534c-a0d3-1478176c7d93"
version = "5.8.0+0"

[[deps.libfdk_aac_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "daacc84a041563f965be61859a36e17c4e4fcd55"
uuid = "f638f0a6-7fb0-5443-88ba-1cc74229b280"
version = "2.0.2+0"

[[deps.libpng_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg", "Zlib_jll"]
git-tree-sha1 = "94d180a6d2b5e55e447e2d27a29ed04fe79eb30c"
uuid = "b53b4c65-9356-5827-b1ea-8c7a1a84506f"
version = "1.6.38+0"

[[deps.libsixel_jll]]
deps = ["Artifacts", "JLLWrappers", "JpegTurbo_jll", "Libdl", "Pkg", "libpng_jll"]
git-tree-sha1 = "d4f63314c8aa1e48cd22aa0c17ed76cd1ae48c3c"
uuid = "075b6546-f08a-558a-be8f-8157d0f608a5"
version = "1.10.3+0"

[[deps.libvorbis_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Ogg_jll", "Pkg"]
git-tree-sha1 = "b910cb81ef3fe6e78bf6acee440bda86fd6ae00c"
uuid = "f27f6e37-5d2b-51aa-960f-b287f2bc3b7a"
version = "1.3.7+1"

[[deps.nghttp2_jll]]
deps = ["Artifacts", "Libdl"]
uuid = "8e850ede-7688-5339-a07c-302acd2aaf8d"
version = "1.48.0+0"

[[deps.p7zip_jll]]
deps = ["Artifacts", "Libdl"]
uuid = "3f19e933-33d8-53b3-aaab-bd5110c3b7a0"
version = "17.4.0+0"

[[deps.x264_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "4fea590b89e6ec504593146bf8b988b2c00922b2"
uuid = "1270edf5-f2f9-52d2-97e9-ab00b5d0237a"
version = "2021.5.5+0"

[[deps.x265_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg"]
git-tree-sha1 = "ee567a171cce03570d77ad3a43e90218e38937a9"
uuid = "dfaa095f-4041-5dcd-9319-2fabd8486b76"
version = "3.5.0+0"

[[deps.xkbcommon_jll]]
deps = ["Artifacts", "JLLWrappers", "Libdl", "Pkg", "Wayland_jll", "Wayland_protocols_jll", "Xorg_libxcb_jll", "Xorg_xkeyboard_config_jll"]
git-tree-sha1 = "9ebfc140cc56e8c2156a15ceac2f0302e327ac0a"
uuid = "d8fb68d0-12a3-5cfd-a85a-d49703b185fd"
version = "1.4.1+0"
"""

# ╔═╡ Cell order:
# ╟─5e232da0-3d47-4e2c-9499-ea8e09f337fb
# ╟─295638ba-a435-42db-aa5a-838a47d594ab
# ╠═1c0b6789-7dcb-4005-8adc-e1a4a275629d
# ╟─e7d3ed3d-6eeb-4783-a0d4-864dd258588a
# ╠═52e6d1e7-064a-4cea-940d-31626ba11444
# ╟─481ffec9-8a37-4d49-b18b-a73f1a9f20ce
# ╠═b00a1e34-dc4d-47e7-a364-ea68f9a3e8ca
# ╟─42bbc7bb-2619-4e2f-8feb-b6db95725a1f
# ╠═d9e6f3d2-b56d-4587-8324-385d11d732fe
# ╟─6920938e-35c1-4ad6-afdc-7074b6c14864
# ╟─5f52b01e-243a-475a-9583-afc7bc31bd60
# ╠═37decd55-6f2b-4344-a20c-a893227c0f13
# ╟─4bc35f6c-c01b-46be-834b-e00c050cfb2a
# ╠═554b1c89-d99b-4da3-a2b0-485e7f907b9f
# ╟─3c3da943-5661-4fa3-a3f0-dbd90ed63a1f
# ╠═81de4891-4cc5-4711-91c3-5fbd7253ee18
# ╟─0fe503e3-1209-439b-98ab-8aa3ec9e8ec3
# ╠═4e0dc9a3-6e73-4c6b-9337-29fd0504f4a0
# ╟─9981bbc9-8853-42db-95af-2b6b4573e563
# ╠═c8542af2-5580-4216-acf1-b411352b30e4
# ╠═ecf0379f-d0f4-471c-8d9a-5a0caf6e7c0d
# ╟─335a3b2f-b203-47d9-9424-eb3d7e721034
# ╠═7239c4f3-554a-40aa-b8f3-a61089ab0343
# ╠═19ecd9aa-7a18-47a9-bbab-905e4b605298
# ╟─a020300f-054f-40f2-bbc0-f2519bcb5aac
# ╠═76c842d6-18ab-47c6-8c3d-9b0ac302c755
# ╟─5f3aa8cb-f05b-4e99-a3c2-17b935fdba32
# ╠═109f33e8-bc1c-4b07-b17a-e3e71224195f
# ╟─46b9e722-b97c-41a9-b8ed-3d9342bbbafe
# ╠═e78147a2-25b1-4a99-93d8-e911a750767b
# ╟─8c4234ce-c204-4931-a355-bc73e91c6823
# ╠═a7a06841-d2b3-4265-8549-44b3a08e5302
# ╟─d469fdc5-7eb2-494c-bfb7-a9ee3087106b
# ╠═439f0d7f-69f5-4252-826d-f143a2196564
# ╟─7782fffd-0699-410d-bf59-0fdc2046a1cf
# ╠═ca1a1e92-e576-4938-a914-08abb1ed8ebe
# ╟─083ec2ad-4409-4522-97b9-5c34bda0c7a6
# ╠═30e842dc-5531-45c2-b19d-87cc809d9daf
# ╠═7aeabc41-fbc3-4dac-b2b1-bea71ae1b7da
# ╠═1e30ab88-74e4-46cc-929b-5b9ba37104cf
# ╟─8604a238-25d4-466f-ba58-dbdd2fe657c5
# ╠═3699204b-7ae6-4af5-afa8-f7501e5d8451
# ╟─30bc37f0-7bd8-4b23-a747-3ff348377a33
# ╠═0d0459f6-f921-4d4d-ac7c-fb121b9b4058
# ╠═9aa9375b-0047-44ff-b8c7-7f686429b9a1
# ╟─64342e14-0fa3-4967-92d5-ea093e5a2000
# ╠═d0282bb1-0527-4de8-9a26-6c61d7075b56
# ╟─2b97b515-2aba-40a6-a16b-27c2d0411d86
# ╠═6a6c3e7c-c61e-429a-a00a-b8c121ff313e
# ╟─fad612c2-c63e-4114-9b77-28c0e8858848
# ╠═566bb40d-1527-4796-9d49-cd7ce7aa8c93
# ╟─dcaf893d-51fa-4a58-8eff-7b2e8e952d0b
# ╟─bd549b0d-0266-404d-9f4b-592120957aa5
# ╠═6c67f721-9d8b-42df-aecc-93ab5307e2d7
# ╠═a7437e1e-86ae-4049-b54e-d4bed317a3df
# ╟─ec032c49-0f42-4367-b4ea-04c147b86374
# ╠═e5423ff9-a1d1-4b6d-ade4-e5926f56d2b0
# ╠═32c4dc42-6ab6-40c4-ba3f-f27d049fc2c4
# ╟─746aacbb-1462-455a-9b6e-686469685674
# ╠═f451b75f-220f-4ccf-b67a-d336bcb09a7e
# ╠═757a3ba9-9900-4783-b81c-84649a0dd721
# ╠═df4186f1-a2d5-4fde-8561-cb45c7da44d7
# ╠═69960128-6005-46f2-a472-b00ab0d6abe7
# ╠═0df007a2-7553-43a6-991f-815704a29985
# ╠═08d2ba43-fd3c-481e-b18b-f100bccd033e
# ╠═1788b455-4444-4a7e-b830-a439dc9fba6a
# ╟─d460c908-d7eb-49b4-8924-44bab234cd43
# ╠═5c46bd5b-ce78-430e-8ced-7e579fd6c831
# ╠═7d7c03f0-bc9e-4272-8b36-730aea4f1f4d
# ╠═b8d98eb6-7c33-429d-8f16-127df3b9295a
# ╠═1547e812-f21b-4078-80f7-2bd51aa55f36
# ╠═9f9a9106-93e2-466a-bd84-007ae0f1f968
# ╠═fa58d471-5e56-4e9e-9c44-d0d22ac4e188
# ╠═bcf35e8f-a58e-45fb-9fe8-45e06ab76962
# ╠═19e1a879-f5d9-48cc-8de6-5d8a4cbe7e66
# ╠═97e74c33-ce44-4582-bf78-b148ef938f2d
# ╠═e8a774be-b3e6-4895-be4e-d1eb17770925
# ╟─38eeeab0-7390-4ecb-8649-a215db54bdf9
# ╟─d5e8a30e-7c02-4488-9b76-c433bfc47af3
# ╠═af24a85b-10dc-4191-9f9c-1feb5b087c9b
# ╠═ab37b446-9ae2-43f2-8ad2-23c955bef5e2
# ╠═22c87b83-e604-47cf-9cc5-c62bb596dad0
# ╟─ac26115c-994c-4d26-8cd3-1d0173ff0963
# ╟─d60401e4-68c1-46eb-a058-198bc07cc038
# ╠═2595d95d-e078-4797-89f0-a5fea224958d
# ╟─a671e43e-b047-40be-aa86-033cb2d9f189
# ╠═acecd610-61b1-4a9d-b25c-7621cf1118aa
# ╟─d3d284f6-bd4c-409a-b7df-6273cc80205d
# ╠═521ce74b-50b7-486b-9ffe-c5af10eeacea
# ╠═a3f1a607-2a83-4fcf-b82d-d5ed77a278ba
# ╠═a9838ecf-a01a-43ea-a954-c17449d8217e
# ╠═a030d112-051c-483d-8363-82447c965e28
# ╟─4a6b124f-ab81-4703-b281-87e76a224406
# ╠═1b0808e4-5183-419d-a0d2-cc47bf6f91d2
# ╟─2a61b7ea-0030-4df5-98c4-9184b44c3768
# ╠═82272fb8-ffe1-4842-b969-c4528ae80aaa
# ╠═1189bc98-6e15-4a71-92b2-1fc2e9be1657
# ╠═7e817f5c-dcce-4c83-8447-e2387cc270e3
# ╠═8761ec2b-a55a-4306-bffa-207653f1236e
# ╠═3bf34379-4cfc-4821-a86b-3585ada6d032
# ╠═e7d21766-9690-4ede-9eca-fdb1af86f246
# ╠═31584ad2-69ee-4e51-a953-7b6ed0f6e669
# ╟─4d1cc7d4-95c3-466a-9d0d-234031ca7782
# ╠═afe11549-6acc-42c7-a7f4-f0e1d7cd1692
# ╠═7423ca4f-cc69-4979-8d7f-706a41c2e283
# ╠═13a5455e-57e4-4189-ba03-afaa20da4182
# ╠═99405ef9-7d99-401f-ab77-45846a5c6259
# ╠═fd93a667-1e96-47f2-b648-8342cc1b1cc2
# ╠═214b88e7-6d5b-4cda-b631-e10d356cefc9
# ╠═f6eeb61f-de47-4b9f-9906-84045543690e
# ╠═031cba54-13fb-4aae-8de8-a7fd2fdacaa3
# ╟─00000000-0000-0000-0000-000000000001
# ╟─00000000-0000-0000-0000-000000000002
