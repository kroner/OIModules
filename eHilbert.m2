needsPackage "EquivariantGB"

-- Minimal standard form word representation of monomail m.
-- Outputs a list of integers, where 0 is the shift operator and 1,...,k are variable orbits.
word = m -> (
    M := exponentMatrix m;
    Mlist := entries transpose M;
    w := flatten for row in Mlist list (flatten toList apply(#row, i->toList(row#i:i+1)))|{0};
    p := position(w, l->(l!=0), Reverse=>true);
    take(w,p+1)
    )

-- New automaton with states indexed by snames, alphabet S, i the intial state and A the set of (terminal) reject states.
newAutomaton = (snames,S,i,A) -> (
    sts := hashTable toList apply(snames, s->(s => new MutableList from toList (#S:s)));
    new HashTable from {alphabet => S, states => sts, initial => i, rejects => A}
    )

-- Automaton that rejects all standard form words of monomials that are
-- Inc-multiples of the monomial corresponding to w.
wordAutomaton = (w,S) -> (
    A := newAutomaton((0..#w),S,0,{#w});
    lastrho := 0;
    for i from 0 to #w-1 do (
	A.states#i#(w#i) = i+1;
	if w#i == 0 then lastrho = i+1
	else A.states#i#0 = lastrho;
	);
    A
    )

-- Automaton on alphabet S that rejects words not in standard form.
-- (A word is in standard form if it does not contain subword s_js_i for j > i > 0,
-- with S = {s_0,s_1,...,s_k}.)
commAutomaton = S -> (
    A := newAutomaton((0..#S-1),S,0,{#S-1});
    for i from 0 to #S-2 do (
	A.states#i#0 = 0;
	for l from 0 to #S-2 do
	    A.states#i#(l+1) = if l < i then #S-1 else l;
	);
    A
    )

-- automaton that rejects if either A or B would reject.  All reject states are combined to one terminal reject state.
productAutomaton = (A,B) -> (
    S := A.alphabet;
    As := select(keys A.states, s->not member(s,A.rejects));
    Bs := select(keys B.states, s->not member(s,B.rejects));
    Cs := flatten for s in As list for t in Bs list (s,t);
    C := newAutomaton(Cs|{0},S,(A.initial,B.initial),{0});
    for s in As do for t in Bs do (
	for l from 0 to #S-1 do (
	    Cls := (A.states#s#l, B.states#t#l);
	    if member(Cls#0,A.rejects) or member(Cls#1,B.rejects) then Cls = 0;
	    C.states#(s,t)#l = Cls;
	    );
	);
    C
    )

-- transition matrix of automaton A for letter l
transitionMatrix = (A,l) -> (
    As := keys A.states;
    M := new MutableMatrix from map(T^(#As),T^(#As),0);
    for i from 0 to #As-1 do (
	j := position(As, k->A.states#(As#i)#l === k);
	M_(j,i) = 1;
	);
    new Matrix from M
    )

-- characteristic column vector of the initial state.
initVect = A -> transpose matrix {toList apply(keys A.states, s->if s===A.initial then 1 else 0)}
-- characteristic row vector of the accept states.
nonRejectVect = A -> matrix {toList apply(keys A.states, s->if member(s,A.rejects) then 0 else 1)}

-- Inputs:
--  F - a list of monomial generators, or Groebner basis
-- Output:
--  automaton A that rejects all words in the ideal of F or not in standard form
idealAutomaton = F -> (
    k := numrows exponentMatrix first F;
    rho := symbol rho;
    S' := toList (0..k);
    Afs := apply(F, f->wordAutomaton(word f, S'));
    A := commAutomaton(S');
    for Af in Afs do A = productAutomaton(A,Af);
    A
    )

-- Inputs:
--  A - an automaton
--  weights - a list of gradings of the letters in the alphabet
-- Output:
--  Hilbert series of the words not rejected by A
automatonHS = (A,weights) -> (
    k := #A.states;
    T := ring first weights;
    M := apply(#A.alphabet, l->transitionMatrix(A,l));
    v := sub(initVect A,T);
    u := sub(nonRejectVect A,T);
    N := id_(T^k) - sum apply(#A.alphabet, i->(weights#i)*(M#i));
    1 + first flatten entries (s*u*(inverse N)*v)
    )

T = frac(QQ[s,t])
eHilbertSeries = F -> (
    k := numrows exponentMatrix first F;
    A := idealAutomaton F;
    weights := {s}|toList(k:t);
    automatonHS(A,weights)
    )
    

end
----------

restart
load "eHilbert.m2"

T = frac(QQ[s,t])
S = {symbol x, symbol y}
R = buildERing(S,{1,1},QQ,2) -- make a ring with 2 variable orbits, x,y
f = y_1*x_0 - x_1*y_0 -- {f} is an EGB for 2x2 minors
A = idealAutomaton {f}; -- A rejects monomials in the intial ideal of {f} and words not in standard form
h = automatonHS(A,{s,t,t}) -- the shift operator gets weight s, and x,y both get weight t

S = {symbol x}
R = buildERing(S,{1},QQ,2)
A = idealAutomaton {x_0^2,x_0*x_1};
h = automatonHS(A,{s,t})




S = {symbol x, symbol y}
w = word f
A1 = wordAutomaton(w,{rho}|S)
B = commAutomaton({rho}|S)
A = productAutomaton(A1,B)

S = {symbol x}
R = buildERing(S,toList(#S:1),QQ,1)
m = x_0^2
exponentMatrix m
w = word m
A = wordAutomaton(w,{rho}|S)


