newPackage(
     "RegularLanguages",
     Version =>"0.0",
     Date => "2019",
     Headline => "A package for regular languages and their Hilbert series",
     HomePage => "",
     Authors => {
	  },
     PackageImports => {},
     DebuggingMode => true, --should be true while developing a package, 
     --   but false after it is done
     AuxiliaryFiles => false
     )

export {

     }

protect \ { }
--Types
Automaton = new Type of HashTable

--Methods

-- New automaton with states indexed by snames, alphabet S, i the intial state and A the set of accept states.
-- The arrows are not yet defined.
automaton = method()
automaton(List,List,Thing,List) := (S,statenames,i,Acc) -> (
    lastst := last statenames;
    arsHash := hashTable apply(S, s->(s=>lastst))
    ars := hashTable toList apply(statenames, st->(st => new MutableHashTable from arsHash));
    automaton(S,ars,i,Acc)
    )
automaton(List,ZZ,List) := (S,nstates,Acc) -> automaton(S,toList(0..nstates-1),0,Acc)
automaton(List,HashTable,Thing,List) := (S,ars,i,Acc) -> (
    sts := keys ars;
    assert(ars#?i);
    new Automaton from {
	alphabet => S, 
	states => sts,
	arrows => ars,
	initial => i, 
	accepts => set Acc
	}
    )

sparseAutomaton = method()
sparseAutomaton(List,ZZ,List,List) := (S,nstates,ars,Acc) -> (
    A := automaton(S,nstates,Acc);
    for arrow in ars do A.arrows#(ars#0)#(ars#1) = ars#2;
    A
    )

matrixAutomaton = method()
matrixAutomaton(List,List,List) := (S,Mats,Acc) -> (
    n := numcols first Mats;
    A := automaton(S,n,Acc);
    for i from 0 to #S-1 do (
	M := Mats#i;
	for j from 0 to n-1 do (
	    );
      
	);
    A
    )


complement(Automaton) := A -> (
    H := new MutableHashTable from A;
    H.accepts = set(keys A.states) - A.accepts;
    new Automaton from H
    )


-- automaton that rejects if either A or B would reject.  All reject states are combined to one terminal reject state.
Automaton * Automaton := (A,B) -> (
    S := A.alphabet;
    sts := flatten for a in A.states list for b in B.states list (a,b);
    Acc := flatten for a in toList A.accepts list for b in toList B.accepts list (a,b);
    C := automaton(S,sts,(A.initial,B.initial),Acc);
    for state in sts do for l in S do (
	C.arrows#state#l = (A.arrows#(state#0)#l, B.arrows#(state#1)#l);
	);
    C
    )

Automaton + Automaton := (A,B) -> (
    complement ((complement A) * (complement B))
    )

-- transition matrix of automaton A for letter l
transitionMatrix = method()
transitionMatrix(Automaton,Thing) := (A,l) -> (
    M := new MutableMatrix from map(ZZ^(#A.states),ZZ^(#A.states),0);
    for i from 0 to #A.states - 1 do (
	j := position(A.states, k->A.arrows#(A.states#i)#l === k);
	M_(j,i) = 1;
	);
    new Matrix from M
    )

-- characteristic column vector of the initial state.
initVect = A -> transpose matrix {toList apply(A.states, s->if s===A.initial then 1 else 0)}
-- characteristic row vector of the accept states.
acceptVect = A -> matrix {toList apply(A.states, s->if member(s,A.accepts) then 1 else 0)}

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
    u := sub(acceptVect A,T);
    N := id_(T^k) - sum apply(#A.alphabet, i->(weights#i)*(M#i));
    1 + first flatten entries (s*u*(inverse N)*v)
    )



-- OI-algebra Hilbert series methods

-- Minimal standard form word representation of monomail m.
-- Outputs a list of integers, where 0 is the shift operator and 1,...,k are variable orbits.
word = m -> (
    M := exponentMatrix m;
    Mlist := entries transpose M;
    w := flatten for row in Mlist list (flatten toList apply(#row, i->toList(row#i:i+1)))|{0};
    p := position(w, l->(l!=0), Reverse=>true);
    take(w,p+1)
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
    A := automaton((0..#S-1),S,0,{#S-1});
    for i from 0 to #S-2 do (
	A.states#i#0 = 0;
	for l from 0 to #S-2 do
	    A.states#i#(l+1) = if l < i then #S-1 else l;
	);
    A
    )

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
    for Af in Afs do A = A * Af;
    A
    )


T = frac(QQ[s,t])
eHilbertSeries = F -> (
    k := numrows exponentMatrix first F;
    A := idealAutomaton F;
    weights := {s}|toList(k:t);
    automatonHS(A,weights)
    )
    






beginDocumentation()

doc ///
     Key
          RegularLanguages
     Headline
          A package for regular languages and their Hilbert series
     Description
          Text
	       
	  Example
	       
	  Text
	       
     Subnodes
          
///



end
----------

restart
load "eHilbert.m2"
needsPackage "EquivariantGB"

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
