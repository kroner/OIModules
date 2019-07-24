newPackage(
     "RegularLanguages",
     Version =>"0.0",
     Date => "2019",
     Headline => "A package for regular languages and their Hilbert series",
     HomePage => "",
     Authors => {
	  },
     PackageImports => {"EquivariantGB"},
     DebuggingMode => true, --should be true while developing a package, 
     --   but false after it is done
     AuxiliaryFiles => false
     )

export {
    "Automaton",
    "Word",
    "word",
    "RegularLanguage",
    "automaton",
    "transitionMatrix",
    "wordAutomaton",
    "commAutomaton",
    "idealAutomaton",
    "automatonHS"
     }

protect \ {arrows, accepts, states, alphabet, initial, transitions}
--Types
Automaton = new Type of HashTable
Word = new Type of List
RegularLanguage = new Type of HashTable

--Methods

word = method()
word(List) := L -> new Word from L

-- New automaton with states indexed by snames, alphabet S, i the intial state and A the set of accept states.
-- The arrows are not yet defined.
automaton = method()
automaton(List,List,HashTable,List) := (S,sts,ars,Acc) -> (
    n := #sts;
    L := for state in sts list (
	starrows := new MutableHashTable from ars#state;
	for l in S do if not starrows#?l then starrows#l = last sts;
	state => new HashTable from starrows
	);
    ars = hashTable L;
    Mats := arrowsToMatrices(S,sts,ars);
    Acc = toList((set sts)*(set Acc)); 
    new Automaton from {
	alphabet => S, 
	states => sts,
	arrows => ars,
	transitions => Mats,
	initial => first sts, 
	accepts => set Acc
	}
    )
automaton(List,List,List,List) := (S,states,Mats,Acc) -> (
    ars := matricesToArrows(S,states,Mats);
    automaton(S,states,ars,Acc)
    )
automaton(List,ZZ,List,List) := (S,n,Mats,Acc) -> automaton(S,toList(0..n-1),Mats,Acc)

-- transition matrix of automaton A for letter l
arrowsToMatrices = method()
arrowsToMatrices(List,List,HashTable) := (S,states,H) -> (
    n := #states;
    for l in S list (
    	M := new MutableMatrix from map(ZZ^n,ZZ^n,0);
    	for i from 0 to #states - 1 do (
	    j := position(states, k->H#(states#i)#l === k);
	    M_(j,i) = 1;
	    );
    	new Matrix from M
	)
    )

matricesToArrows = method()
matricesToArrows(List,List,List) := (S,states,Mats) -> (
    HashList := apply(states, state->new MutableHashTable);
    n := #states;
    for i from 0 to #S-1 do (
	M := Mats#i;
	for j from 0 to n-1 do (
	    k := position(flatten entries M_{j}, e -> e!=0);
	    (HashList#j)#(S#i) = k;
	    );
	);
    HashList = apply(n, j -> (states#j => new HashTable from HashList#j));
    hashTable HashList
    )

Automaton Word := (A,w) -> (
    state := A.initial;
    for l in w do state = A.arrows#state#l;
    member(state,A.accepts)
    )
Automaton List := (A,L) -> A word L


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


transitionMatrix = method()
transitionMatrix(Automaton,Thing) := (A,l) -> (
    k := position(A.alphabet, m -> m===l);
    A.transitions#k
    ) 

-- characteristic column vector of the initial state.
initVect = A -> transpose matrix {toList apply(A.states, s->if s===A.initial then 1 else 0)}
-- characteristic row vector of the accept states.
acceptVect = A -> matrix {toList apply(A.states, s->if member(s,A.accepts) then 1 else 0)}


automatonHS = method()
automatonHS(Automaton,List) := (A,weights) -> (
    k := #A.states;
    T := ring first weights;
    M := apply(#A.alphabet, l->sub(transitionMatrix(A,l),T));
    v := sub(initVect A,T);
    u := sub(acceptVect A,T);
    N := id_(T^k) - sum apply(#A.alphabet, i->(M#i)*(weights#i));
    first flatten entries (u*(inverse N)*v)
    )

-- remove unreachable states from an automaton
trim Automaton := o -> A -> (
    S := A.alphabet;
    stateHash := new MutableHashTable from {A.initial => 0};
    seen := new MutableHashTable from stateHash;
    while #keys(stateHash) > 0 do (
	state := first keys stateHash;
	for l in S do (
	    newState := A.arrows#state#l;
	    if seen#?newState then continue;
	    stateHash#newState = 0;
	    seen#newState = 0;
	    );
	remove(stateHash,state);
	);
    remove(seen,A.initial);
    sts := {A.initial}|(keys seen);
    automaton(S,sts,A.arrows,toList A.accepts)
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
    A := automaton(S,#w+1,toList(0..#w-1));
    lastrho := 0;
    for i from 0 to #w-1 do (
	A.arrows#i#(w#i) = i+1;
	if w#i == 0 then lastrho = i+1
	else A.arrows#i#0 = lastrho;
	);
    A
    )

-- Automaton on alphabet S that rejects words not in standard form.
-- (A word is in standard form if it does not contain subword s_js_i for j > i > 0,
-- with S = {s_0,s_1,...,s_k}.)
commAutomaton = S -> (
    A := automaton(S,#S,toList(0..#S-2));
    for i from 0 to #S-2 do (
	A.arrows#i#0 = 0;
	for l from 0 to #S-2 do
	    A.arrows#i#(l+1) = if l < i then #S-1 else l;
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
    


-- Given a Non-Deterministic Finite Automaton (NFA) it implements the classical algorithm
-- to convert it into a Deterministic Finite Automaton (DFA)
-- The states of the DFA are indexed by sets of states of the original automaton

-- Pre: 
NFA2DFA(Automaton) = automaton -> (
    
    states := new MutableHashTable;
    arrows := new MutableHashTable;
    
    frontier:= new MutableList from {{automaton#initial}};
    while #frontier > 0  do (
	  currentState := frontier#0;
	  drop (frontier,1);
	   
	  starrows:= new MutableHashTable from automaton#arrows(frontier#0);
	  
	  for i to #keys(starrows) do (
	     letter:= keys(starrows)#i;  
	     stararrows#letter = unique 
	     flatten apply(currentState,st -> automaton#arrows#letter);
	     
	     if ( states?#(stararrows#letter) ) then (
		 
		 frontier = append(frontier,stararrows#letter);
		 );
		    
	  );	   
      ); 
	     
	
	) 
    )




beginDocumentation()

doc ///
    Key
        RegularLanguages
    Headline
        A package for regular languages and their Hilbert series
    Description
        Text
	    Do regular language stuff.
          
///



end
----------

restart
installPackage "RegularLanguages"
tmats = {matrix{{1,1,0},{0,0,0},{0,0,1}}, matrix{{0,0,0},{1,0,0},{0,1,1}}}
A = automaton({0,1},3,tmats,{2})
A(new Word from {0,1,0,0,1,0,1,0})
A(new Word from {1,1})
T = frac(QQ[s,t])
automatonHS(A,{s,t})

tmats = {matrix{{1,1,0},{0,0,0},{0,0,1}}, matrix{{0,0,0},{0,0,0},{1,1,1}}}
A = automaton({0,1},3,tmats,{1,2})
trim A

needsPackage "EquivariantGB"
T = frac(QQ[s,t])
S = {symbol x, symbol y}
R = buildERing(S,{1,1},QQ,2) -- make a ring with 2 variable orbits, x,y
f = y_1*x_0 - x_1*y_0 -- {f} is an EGB for 2x2 minors
A = idealAutomaton {f}; -- A rejects monomials in the intial ideal of {f} and words not in standard form
h = 1 + s*automatonHS(A,{s,t,t}) -- the shift operator gets weight s, and x,y both get weight t

S = {symbol x}
R = buildERing(S,{1},QQ,2)
A = idealAutomaton {x_0^2,x_0*x_1};
h = 1 + s*automatonHS(A,{s,t})




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
