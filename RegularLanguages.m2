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
    "kleeneStar",
    "wordAutomaton",
    "monomialAutomaton",
    "monomialToWord",
    "commAutomaton",
    "idealAutomaton",
    "automatonHS",
    "NFA2DFA",
    "cat"
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
automaton(List,List,HashTable,Set) := (S,sts,ars,Acc) -> automaton(S,sts,ars,toList Acc)
automaton(List,List,HashTable,List) := (S,sts,ars,Acc) -> (
    L := for state in sts list (
	starrows := if ars#?state then new MutableHashTable from ars#state else new MutableHashTable;
	for l in S do if not starrows#?l then starrows#l = {last sts};
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
automaton(List,List,List,Set) := (S,sts,Mats,Acc) -> automaton(S,sts,Mats,toList Acc)
automaton(List,List,List,List) := (S,sts,Mats,Acc) -> (
    ars := matricesToArrows(S,sts,Mats);
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
automaton(List,ZZ,List,Set) := (S,n,Mats,Acc) -> automaton(S,n,Mats,toList Acc)
automaton(List,ZZ,List,List) := (S,n,Mats,Acc) -> automaton(S,toList(0..n-1),Mats,Acc)


-- transition matrix of automaton A for letter l
arrowsToMatrices = method()
arrowsToMatrices(List,List,HashTable) := (S,states,H) -> (
    n := #states;
    for l in S list (
    	M := new MutableMatrix from map(ZZ^n,ZZ^n,0);
    	for j from 0 to n-1 do for i from 0 to n-1 do (
	    if member(states#i, H#(states#j)#l) then M_(i,j) = 1;
	    );
    	new Matrix from M
	)
    )

matricesToArrows = method()
matricesToArrows(List,List,List) := (S,states,Mats) -> (
    HashList := apply(states, state->new MutableHashTable);
    n := #states;
    for l from 0 to #S-1 do (
	M := Mats#l;
	for j from 0 to n-1 do (
	    is := select(n, i-> M_(i,j) != 0);
	    (HashList#j)#(S#l) = is;
	    );
	);
    HashList = apply(n, j -> (states#j => new HashTable from HashList#j));
    hashTable HashList
    )

Automaton Word := (A,w) -> (
    v := initVect(A);
    for l in w do v = transitionMatrix(A,l)*v;
    (acceptVect(A)*v)_(0,0) != 0
    )
Automaton List := (A,L) -> A (word L)


complement(Automaton) := A -> (
    H := new MutableHashTable from A;
    H.accepts = set(keys A.states) - A.accepts;
    new Automaton from H
    )

intersect(Automaton,Automaton) := (A,B) -> (
    S := A.alphabet;
    sts := flatten for a in A.states list for b in B.states list (a,b);
    Acc := flatten for a in toList A.accepts list for b in toList B.accepts list (a,b);
    C := automaton(S,sts,(A.initial,B.initial),Acc);
    for state in sts do for l in S do (
	C.arrows#state#l = (A.arrows#(state#0)#l, B.arrows#(state#1)#l);
	);
    C
    )

union = method()
union(Automaton,Automaton) := (A,B) -> (
    complement ((complement A) * (complement B))
    )

cat = method()
cat(Automaton,Automaton) := (A,B) -> (
    S := A.alphabet;
    n := #A.states;
    m := #B.states;
    Mats := for l from 0 to #S-1 list (
	C := ((B.transitions#l)_{0})*(acceptVect A);
	matrix{{A.transitions#l, map(ZZ^n,ZZ^m,0)},{C, B.transitions#l}}
	);
    Acc := apply(toList B.accepts, state->n+position(B.states,st->st===state));
    automaton(S,n+m,Mats,Acc)
    )

kleeneStar = method()
kleeneStar(Automaton) := A -> (
    S := A.alphabet;
    Mats := for l from 0 to #S-1 list A.transitions#l + ((A.transitions#l)_{0})*(acceptVect A);
    automaton(S,A.states,Mats,A.accepts)
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

-- automaton that accepts only the word w
wordAutomaton = method()
wordAutomaton(List,Word) := (S,w) -> (
    n := #w;
    hashs := apply(n, i-> i => hashTable{w#i => {i+1}});
    arrows := hashTable hashs;
    automaton(S,toList(0..n+1),arrows,{n})
    )



----------------------------------------------------------------------------------------------
-- OI-algebra Hilbert series methods

-- Minimal standard form word representation of monomail m.
-- Outputs a list of integers, where 0 is the shift operator and 1,...,k are variable orbits.
monomialToWord = m -> (
    M := exponentMatrix m;
    Mlist := entries transpose M;
    w := flatten for row in Mlist list (flatten toList apply(#row, i->toList(row#i:i+1)))|{0};
    p := position(w, l->(l!=0), Reverse=>true);
    take(w,p+1)
    )

-- Automaton that rejects all standard form words of monomials that are
-- Inc-multiples of the monomial.
monomialAutomaton = (m,S) -> (
    w := monomialToWord m;
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
    Afs := apply(F, f->wordAutomaton(monomialToWord f, S'));
    A := commAutomaton(S');
    for Af in Afs do A = A * Af;
    A
    )


T = frac(QQ[s,t])
eHilbertSeries = F -> (
    k := numrows exponentMatrix first F;
    A := idealAutomaton F;
    weights := {s}|toList(k:t);
    1 + s*automatonHS(A,weights)
    )
    


-- Given a Non-Deterministic Finite Automaton (NFA) it implements the classical algorithm
-- to convert it into a Deterministic Finite Automaton (DFA)
-- The states of the DFA are indexed by sets of states of the original automaton

-- Pre:The NFA stores lists of states as targets. If it has a single target a, it stores
-- the singleton {a}.
NFA2DFA = method() 
NFA2DFA(Automaton) := aut -> (
    
    ars := new MutableHashTable;
    frontier := { {first aut.states}};
    while #frontier > 0  do (
	  currentState := frontier#0;
	  frontier = drop (frontier,1);
	   
	  starrows:= new MutableHashTable from aut.arrows#(aut.initial);
	  for letter in keys(starrows) do (
	     starrows#letter = {unique flatten apply(currentState,st -> aut.arrows#st#letter)};
	     
	     
	     -- Check last is rejected state
	     -- Make the list of accepted states
	     if ( not ars#?(starrows#letter#0) ) then (
		 
		 frontier = append(frontier,starrows#letter#0);
		 );	    
	     );
	 ars#currentState = starrows;
      	 );
      
      acc:= select(keys(ars), l->any(l, i-> member(i,aut.accepts)));
      automaton(aut.alphabet,sort keys(ars),ars,acc)
      
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

doc ///
     Key
          automaton
	  (automaton,List,List,HashTable,List)
	  (automaton,List,List,List,List)
	  (automaton,List,ZZ,List,List)
     Headline
          constructor for Automaton
     Usage
          A = automaton(S,states,arrows,accepts)
	  A = automaton(S,states,Mats,accepts)
	  A = automaton(S,n,Mats,accepts)
     Inputs
          S:List
	       the alphabet
	  states:List
	       the names of the states
	  n:ZZ
	       the number of states
	  arrows:HashTable
	  Mats:List
	       transition matrices
	  accepts:List
	       the accepting states
     Outputs
          A:Automaton
     Description
          Text
	       Builds a finite state automaton over alphabet S.  The initial state is always
	       the first one in the list of states.  The last arguement specifies the accepting
	       states, and the rest are rejecting.  There are two main ways to specify the 
	       arrows between states:
	       
	       The first way is as a HashTable of HashTables.  The keys
	       of the HashTable are the states, and the values are HashTables that assign a
	       list of states to each element of the alphabet.  Any missing arrows default to 
	       point to the last state.
	       
	       This example accepts words in the alphabet \{a,b\} that contain at least one b
	  Example
	       arrows0 = hashTable{a=>{0},b=>{1}}
	       arrows1 = hashTable{a=>{1},b=>{1}}
	       H = hashTable{0=>arrows0, 1=>arrows1};
	       A = automaton({a,b},{0,1},H,{1})
	       A {a,a,b,a}
	  Text
	       The second way is as a list of transition matrices, one for each element of
	       the alphabet.  Each is a stochastic 0/1 matrix.  The matrix sends each standard
	       basis vector for a state to the standard basis vector of the state it points to.
	       
	       This example accepts words in the alphabet \{a,b\} that contain two b's in a row.
          Example
               tmats = {matrix{{1,1,0},{0,0,0},{0,0,1}}, matrix{{0,0,0},{1,0,0},{0,1,1}}}
	       A = automaton({a,b},3,tmats,{2})
	       A {a,b,a,a,b,a,b,a}
	       A {b,b}
///

end
----------

restart
installPackage "RegularLanguages"
tmats = {matrix{{1,1,0},{0,0,0},{0,0,1}}, matrix{{0,0,0},{1,0,0},{0,1,1}}}
A = automaton({0,1},3,tmats,{2})
A {0,1,0,0,1,0,1,0}
A {1,1}
AA = cat(A,A)
AA {0,1,1,1,1}
AA {0,1,1,1}
A' = kleeneStar(A)
A' {1}
A' {1,1,1,1}
B = wordAutomaton({a,b}, word {a,a,b})
B' = kleeneStar B
B' {a,a,b,a,a,b}
B' {a,a,b,b}
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
w = monomialToWord f
A1 = wordAutomaton(w,{rho}|S)
B = commAutomaton({rho}|S)
A = productAutomaton(A1,B)

S = {symbol x}
R = buildERing(S,toList(#S:1),QQ,1)
m = x_0^2
exponentMatrix m
w = monomialToWord m
A = wordAutomaton(w,{rho}|S)



S = {0, 1}
sts = toList ( 1..4)
arrows1  = new HashTable from {0 => {2},1=> {4}}
arrows2 = new HashTable from {0 => {2,3},1=> {2}}
arrows3 = new HashTable from {0 => {4},1=> {4}}
arrows4 = new HashTable from {0 => {4},1=> {4}}

ars = new HashTable from {1 => arrows1,2 => arrows2,3 => arrows3,4 => arrows4}
Acc = {3}

--A = automaton(S,states,arrows,accepted)
--NFA have a problem constructing the matrices with the current implementation 

tmats = {matrix{{1,1,0},{0,0,0},{0,0,1}}, matrix{{0,0,0},{1,0,0},{0,1,1}}}
A = automaton({0,1},3,tmats,{2})

A = new Automaton from {
	alphabet => S, 
	states => sts,
	arrows => ars,
	transitions => {},
	initial => first sts, 
	accepts => set Acc
	}

tmats = {matrix{{1,1,0},{0,0,0},{0,0,1}}, matrix{{0,0,0},{0,0,0},{1,1,1}}}
A = automaton({0,1},3,tmats,{1,2})
NFA2DFA A
