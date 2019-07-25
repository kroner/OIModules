newPackage(
     "RegularLanguages",
     Version =>"0.0",
     Date => "2019",
     Headline => "A package for regular languages and their Hilbert series",
     HomePage => "",
     Authors => {
	  },
     PackageImports => {
	 "EquivariantGB",
	 "OIModules"
	 },
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
    "isDeterministic",
    "transitionMatrix",
    "renameStates",
    "union",
    "intersection",
    "kleeneStar",
    "wordAutomaton",
    "setAutomaton",
    "surjectionToAutomaton",
    "monomialAutomaton",
    "monomialToWord",
    "commAutomaton",
    "idealAutomaton",
    "automatonHS",
    "NFA2DFA",
    "cat",
    "kleeneSetAutomaton"
     }

protect \ {arrows, accepts, states, alphabet, initial, transitions, deterministic}
--Types
Automaton = new Type of HashTable
Word = new Type of List
RegularLanguage = new Type of HashTable

--Methods

word = method()
word(List) := L -> new Word from L
word(String) := s -> word characters s

-- New automaton with states indexed by snames, alphabet S, i the intial state and A the set of accept states.
-- The arrows are not yet defined.
automaton = method()
automaton(List,List,HashTable,Set) := Automaton => (S,sts,ars,Acc) -> automaton(S,sts,ars,toList Acc)
automaton(List,List,HashTable,List) := Automaton => (S,sts,ars,Acc) -> (
    L := for state in sts list (
	starrows := if ars#?state then new MutableHashTable from ars#state else new MutableHashTable;
	for l in S do if not starrows#?l then starrows#l = {last sts};
	state => new HashTable from starrows
	);
    ars = hashTable L;
    Mats := arrowsToMatrices(S,sts,ars);
    Acc = toList((set sts)*(set Acc));
    d := not any(sts, state -> any(S, l -> #ars#state#l > 1));
    new Automaton from {
	alphabet => S, 
	states => sts,
	arrows => ars,
	transitions => Mats,
	initial => first sts, 
	accepts => set Acc,
	deterministic => d
	}
    )
automaton(List,List,List,Set) := Automaton => (S,sts,Mats,Acc) -> automaton(S,sts,Mats,toList Acc)
automaton(List,List,List,List) := Automaton => (S,sts,Mats,Acc) -> (
    ars := matricesToArrows(S,sts,Mats);
    Acc = toList((set sts)*(set Acc));
    d := not any(sts, state -> any(S, l -> #ars#state#l > 1));
    new Automaton from {
	alphabet => S, 
	states => sts,
	arrows => ars,
	transitions => Mats,
	initial => first sts, 
	accepts => set Acc,
	deterministic => d
	}
    )
automaton(List,ZZ,List,Set) := Automaton => (S,n,Mats,Acc) -> automaton(S,n,Mats,toList Acc)
automaton(List,ZZ,List,List) := Automaton => (S,n,Mats,Acc) -> automaton(S,toList(0..n-1),Mats,Acc)


-- converts HashTables of arrows to a list of transition matrices
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

-- converts a list of transition matrices to HashTables of arrows
matricesToArrows = method()
matricesToArrows(List,List,List) := (S,states,Mats) -> (
    HashList := apply(states, state->new MutableHashTable);
    n := #states;
    for l from 0 to #S-1 do (
	M := Mats#l;
	for j from 0 to n-1 do (
	    is := select(n, i-> M_(i,j) != 0);
	    is = apply(is, i -> states#i);
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
Automaton String := (A,s) -> A (word s)

net Automaton := A -> (
    "Automaton on states "|net(A.states)
    )


complement(Automaton) := Automaton => A -> (
    H := new MutableHashTable from A;
    H.accepts = set(A.states) - A.accepts;
    new Automaton from H
    )

productList = (L,M) -> flatten for a in L list for b in M list (a,b)

intersection = method()
intersection(Automaton,Automaton) := Automaton => (A,B) -> (
    S := A.alphabet;
    sts := productList(A.states, B.states);
    Acc := productList(toList A.accepts, toList B.accepts);
    ars := hashTable for state in sts list (
	state => hashTable for l in S list (
	    l => productList(A.arrows#(state#0)#l, B.arrows#(state#1)#l)
	    )
	);
    	automaton(S,sts,ars,Acc)
    )	 

union = method()
union(Automaton,Automaton) := Automaton => (A,B) -> (
    complement intersection(complement A, complement B)
    )

cat = method()
cat(Automaton,Automaton) := Automaton => (A,B) -> (
    S := A.alphabet;
    n := #A.states;
    m := #B.states;
    Mats := for l from 0 to #S-1 list (
	C := ((B.transitions#l)_{0})*(acceptVect A);
	matrix{{A.transitions#l, map(ZZ^n,ZZ^m,0)},{C, B.transitions#l}}
	);
    Acc := apply(toList B.accepts, state->n+position(B.states,st->st===state));
    if member(B.initial, B.accepts) then (
	AccA := apply(toList A.accepts, state->position(A.states,st->st===state));
	Acc = Acc|AccA;
	);
    D := automaton(S,n+m,Mats,Acc);
    NFA2DFA D
    )

kleeneStar = method()
kleeneStar(Automaton) := Automaton => A -> (
    S := A.alphabet;
    Mats := for l from 0 to #S-1 list A.transitions#l + ((A.transitions#l)_{0})*(acceptVect A);
    B := automaton(S,A.states,Mats,{A.initial}|(toList A.accepts));
    NFA2DFA B
    )

transitionMatrix = method()
transitionMatrix(Automaton,Thing) := (A,l) -> (
    k := position(A.alphabet, m -> (m===l or toString m == toString l));
    A.transitions#k
    )

renameStates = method()
renameStates(Automaton) := A -> renameStates(A,toList(0..#A.states-1))
renameStates(Automaton,List) := (A,L) -> (
    assert(#L == #A.states);
    Acc := select(#L, i->member(A.states#i, A.accepts));
    Acc = apply(Acc, i->L#i);
    automaton(A.alphabet,L,A.transitions,Acc)
    )

-- characteristic column vector of the initial state.
initVect = A -> transpose matrix {toList apply(A.states, s->if s===A.initial then 1 else 0)}
-- characteristic row vector of the accept states.
acceptVect = A -> matrix {toList apply(A.states, s->if member(s,A.accepts) then 1 else 0)}

isDeterministic = method()
isDeterministic(Automaton) := A -> A.deterministic

automatonHS = method()
automatonHS(Automaton,List) := (A,weights) -> (
    k := #A.states;
    T := ring first weights;
    M := apply(A.alphabet, l->sub(transitionMatrix(A,l),T));
    v := sub(initVect A,T);
    u := sub(acceptVect A,T);
    N := id_(T^k) - sum apply(#A.alphabet, i->(M#i)*(weights#i));
    first flatten entries (u*(inverse N)*v)
    )

automatonHS(Automaton) := A -> (
    n:=#(A.alphabet);
    T:=frac(QQ[t]);
    use T;
    automatonHS(A,apply(n,i->t))
    )

-- remove unreachable states from an automaton
trim Automaton := o -> A -> (
    S := A.alphabet;
    stateHash := new MutableHashTable from {A.initial => 0};
    seen := new MutableHashTable from stateHash;
    while #keys(stateHash) > 0 do (
	state := first keys stateHash;
	for l in S do for newState in A.arrows#state#l do (
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


-- automaton that accepts any letter of the input set
-- it is equivalent to the regular expression {a,b,...,n}
-- Input: A language S and a subset of letter U
setAutomaton = method()
setAutomaton(List,List) :=(S,U) -> (
    junk:=hashTable apply(S,i->(i=>{2}));
    hash0 := hashTable apply(S, i-> if member(i,U) then (i=>{1}) else (i=>{2}));
    ars:= hashTable {0 => hash0, 1=>junk, 2=>junk};
    automaton(S,{0,1,2},ars,{1})
    )


-- an optimized version of the composition between the setAutomaton an the kleene
-- automaton. It is equivalent to the regular expression {1,2,..,n}}*
kleeneSetAutomaton = method()
kleeneSetAutomaton(List,List) := (S,U) -> (
    junk:=hashTable apply(S,i->(i=>{1}));
    hash0 := hashTable apply(S, i-> if member(i,U) then (i=>{0}) else (i=>{1}));
    ars:= hashTable {0 => hash0, 1=>junk, 2=>junk};
    trim automaton(S,{0,1},ars,{0})
    
    )


--Input: ordered surjection f:[m]->[n] encoded as (f(1),...,f(m)).
--Output: Regular language for ideal generated by this in OS^op-module P_n
surjToAutomaton = method()
surjToAutomaton List := f -> (
    m:=length f;
    val:=sort unique f;
    seen:=1;
    ans:=cat(wordAutomaton(val, word{f_0}), kleeneSetAutomaton(val,{1}));
    for i from 1 to m-1 do (
	ans = cat(ans, wordAutomaton(val, word{f_i}));
	if f_i > seen then 
	if f_i > seen+1 then error "Input is not an ordered surjection."
	else seen=seen+1;
    	ans = cat(ans, kleeneSetAutomaton(val,toList(1..seen)));
	);
    ans
    )

--Input: a list of ordered surjections
--Output: Regular language for ideal generated by the ordered surjections
surjectionToAutomaton = method()
surjectionToAutomaton List := L -> (
    ans:=surjToAutomaton(L_0);
    for i from 1 to #L-1 do ans=union(ans,surjToAutomaton(L_i));
    ans
    )

elementToWord = method()
elementToWord List := e -> (
    n := source e;
    m := target e;
    k := 1;
    L := for i from 1 to n list (
	space := (e i) - k;
	k = e i;
	(toList (space:0))|{1}
	);
    (join L)|(toList (m-k):0)
    )

elementAutomaton = method()
elementAutomaton List := e -> (
    w := elementToWord e;
    hashs := for i from 0 to #w-1 list (
	if w#i == 0 then hashTable{0 => {i+1}} else hashTable{0 => {i}, 1 => {i+1}}
	);
    automaton({0,1},toList(0..#w+1),hashTable hashs,{#w})
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
	A.arrows#i#(w#i) = {i+1};
	if w#i == 0 then lastrho = i+1
	else A.arrows#i#0 = {lastrho};
	);
    A
    )

-- Automaton on alphabet S that rejects words not in standard form.
-- (A word is in standard form if it does not contain subword s_js_i for j > i > 0,
-- with S = {s_0,s_1,...,s_k}.)
commAutomaton = S -> (
    A := automaton(S,#S,toList(0..#S-2));
    for i from 0 to #S-2 do (
	A.arrows#i#0 = {0};
	for l from 0 to #S-2 do
	    A.arrows#i#(l+1) = if l < i then {#S-1} else {l};
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
    if isDeterministic aut then return aut;
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
      trim automaton(aut.alphabet,sort keys(ars),ars,acc)
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
          Automaton
	  (symbol SPACE,Automaton,List)
	  (symbol SPACE,Automaton,Word)
     Headline
          the class of finite state automata
     Description
          Text
	       Can represent a deterministic or nondeterinistic automaton.
	       
	       The following example makes an automaton that only accepts the word aab.
	  Example
	       S = {"a","b"}
	       B = wordAutomaton(S, word "aab")
	       B "aab"
	       B "aabb"
///

doc ///
     Key
          automaton
	  (automaton,List,List,HashTable,Set)
	  (automaton,List,List,HashTable,List)
	  (automaton,List,List,List,Set)
	  (automaton,List,List,List,List)
	  (automaton,List,ZZ,List,Set)
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
	       point to the last state.  The alphabet elements can either be symbols or strings
	       with length 1.
	       
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
	       A = automaton({"a","b"},3,tmats,{2})
	       A "abaababa"
	       A "bb"
///

doc ///
     Key
          Word
     Headline
          the class of words in a finite alphabet
     Description
          Text
	       Should this class even exist?
	  Example
	       S = {a,b}
	       w = word {a,a,a}
	       A = wordAutomaton(S, w)
	       A w
///

doc ///
     Key
	  (trim,Automaton)
     Headline
          removes extraneous states from an Automaton
     Usage
          B = trim A
     Inputs
          A:Automaton
     Outputs
          B:Automaton
     Description
          Text
	       Removes any unreachable states from an Automaton
	  Example
	       tmats = {matrix{{1,1,0},{0,0,0},{0,0,1}}, matrix{{0,0,0},{0,0,0},{1,1,1}}}
	       A = automaton({0,1},3,tmats,{1,2})
	       B = trim A
///

doc ///
     Key
	  (complement,Automaton)
     Headline
          Automaton for the complement language
     Usage
          B = complement A
     Inputs
          A:Automaton
     Outputs
          B:Automaton
     Description
          Text
	       Produces the automaton that accepts on the language that is complement to that
	       of the input.  These two automata differ only in which states are accepting.
	  Example
	       S = {a,b}
	       A = wordAutomaton(S, word {a,a})
	       B = complement A
	       B {a,a}
     Caveat
          Applying this function to nondeterministic automata may give incorrect results.
///

doc ///
     Key
          union
	  (union,Automaton,Automaton)
     Headline
          Automaton for the union of languages
     Usage
          C = union(A,B)
     Inputs
          A:Automaton
	  B:Automaton
     Outputs
          C:Automaton
     Description
          Text
	       Produces the automaton that accepts on the language that is the union of
	       those accepted by the two input automata
	  Example
	       S = {a,b}
	       A = wordAutomaton(S, word {a,a})
	       B = wordAutomaton(S, word {b,b})
	       C = union(A,B)
	       C {a,a}
///

doc ///
     Key
     	  intersection
	  (intersection,Automaton,Automaton)
     Headline
          Automaton for the intersection of languages
     Usage
          C = intersection(A,B)
     Inputs
          A:Automaton
	  B:Automaton
     Outputs
          C:Automaton
     Description
          Text
	       Produces the automaton that accepts on the language that is the intersection of
	       those accepted by the two input automata
	  Example
	       S = {a,b}
	       A = kleeneStar(wordAutomaton(S, word {a,a}))
	       B = kleeneStar(wordAutomaton(S, word {b,b}))
	       C = intersection(A,B)
	       C ""
///

doc ///
     Key
          cat
	  (cat,Automaton,Automaton)
     Headline
          Automaton for the concatenation of languages
     Usage
          C = cat(A,B)
     Inputs
          A:Automaton
	  B:Automaton
     Outputs
          C:Automaton
     Description
          Text
	       Produces the automaton that accepts on the language that is the concatenation of
	       those accepted by the two input automata
	  Example
	       S = {a,b}
	       A = wordAutomaton(S, word {a,a})
	       B = wordAutomaton(S, word {b,b})
	       C = cat(A,B)
	       C {a,a,b,b}
///

doc ///
     Key
          kleeneStar
	  (kleeneStar,Automaton)
     Headline
          Automaton for the Kleene star of a language
     Usage
          B = kleeneStar(A)
     Inputs
          A:Automaton
     Outputs
          B:Automaton
     Description
          Text
	       Produces the automaton that accepts on the language that is the Kleene star of
	       the one accepted by the input automaton.
	  Example
	       S = {a,b}
	       A = wordAutomaton(S, word {a})
	       B = kleeneStar A
	       B {a,a,a,a}
	       B {}
///

doc ///
     Key
          automatonHS
	  (automatonHS,Automaton)
	  (automatonHS,Automaton,List)
     Headline
          generating function of an automaton
     Usage
          f = automatonHS(A)
	  f = automatonHS(A,W)
     Inputs
          A:Automaton
	  W:List
	       weights
     Outputs
          f:RingElement
     Description
          Text
	       Produces the generating function of the language accepted by the automaton
	       with weights W.  W should have a weight for each element of the alphabet,
	       and the weights should be elements of a fraction field.
	       
	       If W is not specified, then the default behavior is to use the variable t in frac(QQ[t])
	  Example
	       S = {a,b}
	       Mats = {matrix{{1,1,0},{0,0,0},{0,0,1}}, matrix{{0,0,0},{1,0,0},{0,1,1}}}
	       A = automaton({a,b},3,Mats,{2})
	       f = automatonHS(A)
	       factor(f)
	       T = frac(QQ[x,y])
	       g = automatonHS(A,{x,y})
	       factor(g)
     Caveat
          Applying this function to nondeterministic automata may give incorrect results.
///

doc ///
     Key
          isDeterministic
	  (isDeterministic,Automaton)
     Usage
          b = isDeterministic(A)
     Inputs
          A:Automaton
     Outputs
          b:Boolean
     Description
          Text
	       Returns whether the automaton is deterministic (one arrow per letter from each
	       state) or nondeterministic (possibly more arrows per letter).
	  Example
	       S = {a,b}
	       Mats = {matrix{{1,1,0},{0,0,0},{0,0,1}}, matrix{{0,0,0},{1,0,0},{0,1,1}}}
	       A = automaton({a,b},3,Mats,{2})
	       isDeterministic A
///

doc ///
     Key
          wordAutomaton
	  (wordAutomaton,List,Word)
     Headline
          Automaton of a singleton language 
     Usage
          A = wordAutomaton(S,w)
     Inputs
          S:List
	       the alphabet
          w:Word
     Outputs
          A:Automaton
     Description
          Text
	       Returns an Automaton that accepts the singleton language consisting only of the
	       word w.
	  Example
	       S = {a,b}
	       w = word {a,a,b}
	       A = wordAutomaton(S,w)
	       A w
	       A {a,a,b,b}
///

doc ///
     Key
          setAutomaton
	  (setAutomaton,List,List)
     Headline
          Automaton of a set of letters 
     Usage
          A = setAutomaton(S,U)
     Inputs
          S:List
	       the alphabet
	  U:List
	       a subset of the alphabet
     Outputs
          A:Automaton
     Description
          Text
	       Returns an Automaton that accepts only the singleton words for the letters in U.
	  Example
	       S = {a,b,c}
	       A = setAutomaton(S,{a,b})
	       A {a}
	       A {c}
///


doc ///
     Key
          kleeneSetAutomaton
	  (kleeneSetAutomaton,List,List)
     Headline
          Automaton corresponding to the Kleene star of a set of letter 
     Usage
          A = kleeneSetAutomaton(S,U)
     Inputs
          S:List
	       the alphabet
	  U:List
	       a subset of the alphabet
     Outputs
          A:Automaton
     Description
          Text 
	       This method returns an automaton equivalent to kleeneStar setAutomaton(S,U).
	       However, it is implemented to give an automaton which is the smallest possible
	       for this language. This helps to minimize the size of automatons that
	       are built using these operations, for example, the automaton associated to
	       a list of OS^op morphisms.  
	  Example
	       S = {a,b,c}
	       A = kleeneStar setAutomaton(S,{a,b})
	       peek A
	       B = kleeneSetAutomaton(S,{a,b})
	       peek B
	       A = kleeneStar setAutomaton(S,{a,b,c})
	       peek A
	       B = kleeneSetAutomaton(S,{a,b,c})
	       peek B 
///




doc ///
    Key
    	surjectionToAutomaton
	(surjectionToAutomaton, List)
    Headline
    	converts a list of OS^op-morphisms into a regular language
    Usage
    	A = surjectionToAutomaton(L)
    Inputs
	L:List
	    List
    Outputs
    	A:Automaton
    Description
    	Text
	    The monomials in a monomial submodule of a principal projective OS^{op}-module P_n 
	    can be encoded by a regular sequence in the alphabet {1..n}. This method constructs
	    the corresponding DFA.
	Example
	    A=surjectionToAutomaton({{1}})
	    use frac(QQ[t])
	    automatonHS(A,{t})
///

doc ///
    Key
    	NFA2DFA
	(NFA2DFA, Automaton)
    Headline
    	transforms a NFA into a DFA. 
    Usage
    	B = NFA2DFA(A)
    Inputs
	A:Automaton
	    Automaton
    Outputs
    	B:Automaton
    Description
    	Text
	    Given an Non-deterministic Finite Automaton (NFA) there is a standard algorithm that transforms it into a
	    Deterministic Finite Automaton (DFA).
	    It works by constructing a new automaton from the power set of the states of the NFA.
	Example
	    A= kleeneStar(union(wordAutomaton({a,b}, word {a}),wordAutomaton({a,b}, word {b})))
	    peek A
	    B = NFA2DFA A
	    peek B
///
    	

end
----------

restart
loadPackage "RegularLanguages"
installPackage "RegularLanguages"
tmats = {matrix{{1,1,0},{0,0,0},{0,0,1}}, matrix{{0,0,0},{1,0,0},{0,1,1}}}
A = automaton({a,b},3,tmats,{2}) -- accepts words with two b's in a row
isDeterministic A
A {a,b,a,a,b,a,b,a}
A {b,b}
AA = cat(A,A)
isDeterministic AA
AA {a,b,b,a,b,b}
AA {a,b,b,a,b,a}
A' = kleeneStar(A)
A' {b}
A' {b,b,b,b}
B = wordAutomaton({a,b}, word {a,a,b})
B' = kleeneStar B
B' {a,a,b,a,a,b}
B' {a,a,b,b}
automatonHS(B',{1,1})

A = wordAutomaton({1},word{1})
B = kleeneSetAutomaton({1},{1})
AB = cat(A,B)
AB' = NFA2DFA AB
ABA = cat(AB',A)
ABA' = NFA2DFA ABA
ABAB = cat(ABA',B)

needsPackage "RegularLanguages"
needsPackage "EquivariantGB"
T = frac(QQ[s,t])
S = {symbol x, symbol y}
R = buildERing(S,{1,1},QQ,2) -- make a ring with 2 variable orbits, x,y
f = y_1*x_0 - x_1*y_0 -- {f} is an EGB for 2x2 minors
A = idealAutomaton {f}; -- A rejects monomials in the intial ideal of {f} and words not in standard form
h = 1 + s*automatonHS(A,{s,t,t}) -- the shift operator gets weight s, and x,y both get weight t



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

S = {0,1,2}
A = setAutomaton(S,{1})
B = setAutomaton(S,{1})
B = kleeneStar(B)

path = append(path,"~/OIModules/OIModules/")
S = {0,1,2}
A = setAutomaton(S,{1})
B = setAutomaton(S,{1})
B = kleeneStar(B)
A = cat(A,B)

kleeneStar(union(wordAutomaton({a,b},word{a}),wordAutomaton({a,b},word{b})))

