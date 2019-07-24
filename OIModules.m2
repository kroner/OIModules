-*- coding: utf-8 -*-

newPackage( "OIModules",
    Version => "0.1.0",
    Date => "July 22, 2019",
    Authors => {
	{Name => "Nathan Fieldsteel",
	    Email => "nathan.fieldsteel@uky.edu"},
	{Name => "name2",
	    Email => "email2"},
	{Name => "name3",
	    Email => "email3"},
	{Name => "name4",
	    Email => "email4"},
	{Name => "name5",
	    Email => "email5"},
	{Name => "name6",
	    Email => "email6"}
	},
    HomePage => "https://nathanfieldsteel.github.io",
    Headline => "A package for computations with OI-algebras and modules over OI-algebras",
    AuxiliaryFiles => false)

export {
    "OIObject",
    "OIMorphism",
    "OIHom",
    "OIMontoHilbert",
    "isOIMonomial",
    "makeOIAlgebra",
    "OIElement",
    "OIMonomials"
    "getOIBasis"
    }

protect \ {widthList,OIAlgebra,OIBasis}

---------------
-- New types --
---------------

FiniteTotallyOrderedSet = new Type of VisibleList
OrderPreservingInjectiveFunction = new Type of HashTable
ConstantOIAlgebra = new Type of HashTable
OIModule = new Type of HashTable
--OIModuleElement = new Type of VisibleList  
OIModuleElement = new Type of HashTable
-----------------------
-- Type constructors --
-----------------------
--Has Construction of OIElements

OIElement = method()

OIElement HashTable := OIModuleElement => H ->(
    new OIModuleElement from H)

OIMonomials = method()
OIMonomials OIModuleElement := List => H -> keys H
OIModuleElement + OIModuleElement := (a,b) ->(
    temp := {};
    for i in OIMonomials a do(
	if b#?i then temp = append(temp, {i,a#i+b#i})
	else temp = append(temp,{i,a#i}));
    for j in OIMonomials b do(
	if not a#?j then temp = append(temp,{j,b#j}));
    temphash := new HashTable from temp;
    return OIElement temphash)
    
ZZ*OIModuleElement := (a,b) -> (HOIElement(hashTable(for i in keys b list {i,a*b#i})))
QQ*OIModuleElement := (a,b) -> (HOIElement(hashTable(for i in keys b list {i,a*b#i})))
RingElement*OIModuleElement := (a,b) -> (HOIElement(hashTable(for i in keys b list {i,a*b#i})))

OIModuleElement - OIModuleElement := (a,b) -> a+((-1)*b)





-- constructor for OIElements

OrderPreservingInjectiveFunction == OrderPreservingInjectiveFunction := (a,b) ->(
    if #(source a) != #(source b) then return false
    else if #(target a)!= #(target b) then return false
    else(
	tempbool := true;
	for i from 1 to #(source a) do(
	    if a(i) != b(i) then tempbool false);
	return tempbool))    
    
--OIMonomialtoMonomial = mon->(
--    assert(isOIMonomial mon);
--    t := mon_0_1;
--    m := #(target t);
--    n := #(source t);
--    R := QQ;--Base(mon);
--    x := getSymbol "x";
--    S := QQ[x_0..x_n];-- R[x_0..x_n];
--    temp :=1;
--    if n ==1 then(
--	print "here";
--	temp= temp*((S_0)^(t(1)-1))*((S_1)^(m-t(1)));
--        return {R,temp})
--    else(
--	temp= temp*(S_0)^(t(1)-1)*(S_n)^(m-t(n));
--	for i from 2 to n-1 do temp = temp*(S_i)^(t(i+1)-t(i)-1);
--	return {R,temp}))
    
--OIMontoHilbert = L -> (
--    for i in L do assert(isOIMonomial i);
--    basecase := L_0;
--    n :=#source(basecase_0_1);
--    R := QQ; --TO BE REPLACED BY RING/FIELD DEPENDING ON MONOMIALS
--    x:= getSymbol "x";
--    S:=R[x_0..x_n];
--    temp :={};
--    for mon in L do(
--	tempmonomial := 1;
--	t := mon_0_1;
--	m := #(target t);
--	tempmonomial = tempmonomial*(S_0)^(t(1)-1)*(S_n)^(m-t(n));
--	for i from 1 to n-1 do tempmonomial = tempmonomial*(S_i)^(t(i+1)-t(i)-1);
--	temp = append(temp,tempmonomial);
--	);
--    I := ideal(temp);
--    return hilbertSeries I)

	
	

-- constructor for FiniteTotallyOrderedSet objects

OIObject = method()

OIObject ZZ := FiniteTotallyOrderedSet => n -> (
    new FiniteTotallyOrderedSet from toList(1..n)
    )

net FiniteTotallyOrderedSet := (obj) -> (
    "[" | (toString length obj) |"]"
    )

toString FiniteTotallyOrderedSet := (obj) -> (
    toString net obj
    )

OIMorphism = method()

OIMorphism List := OrderPreservingInjectiveFunction => (l) -> (
    new OrderPreservingInjectiveFunction from {
	symbol source => OIObject length l,
	symbol target => OIObject max l,
	symbol values => l
	}
    )

OIMorphism (List,ZZ) := OrderPreservingInjectiveFunction => (l,n) -> (
    new OrderPreservingInjectiveFunction from {
	symbol source => OIObject length l,
	symbol target => OIObject n,
	symbol values => l
	}
    )

net OrderPreservingInjectiveFunction := (epsilon) -> (
    vals := epsilon#(symbol values);
    fold(vals, (x,y) -> (toString x) | (toString y))
    )

-- get source object

source OrderPreservingInjectiveFunction := OIObject => (epsilon) -> (
    epsilon#(symbol source)
    )

-- get target object

target OrderPreservingInjectiveFunction := OIObject => (epsilon) -> (
    epsilon#(symbol target)
    )

-- apply function to integers

OrderPreservingInjectiveFunction ZZ := ZZ => (ep, n) -> (
    ep#(symbol values)_(n-1)
    )

-- function composition

OrderPreservingInjectiveFunction OrderPreservingInjectiveFunction := OrderPreservingInjectiveFunction => (epsilon, tau) -> (
    composedVals := (toList source tau) / (i -> tau i) / (j -> epsilon j);
    new OrderPreservingInjectiveFunction from {
	symbol source => source tau,
	symbol target => target epsilon,
	symbol values => composedVals
	}
    )

-- compare morphisms in OI

OrderPreservingInjectiveFunction ? OrderPreservingInjectiveFunction := (ep, tau) -> (
    if source ep != source tau then (
	symbol incomparable
	)
    else (
	if (target ep != target tau) then (
	    length target ep ? length target tau
	    )
	else (
	    ep#(symbol values) ? tau#(symbol values)
	    )
	)
    )

OIHom = method()

OIHom (FiniteTotallyOrderedSet, FiniteTotallyOrderedSet) := List => (ob1, ob2) -> (
    subsets(toList ob2, length ob1) / (l -> OIMorphism(l,length ob2))
    )

OIHom (ZZ,ZZ) := List => (m,n) -> (
    OIHom(OIObject m, OIObject n)
    )

makeOIAlgebra = method()

makeOIAlgebra Ring := ConstantOIAlgebra => (K) -> (
    new ConstantOIAlgebra from {symbol ring => K}
    )

net ConstantOIAlgebra := (A) -> (
    "The constant OI-algebra determined by "| net A#(symbol ring)
    )

ConstantOIAlgebra ^ List := OIModule => (A,l) -> (
    new OIModule from {
	symbol cache => new MutableHashTable from {},
	symbol numgens => length l,
	symbol widthList => l,
	symbol OIAlgebra => A
	}
    )

OIModule FiniteTotallyOrderedSet := Module => (M,n) -> (
    if (M#(symbol cache) #? n) then (
 	M#(symbol cache) # n
	)
    else (	
	naturalBasis := flatten (M#(symbol widthList) / (w -> sort OIHom(OIObject w,n)));
	nthModuleRank := length naturalBasis;	
	underlyingRing := M#(symbol OIAlgebra)#(symbol ring);
	nthModule := underlyingRing^nthModuleRank;
	nthModule#cache#OIBasis = naturalBasis;
	M#(symbol cache)#n = nthModule;
	nthModule
	)
    )

getOIBasis = method()

getOIBasis Module := List => (M) -> (
    if (M#cache #? OIBasis) then (
	M#cache#OIBasis
	)
    else (
	error "Module does not have a cached OIBasis"
	)
    )

beginDocumentation()

-- front page of documentation

doc ///
    Key    
        OIModules
    Headline
        A Package computations with OIModules
    Description
        Text
	    Big-picture description of package goes here.
///

end


restart
installPackage "OIModules"
FiniteTotallyOrderedSet
OIModuleElement
List
M={{1,OIMorphism({1,2,9})}}
M_0_1
OIMorphism
OIMorphism {1}



m = OIElement M
m
OIMonomials m
for i in m do print i_1
ob1 = OIObject 3
ob2 = OIObject 6
OIHom(ob1, ob2)
ep = OIMorphism {1,2,4}
tau  = OIMorphism {1,3,5,8}


-- operator precedece

-- nets vs strings, printing in matrices

-- coherence w/ type system, class vs parent

-- controlling precedence of operators

-- conflicts between dictionaries

-- some packages are symbols, some are packages

--quit
--installPackage "OIModules"
--M = OIMorphism{1,4,7,11,15,17,18}
--N = OIMorphism({1,2,3,5,7,9,18})
--S = OIElement{{1,M}}
--T = OIElement{{1,N}}
--OIMontoHilbert({S})
--OIMontoHilbert({T})
--OIMontoHilbert({S,T})


-- net function so that the net of A=OIAlg(R) is just "A" (like rings)

-- when to export overloaded binary / unary operators?

-- diff between methodFunction and FunctionClosure

-- keys of hashtables, symbols in various dictionaries, accessor methods

-- net of list of functionVals:

A = makeOIAlgebra (ZZ/2)
M = A^{1,2,4}
ob1 = OIObject 4
F = M ob1
naturalBasis = getOIBasis F
naturalBasis / (e -> net e)


restart
installPackage "OIModules"

ob1 = OIObject 3
ob2 = OIObject 6
l1 = OIHom(ob1, ob1)
l2 = OIHom(ob1, ob2)
l3 = OIHom(ob1, ob2)
ep = OIMorphism({1,2,4})
tau  = OIMorphism {1,3,5,8}

A = makeOIAlgebra (ZZ/2)
M = A^{1,2,4}
ob1 = OIObject 3
M ob1 
objectList = apply(20, i -> OIObject i)
objectList / (n -> rank (N n))

R = ZZ/31991[x]

F=R^3
hashTable { a => 0, b => 1 , c => 2}
F

