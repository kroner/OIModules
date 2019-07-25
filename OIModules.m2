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
    "oiObject",
    "oiMorphism",
    "OIHom",
    "OIElement",
    "OIMonomialtoMonomial",
    "OIMonomials",
    "OIMontoHilbert",
    "Hilb",
    "OIModule",
    "isOIMonomial",
    "makeOIAlgebra",
    "getOIBasis",
    "getOIAlgebra",
    "getWidthList",
    "OIModuleMap",
    "oiModuleMap",
    "getImageGensList"
    }

protect \ {widthList,OIAlgebra,OIBasis,imageGensList,Generators,Relations,isFree}

---------------
-- New types --
---------------

OIObject = new Type of VisibleList
OIMorphism = new Type of HashTable
ConstantOIAlgebra = new Type of HashTable
OIModule = new Type of HashTable
OIModuleElement = new Type of VisibleList
OIModuleMap = new Type of HashTable  

globalAssignment OIModule

-----------------------
-- Type constructors --
-----------------------

-- constructor for OIElements

OIElement = method()

OIElement List := OIModuleElement => L -> (
    new OIModuleElement from L)

OIMonomials = method()

OIMonomials OIModuleElement := List => m -> (
     return for i in m list i_1)
OIModuleElement + OIModuleElement := (a,b) -> (
    temp := {};
    for i in a do(
	tempbool := false;
	for j in b do(
	    if i_1==j_1 then(
		temp = append(temp, {i_0+j_0,i_1});
		tempbool = true;
		);
	    );
	if tempbool == false then(
	    temp = append(temp, i));
	);
    for i in b do(
	tempbool := false;
	for j in a do(
	    if i_1 == j_1 then tempbool = true);
	if tempbool == false then temp = append(temp, i));
    return(OIElement(temp)))

isOIMonomial = m -> #m ==1

OIMonomialtoMonomial = mon->(
    assert(isOIMonomial mon);
    t := mon_0_1;
    m := #(target t);
    n := #(source t);
    R := QQ;--Base(mon);
    x := getSymbol "x";
    S := QQ[x_0..x_n];-- R[x_0..x_n];
    temp :=1;
    if n ==1 then(
	print "here";
	temp= temp*((S_0)^(t(1)-1))*((S_1)^(m-t(1)));
        return {R,temp})
    else(
	temp= temp*(S_0)^(t(1)-1)*(S_n)^(m-t(n));
	for i from 2 to n-1 do temp = temp*(S_i)^(t(i+1)-t(i)-1);
	return {R,temp}))
Hilb = L -> (
    temp := {};
    for i in L do temp = append(temp,OIMonomialtoMonomial i);
    monomiallist := for i in temp list i_1;
    I:= ideal(monomiallist);
    return hilbertSeries I)
    
OIMontoHilbert = L -> (
    for i in L do assert(isOIMonomial i);
    basecase := L_0;
    n :=#source(basecase_0_1);
    R := QQ; --TO BE REPLACED BY RING/FIELD DEPENDING ON MONOMIALS
    x:= getSymbol "x";
    S:=R[x_0..x_n];
    temp :={};
    for mon in L do(
	tempmonomial := 1;
	t := mon_0_1;
	m := #(target t);
	tempmonomial = tempmonomial*(S_0)^(t(1)-1)*(S_n)^(m-t(n));
	for i from 1 to n-1 do tempmonomial = tempmonomial*(S_i)^(t(i+1)-t(i)-1);
	temp = append(temp,tempmonomial);
	);
    I := ideal(temp);
    return hilbertSeries I)
	
	

-- constructor for OIObject objects

oiObject = method()

oiObject ZZ := OIObject => n -> (
    new OIObject from toList(1..n)
    )

net OIObject := (obj) -> (
    "[" | (toString length obj) |"]"
    )

toString OIObject := (obj) -> (
    toString net obj
    )

oiMorphism = method()

oiMorphism List := OIMorphism => (l) -> (
    new OIMorphism from {
	symbol source => oiObject length l,
	symbol target => oiObject max l,
	symbol values => l
	}
    )

oiMorphism (List,ZZ) := OIMorphism => (l,n) -> (
    new OIMorphism from {
	symbol source => oiObject length l,
	symbol target => oiObject n,
	symbol values => l
	}
    )

net OIMorphism := (epsilon) -> (
    vals := epsilon#(symbol values);
    if (length vals == 0) then (
	net 0
	) else (
	if (length vals == 1) then (
	    net vals_0
	    )
    	else (
    	    fold(vals, (x,y) -> (toString x) | (toString y))
	    )
	)
    )

-- get source object

source OIMorphism := oiObject => (epsilon) -> (
    epsilon#(symbol source)
    )

-- get target object

target OIMorphism := oiObject => (epsilon) -> (
    epsilon#(symbol target)
    )

-- apply function to integers

OIMorphism ZZ := ZZ => (ep, n) -> (
    ep#(symbol values)_(n-1)
    )

-- function composition

OIMorphism OIMorphism := OIMorphism => (epsilon, tau) -> (
    composedVals := (toList source tau) / (i -> tau i) / (j -> epsilon j);
    new OIMorphism from {
	symbol source => source tau,
	symbol target => target epsilon,
	symbol values => composedVals
	}
    )

-- compare morphisms in OI

OIMorphism ? OIMorphism := (ep, tau) -> (
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

OIMorphism == OIMorphism := Boolean => (ep, tau) -> (
    if (source ep == source tau and target ep == target tau and ep#(symbol values) == tau#(symbol values)) then (
	true
	) else (
	false
	)
    )

OIHom = method()

OIHom (OIObject, OIObject) := List => (ob1, ob2) -> (
    subsets(toList ob2, length ob1) / (l -> oiMorphism(l,length ob2))
    )

OIHom (ZZ,ZZ) := List => (m,n) -> (
    OIHom(oiObject m, oiObject n)
    )

makeOIAlgebra = method()

makeOIAlgebra Ring := ConstantOIAlgebra => (K) -> (
    new ConstantOIAlgebra from {symbol ring => K}
    )

ring ConstantOIAlgebra := (A) -> A#(symbol ring)

net ConstantOIAlgebra := (A) -> (
    "The constant OI-algebra determined by "| net ring A
    )
buildERing = method(Options=>{MonomialOrder=>Lex,Degrees=>{}})
buildERing (List,List,Ring,ZZ) := o -> (X,s,K,n) -> buildERing((X,s,K),ZZ,n, MonomialOrder=>o.MonomialOrder, Degrees=>o.Degrees)

oiModule = method(Options=>{Generators=>null,Relations=>null})
oiModule(ConstantOIAlgebra,List) := OIModule => o -> (A,l) -> (
    new OIModule from {
	cache => new MutableHashTable from {},
	numgens => length l,
	widthList => l,
	OIAlgebra => A,
	generators => o.Generators,
	relations => o.Relations,
	isFree => o.Generators === null
	}
    )

net OIModule := M -> (
    if M.isFree then "Free OI-module on "|net(M.widthList)
    else "OI-module generated by "|net(M#generators)
    )

ConstantOIAlgebra ^ List := OIModule => (A,l) -> oiModule(A,l)

getWidthList = method()
getWidthList OIModule := List => (M) -> M.widthList

getOIAlgebra = method()
getOIAlgebra OIModule := ConstantOIAlgebra => (M) -> M.OIAlgebra

OIModule ++ OIModule := OIModule => (M,N) -> (
    A := getOIAlgebra M;
    if (ring A =!= ring getOIAlgebra N) then
      error "expected OIModules over the same OIAlgebra";
    oiModule(A, getWidthList M | getWidthList N) 
    )

OIModule OIObject := Module => (M,n) -> (
    if M.cache #? n then M.cache # n
    else (
	phi := M#generators;
	psi := M#relations;
	naturalBasis := flatten (M.widthList / (w -> sort OIHom(oiObject w,n)));
	nthModule := if phi =!= null then image phi oiObject n else (
	    nthModuleRank := length naturalBasis;	
	    underlyingRing := ring getOIAlgebra M;
	    underlyingRing^nthModuleRank
	    );
	if psi =!= null then nthModule = nthModule/(image psi oiObject n);
	nthModule.cache#(symbol OIBasis) = naturalBasis;
	M.cache#n = nthModule;
	nthModule
    	)
    )

OIModule ZZ := Module => (M,n) -> M oiObject n

OIModule OIMorphism := (Matrix) => (M,ep) -> (
    sourceModule := M source ep;
    targetModule := M target ep;
    summandMatrices := M#widthList / (w -> inducedMorphism(ep,w));
    integerMatrix := fold(summandMatrices, (a,b) -> a++b);
    ringMatrix := sub(integerMatrix, ring getOIAlgebra M);
    map(targetModule, sourceModule, ringMatrix)
    )

inducedMorphism = method()

-- given a principle projective P_n and an OImorphism ep, the matrix for the induced map
-- P_n(b) <- P_n(a) (here, ep is a morphisms from [a] to [b])

inducedMorphism (OIMorphism,ZZ) := Matrix => (ep,n) -> (
    sourceBasis := sort OIHom(oiObject n, source ep);
    targetBasis := sort OIHom(oiObject n, target ep);
    matrixEntriesFunction := (i,j) -> (
	if (ep sourceBasis_j == targetBasis_i) then (
	    1
	    ) else (
	    0
	    )
	);
    map(ZZ^(length targetBasis), ZZ^(length sourceBasis), matrixEntriesFunction)
    )

getOIBasis = method()

getOIBasis Module := List => (M) -> (
    if (M.cache #? (symbol OIBasis)) then (
	M.cache# (symbol OIBasis)
	)
    else (
	error "Module does not have a cached OIBasis"
	)
    )

--Add a check that the imageGensList is the same length as the 
--number of generators of M

oiModuleMap = method()
oiModuleMap (OIModule, OIModule, List,ZZ) := OIModuleMap => (M,N,l,n) -> (
    new OIModuleMap from {
	source => M,
	target => N,
	imageGensList => l 
	}
    )

idOI = method()
idOI(OIModule) := OIModuleMap => (M) -> (

getImageGensList = method()

getImageGensList OIModuleMap := List => phi -> phi.imageGensList
source OIModuleMap := phi -> phi.source
target OIModuleMap := phi -> phi.target
    
OIModuleMap ZZ := matrix => (phi, n) -> (
    M := source phi;
    N := target phi;
    if (M n) == 0 then return map(N n, M n, 0);
    if (N n) == 0 then return map(N n, M n, 0);
    vectors := {};
    widths := getWidthList M;
    imageGens := getImageGensList phi;
    for i from 0 to ((length widths)-1) when widths_i < n+1 do (
	maps := OIHom(widths_i, n);
	for j from 0 to ((length maps)-1) do (
	   ep := maps_j;
	   imageEpMatrix := N ep;
	   imageGenMatrix := imageEpMatrix*matrix(imageGens_i);
	   vectors = append(vectors, flatten(entries(imageGenMatrix)));
	   )	
	);
    transpose matrix(ring getOIAlgebra M, vectors)
    )


image OIModuleMap := OIModule => (phi) -> (
    M := target phi;
    oiModule(getOIAlgebra M, getWidthList M, Generators => phi)
    )

coker OIModuleMap := OIModule => (phi) -> (
    M := target phi;
    oiModule(getOIAlgebra M, getWidthList M, Relations => phi)
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

doc ///
    Key
    	oiMorphism
	(oiMorphism,List)
	(oiMorphism,List,ZZ)
    Headline
    	Used for creating morphisms in the category OI.
    Usage
    	epsilon = oiMorphism(images)
	epsilon = oiMorphism(images, n)
    Inputs
    	images:List
	    A list, specifying the images of the elements in the source.
	n:ZZ
	    A non-negative integer specifying the target of the morphism if the one inferred from the list of images is not correct.
    Outputs
    	epsilon:OIMorphism
    Description
    	Text
    	    A morphism $\epsilon: [n] \rightarrow [m]$ in the category OI is determined by the list of values $\{\epsilon(1), \epsilon(2), \ldots, \epsilon(n)\}$ as well as the target $[m]$. The constructor OIMorphism takes inputs specifying these data and produces @ofClass OIMorphism@. If a target is not specified, the minimal target is inferred from the list of images.
	Example
	    epsilon = oiMorphism({1,4,5}, 7)
	    tau = oiMorphism({1,3,4,5,7,8,9})
	Text
	    One can ask for the source or target of @ofClass OIMorphism@. Morphisms can be composed if their sources and targets are compatible, and they can be applied to @ofClass ZZ@ in their domain.
	Example
	    target epsilon
	    source tau
	    tau	epsilon
	    epsilon 2
    	Text
	    The collection of all OIMorphisms between two OIObjects can be found using OIHom
	Example
	    sourceObj = oiObject 2;
	    targetObj = oiObject 4;
	    OIHom (sourceObj, targetObj)
        Text
	    The net used to represent @ofClass OIMorphism@ is the strings representing the images of the function, concatenated in order. This can lead to notational ambiguities where distinct morphism are printed with identical strings.
	Example
	    epsilon1 = oiMorphism {1,2,3,4}
	    epsilon2 = oiMorphism ({1,2,3,4},5)
	    epsilon3 = oiMorphism {12,34}
	    epsilon4 = oiMorphism {1,234}
	Text
	    Such concise notation was chosen because these objects are typically used as indices for @ofClass IndexedVariable@, where their primary purpose is bookkeeping for OI-algebras.
///

end


restart
installPackage "OIModules"
OIObject
OIModuleElement
List
M={{1,oiMorphism({1,2,9})}}
M_0_1
oiMorphism
oiMorphism {1}



m = OIElement M
m
OIMonomials m
for i in m do print i_1
ob1 = oiObject 3
ob2 = oiObject 6
OIHom(ob1, ob2)
ep = oiMorphism {1,2,4}
tau  = oiMorphism {1,3,5,8}


-- operator precedece

-- nets vs strings, printing in matrices

-- coherence w/ type system, class vs parent

-- controlling precedence of operators

-- conflicts between dictionaries

-- some packages are symbols, some are packages

--quit
--installPackage "OIModules"
--M = oiMorphism{1,4,7,11,15,17,18}
--N = oiMorphism({1,2,3,5,7,9,18})
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

A = makeOIAlgebra (ZZ/101[x,y,z])
M = A^{1,2,4}
ep = oiMorphism({1,2,4})
M ep
ob1 = oiObject 4
F = M ob1
naturalBasis = getOIBasis F
naturalBasis / (e -> net e)


-- net problem example:

restart
installPackage "OIModules"

R = QQ[x,y]
A = makeOIAlgebra (R)
F = A^{1,2,4}

tau  = oiMorphism({1,3,4},5)
getOIBasis(F 5)
F tau
-- you can look at the modules you get by applying F to the first few values:

testList := OIHom(4,5)

apply(testList, i -> F i)

-- or get a particular one:

ob3 = oiObject 5
M = F ob3 

-- now M is almost an ordinary M2 object.
-- But it has one new thing added to M.cache: a symbol, called OIBasis, which
-- records a list of morphisms in OI, used for bookkeeping the standard basis for M.

-- however, this list of OImorphisms can't be printed nicely  (claiming a time limit was reached):

basisList = getOIBasis M

-- despite this seeming to work:

basisList / (e -> net e)

-- also, I can no longer peek at the cache of M ??

restart
installPackage "OIModules"
viewHelp oiMorphism

R = ZZ/101[x,y,z]
A = makeOIAlgebra (R)
M = A^{2,3}
N = A^{1,2}
N 2
g1 = map(N 2, R^1, transpose matrix {{x,y,z}})
g2 = map(N 3, R^1, transpose matrix {{x^2,0,y^2,0,z^2,0}})

l = {entries g1,entries g2}
phi = oiModuleMap(M,N,l,0)

phi 1
phi 2
phi 3
phi 4
phi 5
