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
    "ConstantOIAlgebra",
    "oiMonomialsToHilbert",
    "OIInitial",
    "OIObject",
    "OIMorphism",
    "OIHom",
    "MaxOIMon",
    "OIElement",
    "OIModuleElement",
    "OIMonomialtoMonomial",
    "OIMonomials",
    "OIMontoHilbert",
    "Hilb",
    "OIModule",
    "isOIMonomial",
    "OIDivides",
    "OIDivider",
    "makeOIAlgebra",
    "OICleaner",
    "OIGCD",
    "OILCM",
    "OIDivisionAlgorithm",
    "getOIBasis",
    "OISPairs",
    "OIGroebner",
    "OIDivideList",
    "getOIAlgebra",
    "getWidthList",
    "oiModuleMap",
    "getImageGensList",
    "idOI"
    }

protect \ {widthList,OIAlgebra,OIBasis,imageGensList,Generators,Relations,isFree}

---------------
-- New types --
---------------

OIObject = new Type of VisibleList
OIMorphism = new Type of HashTable
OIModule = new Type of HashTable
OIModuleElement = new Type of VisibleList
OIModuleMap = new Type of HashTable  

ConstantOIAlgebra = new Type of MutableHashTable
ConstantOIAlgebra.synonym = "constant OI-Algebra"
ConstantOIAlgebra.GlobalAssignHook = globalAssignFunction
ConstantOIAlgebra.GlobalReleaseHook = globalReleaseFunction
-----------------------
-- Type constructors --
-----------------------
--Has Construction of OIElements

OIElement = method()

OIElement HashTable := OIModuleElement => H ->(
    new OIModuleElement from H)

OICleaner = m ->(
    templist :={};
    for i in keys m do(
	if m#i !=0 then templist = append(templist,{i,m#i}));
    return OIElement(hashTable(templist)))

OIModuleElement == OIModuleElement := (a,b) ->(
    tempbool:=true;
    if keys a != keys b then tempbool = false
    else for i in keys a  when tempbool == true do(
	if a#i != b#i then tempbool = false);
    return tempbool) 


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
    return OICleaner(OIElement temphash))
    
ZZ*OIModuleElement := (a,b) -> (OIElement(hashTable(for i in keys b list {i,a*b#i})))
QQ*OIModuleElement := (a,b) -> (OIElement(hashTable(for i in keys b list {i,a*b#i})))
RingElement*OIModuleElement := (a,b) -> (OIElement(hashTable(for i in keys b list {i,a*b#i})))

OIModuleElement - OIModuleElement := (a,b) -> a+((-1)*b)

OIDivides = (a,b) ->(
    if #(source a)!= #(source b) then( 
    return false)
    else if b(1) < a(1) then( 
	return false)
    else(
	tempbool:=true;
	for i from 1 to (#(source b)-1) do(
	    if b(i+1)-b(i) < a(i+1)-a(i) then(
		tempbool = false));
	if #(target b) - b(#source b) < #(target a) - a(#source a) then tempbool = false;
	return tempbool))

OIDivider = (a,b) ->(
    assert(OIDivides(a,b));
    temptarget := #(target b);
    tempfull := toList(1..temptarget);
    templist := {};
    tempbig:={};
    tempsource :=toList(1..#(source a));
    for i from 1 to #(source a) do(
	templist = append(templist,{a(i),b(i)});
	tempfull = delete(b(i),tempfull);
	tempsource = delete(a(i),tempsource));
    temphash:= hashTable(templist);
    for i in tempsource do(
	if i==1 then templist = append(templist,{i,tempfull_0})
	else(
	    tempbig={};
	    for j in tempfull do(
		if j>temphash#(i-1) then tempbig = append(tempbig,j));
	    templist = append(templist,{i,tempbig_0}));
	temphash = hashTable templist);
    tempmorph := for i in keys temphash list temphash#i;
    return OIMorphism(tempmorph,temptarget))
    
OrderPreservingInjectiveFunction*OIModuleElement := (a,b) ->(
    temp:={};
    for i in keys b do(
	temp = append(temp,{a i,b#i}));
    return OIElement(hashTable(temp)))
MaxOIMon = L ->(
    temp :=L_0;
    for i in L do if i>temp then temp = i;
    return temp)	

OIInitial = m -> MaxOIMon OIMonomials m

 
 
 
OIDivisionAlgorithm = (m,L) ->(
    tempbool := false;
    init:=0;
    dummy:=m;
    divider :=0;
    remain := 0;
    templist:={};
    initialL := for i in L list {i,OIInitial i};
    for i in initialL when (not tempbool) do(
	for k in (keys m) when (not tempbool) do(
	    if OIDivides(i_1,k) then tempbool = true));
    while tempbool == true and #(keys dummy)>0 do(
	--print("INHERE");
	templist={};
	for k in keys dummy do(
	    for i in initialL do(
		if OIDivides(i_1,k) then templist=append(templist,k)));
	--print("NEXT COMMENT");
	init=MaxOIMon templist;
	for i in initialL do(
	    if OIDivides(i_1,init) then(
		divider = i_0;
		break));
--	print("COEFFICIENT",dummy#init/divider#(OIInitial divider));
--	print(OIInitial(divider),source OIInitial(divider), target OIInitial(divider),init, source init, source init);	
--	print("DIVIDED",(OIDivider(OIInitial(divider),init))*divider);
--	print("FIRST",OIDivider(OIInitial(divider),init));
--	print("OIINITDIVIDER",OIInitial(divider),source OIInitial(divider),target OIInitial(divider) );
--	print("INIT",init,source init,target init);
--	print(dummy#init/divider#(OIInitial divider))*(OIDivider(OIInitial divider,init)*divider);
	dummy = dummy - (dummy#init/divider#(OIInitial divider))*(OIDivider(OIInitial divider,init)*divider);
--        print("DUMMY",dummy);
	tempbool = false;
	for i in initialL when (not tempbool) do(
	    for k in (keys dummy) when (not tempbool) do(
	        if OIDivides(i_1,k) then tempbool = true));	
	);
    return dummy)



OIDivideList = (a,b) ->(
    temp:={};
    for i in OIHom(target a, target b) do(
	if (i a) ==b then temp = append(temp, i));
    return temp)


OIGCD = (a,b) ->(
    tempa:={a(1)-1};
    tempb:={b(1)-1};
    temp:={};
    tempreturn:={};
    for i from 1 to (#(source a)-1) do(
	tempa = append(tempa,a(i+1)-a(i)-1);
	tempb = append(tempb,b(i+1)-b(1)-1));
    tempa = append(tempa,#target(a) - a(#(source a)));
    tempb = append(tempb,#target(b) - b(#(source b)));
    for i from 0 to (#tempa-1) do temp = append(temp,min(tempa_i,tempb_i));
    tempreturn = {temp_0+1};
    for i from 1 to (#temp-2) do(
        tempreturn = append(tempreturn,temp_i+tempreturn_(i-1)+1));
    return OIMorphism(tempreturn,temp_(#temp-1)+tempreturn_(#tempreturn-1)))
    
OILCM = (a,b) ->(
    tempa:={a(1)-1};
    tempb:={b(1)-1};
    temp:={};
    tempreturn:={};
    for i from 1 to (#(source a)-1) do(
	tempa = append(tempa,a(i+1)-a(i)-1);
	tempb = append(tempb,b(i+1)-b(1)-1));
    tempa = append(tempa,#target(a) - a(#(source a)));
    tempb = append(tempb,#target(b) - b(#(source b)));
    for i from 0 to (#tempa-1) do temp = append(temp,max(tempa_i,tempb_i));
    tempreturn = {temp_0+1};
    for i from 1 to (#temp-2) do(
        tempreturn = append(tempreturn,temp_i+tempreturn_(i-1)+1));
    return OIMorphism(tempreturn,temp_(#temp-1)+tempreturn_(#tempreturn-1)))

OISPairs = (a,b)->(
    temp :={};
    inita:=OIInitial a;
    initb:=OIInitial b;
    tempmon := OILCM(inita,initb);
    tempa := OIDivideList(inita,tempmon);
    tempb := OIDivideList(initb,tempmon);
    --print(tempa,tempb);
    --print(tempmon);
    for i in tempa do(
	for j in tempb do(
	    temp = append(temp,(b#initb)*(i*a) - (a#inita)*(j*b))));
    return toList(set(temp))) 
OIGroebner = L ->(								       
    Grob:= L;									       
    tempGrob:={};								       
    SPolys:= {};								       
    while Grob != tempGrob do(							       
	--print(Grob,tempGrob);							       
	SPolys = {};								       
	tempGrob = Grob;							       
	for i in tempGrob do(							       
	    for j in tempGrob do(						       
		if i!=j then for k in OISPairs(i,j) do(				       
		    SPolys = append(SPolys,k))));				       
	for i in SPolys do(							       
	    if keys(OIDivisionAlgorithm(i,tempGrob)) !={} then Grob = append(Grob,i)));
    return(Grob))								       

		     
        
oiMonomialsToHilbert = L ->(
    basecase:= L_0;
    basemorphism := (keys basecase)_0;
    n := #source basemorphism;
    R := QQ; --TO BE REPLACED BY ARBITRARY RING
    x := getSymbol "x";
    S := R[x_0..x_n];
    temp := {};
    for mon in L do(
	tempmonomial :=1;
	t := (keys mon)_0;
	m := #(target t);
	tempmonomial = tempmonomial*(S_0)^(t(1)-1)*(S_n)^(m-t(n));
	for i from 1 to n-1 do tempmonomial = tempmonomial*(S_i)^(t(i+1)-t(i)-1);
	temp = append(temp,tempmonomial);
	);
    I := ideal(temp);
    return hilbertSeries I)
    
    
-- constructor for OIElements

OrderPreservingInjectiveFunction == OrderPreservingInjectiveFunction := (a,b) ->(
    if #(source a) != #(source b) then return false
    else if #(target a)!= #(target b) then return false
    else(
	tempbool := true;
	for i from 1 to #(source a) do(
	    if a(i) != b(i) then tempbool = false);
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

	
	

-- constructor for OIObject objects

oiObject = method()
oiObject ZZ := OIObject => n -> (
    new OIObject from toList(1..n)
    )
oiObject OIObject := OIObject => obj -> obj

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

source OIMorphism := OIObject => (epsilon) -> (
    epsilon#(symbol source)
    )

-- get target object

target OIMorphism := OIObject => (epsilon) -> (
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
	if psi =!= null then nthModule = nthModule/image(psi n);
	nthModule.cache#(symbol OIBasis) = naturalBasis;
	M.cache#n = nthModule;
	nthModule
    	)
    )

OIModule ZZ := Module => (M,n) -> M (oiObject n)

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
oiModuleMap (OIModule, OIModule, List) := OIModuleMap => (M,N,l) -> (
    new OIModuleMap from {
	source => N,
	target => M,
	imageGensList => l 
	}
    )

idOI = method()
idOI(OIModule) := OIModuleMap => (M) -> (
    R := ring getOIAlgebra M;
    l := apply(M.widthList, i -> matrix{{1_R}});
    oiModuleMap(M,M,l)
    )

getImageGensList = method()

getImageGensList OIModuleMap := List => phi -> phi.imageGensList
source OIModuleMap := phi -> phi#source
target OIModuleMap := phi -> phi#target

OIModuleMap ZZ := matrix => (phi, n) -> phi (oiObject n)

OIModuleMap OIObject := matrix => (phi, obj) -> (
    n := length obj;
    M := target phi;
    N := source phi;
    if (M n) == 0 then return map(M n, N n, 0);
    if (N n) == 0 then return map(M n, N n, 0);
    vectors := {};
    widths := getWidthList N;
    imageGens := getImageGensList phi;
    for i from 0 to ((length widths)-1) when widths_i < n+1 do (
	maps := sort OIHom(widths_i, n);
	for j from 0 to ((length maps)-1) do (
	   ep := maps_j;
	   imageEpMatrix := M ep;
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

doc ///
    Key
    	oiModuleMap
    Headline
    	Used for creating a map between free OI-modules.
    Usage
    	phi = oiModuleMap(M,N,v)
    Inputs
    	M:OIModule
	    A free OI-module specifying the source of the map
	N:OIModule
	    A free OI-module, over the same OI-algebra as M, specifying the target of the map
	l:List
	    A list of vectors specifying the images of each of the generators of M.
    Outputs
    	phi:OIModuleMap
    Description
    	Text
    	    A map $\phi: M \rightarrow N$ between free OI-modules is determined by the list of vectors $\{v_1, v_2, \ldots, v_n\}$. The constructor oiMap takes inputs specifying the modules and vectors and produces an object of @ofClass OIModuleMap@.
	Example
	    R = ZZ/101[x,y,z]
	    A = makeOIAlgebra (R)
	    M = A^{2,3}
	    N = A^{1,2}
	    v1 = transpose (matrix {{1,0,1}})
	    v2 = transpose (matrix {{x^2,0,y^2,0,z^2,0}})
	    phi = oiModuleMap(M,N,{v1,v2})
	Text
	    One can ask for the source or target of @ofClass OIModuleMap@. One can also get the list of vectors specifying the images of the generators of the source free module.
	Example
	    source phi
	    target phi
	    getImageGensList phi
        
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

R = ZZ/31991[x,y]
A = makeOIAlgebra (R)

M = A^{2,3,5}
N = A^{1,1,2}
idOI N
N 2
g1 = random(N 2, R^1)
g2 = random(N 3, R^1)
g3 = random(N 5, R^1)

phi = oiModuleMap(N,M,{g1, g2, g3})

phi 1
phi 2
phi 3
phi 4
phi 5
