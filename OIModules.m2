-*- coding: utf-8 -*-

newPackage( "OIModules",
    Version => "0.1.0",
    Date => "July 22, 2019",
    Authors => {
	{Name => "Nathan Fieldsteel",
	    Email => "nathan.fieldsteel@uky.edu"},
	{Name => "Tom Grubb",
	    Email => "tgrubb@ucsd.edu"},
	{Name => "Robert Krone",
	    Email => "rckrone@ucdavis.edu"},
	{Name => "Erica Musgrave",
	    Email => "erica.musgrave@huskers.unl.edu"},
	{Name => "Jonathan Niño",
	    Email => "ninojonathan4@gmail.com"},
	{Name => "Steven Sam",
	    Email => "ssam@ucsd.edu"}
	},
    HomePage => "https://nathanfieldsteel.github.io",
    Headline => "A package for computations with OI-algebras and modules over OI-algebras",
    AuxiliaryFiles => false)

export {
    "oiObject",
    "OIObject",
    "oiMorphism",
    "OIMorphism",
    "oiAlgebra",
    "OIAlgebra",
    "oiModule",
    "OIModule",
    "oiModuleMap",
    "OIModuleMap",
    
    "OIHom",
    "getOIBasis",
    "getWidthList",
    "getImageGensList",
    "idOI",
    "Generators",
    "Relations",

    "oiMonomialsToHilbert",
    "OIInitial",
    "OIGCD",
    "repToHilb",
    "OILCM",
    "OIGroebner",
    "OIElement",
    "OIMonomialtoMonomial",
    "OIMonomials",
    "OIMontoHilbert",
    "Hilb",
    "isOIMonomial",
    "OIgb"
    }

protect \ {widthList,OIAlg,OIBasis,imageGensList,isFree}

---------------
-- New types --
---------------

OIObject = new Type of VisibleList
OIMorphism = new Type of HashTable
OIModule = new Type of HashTable
OIModuleElement = new Type of HashTable
OIModuleMap = new Type of HashTable  

OIAlgebra = new Type of MutableHashTable
OIAlgebra.synonym = "constant OI-Algebra"
OIAlgebra.GlobalAssignHook = globalAssignFunction
OIAlgebra.GlobalReleaseHook = globalReleaseFunction

-----------------------
-- Type constructors --
-----------------------

-- constructor for OIElements

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

OIMorphism*OIModuleElement := (a,b) ->(
    temp:={};
    for i in keys b do(
	temp = append(temp,{a i,b#i}));
    return OIElement(hashTable(temp)))

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
    return oiMorphism(tempmorph,temptarget))
    
oiInitialTerms = L->(
    temp:={};
    for i in L do(
	temp = append(temp,OIElement(hashTable{{OIInitial i,1}})));
    return temp)

repToHilb = L->oiMonomialsToHilbert(oiInitialTerms(OIGroebner(L)))

    
MaxOIMon = L ->(
    temp :=L_0;
    for i in L do if i>temp then temp = i;
    return temp)
    
OIInitial = m -> MaxOIMon OIMonomials m

OIDivideList = (a,b) ->(
    temp:={};
    for i in OIHom(target a, target b) do(
	if (i a) ==b then temp = append(temp, i));
    return temp)

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
--	print("OIINITDIVIDER",OIInitial(divider),source OIInitial(divider),target OIInitial(divider) );
--	print("INIT",init,source init,target init);
	Lemon := OIInitial divider;
	Apple := init;
	dummy = dummy - (dummy#init/divider#(OIInitial divider))*(((OIDivideList(Lemon,Apple))_0)*divider);
	tempbool = false;
	for i in initialL when (not tempbool) do(
	    for k in (keys dummy) when (not tempbool) do(
	        if OIDivides(i_1,k) then tempbool = true));	
	);
    return dummy)
    
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
    return oiMorphism(tempreturn,temp_(#temp-1)+tempreturn_(#tempreturn-1)))
    
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
    return oiMorphism(tempreturn,temp_(#temp-1)+tempreturn_(#tempreturn-1)))



oiSyzZero = (a,b) -> (         --EVENTUALLY SHOULD REMOVE DUPLICATES I.E. SYZ0 SHOULDNT HAVE (f,g) and (g,f)
    mona := (keys a)_0;
    monb := (keys b)_0;
    temp:={};
    newtemp := {};
    tempbool := false;
    targetstart := max(#(target mona),#(target monb));
    maxtarget := #(target mona)+#(target monb)-#(source mona);
    for i from targetstart to maxtarget do(
	for h in OIHom(#(target mona),i) do(
	    for h' in OIHom(#(target monb), i) do(
	            if h*a == h'*b then temp = append(temp, (h,h')))));
    for k from 1 to #temp do(
	tempbool = false;
	h := temp_(-k)_0;
	for l from 0 to #temp-k-1 do(
	    f:=temp_l_0;
	    for morph in OIHom(target f,target h) do(
		if (morph temp_l_0,morph temp_l_1)== temp_(-k) then tempbool = true));
	if not tempbool then newtemp = append(newtemp,temp_(-k)));
    return newtemp)

OISPairs = (a,b)->(
    temp :={};
    inita:=OIInitial a;
    initb:=OIInitial b;
    tempsyz:=oiSyzZero(OIElement(hashTable{{inita,1}}),OIElement(hashTable{{initb,1}}));
    for i in tempsyz do(
	temppair := (b#initb)*(i_0*a) - (a#inita)*(i_1*b);
	if #(keys temppair)>0 then temp = append(temp,(b#initb)*(i_0*a) - (a#inita)*(i_1*b)));
    return toList(set(temp)))     

OIGroebner = L ->(								       
    Grob:= L;									       
    tempGrob:={};								       
    SPolys:= {};								       
    calculated:={};
    while Grob != tempGrob do(							       
	--print(Grob,tempGrob);							       
	SPolys = {};								       
	tempGrob = Grob;
	tempbool := true;
--    	print(target((keys(Grob_(-1)))_0));
	print(Grob);
--	for i in Grob do print(i,target (keys i)_0);
	--print(calculated);
	for i in tempGrob do(							       
	    for j in tempGrob do(
		if not member({i,j},calculated) and not member({j,i},calculated) then(			       
		    calculated = append(calculated,{i,j});
		    for k in OISPairs(i,j) do(				       
		    	SPolys = append(SPolys,k)))));				       
--	print("NUMBER OF",#SPolys);
	for i in SPolys do(
	    tempbool = true;
--	    print("BEFORE DIVISION",i,Grob);
	    Lemon := OIDivisionAlgorithm(i,Grob);
--	    print("AFTER DIVISION");				       
--    	    print Lemon;
	    if keys(Lemon) !={} and not member(OIInitial Lemon,Grob/OIInitial) then(
		for Apple in Grob do(
		    if OIDivides(OIInitial Apple,OIInitial Lemon) then tempbool = false);
		if tempbool == true then Grob = append(Grob,(1/Lemon#(OIInitial Lemon))*Lemon))));
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
    T := S^{-n};
    return hilbertSeries (I*T))

-*OrderPreservingInjectiveFunction == OrderPreservingInjectiveFunction := (a,b) ->(
    if #(source a) != #(source b) then return false
    else if #(target a)!= #(target b) then return false
    else(
	tempbool := true;
	for i from 1 to #(source a) do(
	    if a(i) != b(i) then tempbool = false);
	return tempbool))   *-

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

oiAlgebra = method()
oiAlgebra Ring := OIAlgebra => (K) -> (
    new OIAlgebra from {symbol ring => K}
    )

ring OIAlgebra := (A) -> A#(symbol ring)

OIAlgebra OIObject := Ring => (A,n) -> ring A

oiModule = method(Options=>{Generators=>null,Relations=>null})
oiModule(OIAlgebra,List) := OIModule => o -> (A,l) -> (
    new OIModule from {
	cache => new MutableHashTable from {},
	numgens => length l,
	widthList => l,
	OIAlg => A,
	generators => o.Generators,
	relations => o.Relations,
	isFree => (o.Generators === null and o.Relations === null)
	}
    )

net OIModule := M -> (
    if M.isFree then "Free OI-module on "|net(M.widthList)
    else "OI-module generated by "|net(M#generators)
    )

gens OIModule := o -> M -> (
    if M#generators =!= null then M#generators else idOI(M)
    )

OIAlgebra ^ List := OIModule => (A,l) -> oiModule(A,l)

getWidthList = method()
getWidthList OIModule := List => (M) -> M.widthList

oiAlgebra OIModule := OIAlgebra => (M) -> M.OIAlg

OIModule ++ OIModule := OIModule => (M,N) -> (
    A := oiAlgebra M;
    if (ring A =!= ring oiAlgebra N) then
      error "expected OIModules over the same OIAlgebra";
    oiModule(A, getWidthList M | getWidthList N) 
    )

OIModule OIObject := Module => (M,n) -> (
    if M.cache #? n then M.cache # n
    else (
	phi := M#generators;
	psi := M#relations;
	R := ring oiAlgebra M;
	naturalBasis := flatten (M.widthList / (w -> sort OIHom(oiObject w,n)));
	nthModule := R^(length naturalBasis);
	relsmat := if psi =!= null then (psi n) else map(nthModule,R^0,0); 
	relsmat = map(nthModule,target relsmat,id_(target relsmat))*relsmat;
        if phi =!= null then (
	    gensmat := (phi n);
	    gensmat = map(nthModule,target gensmat,id_(target gensmat))*gensmat;
	    nthModule = subquotient(nthModule,gensmat,relsmat);
	    ) else
	nthModule = nthModule/image relsmat;
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
    ringMatrix := sub(integerMatrix, ring oiAlgebra M);
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
    R := ring oiAlgebra M;
    l := for i from 0 to #M.widthList-1 list flatten for j from 0 to #M.widthList-1 list (
	k := #OIHom(oiObject M.widthList#j, oiObject M.widthList#i);
	toList (k: if i==j then 1_R else 0_R)
	);
    l = apply(l, L -> transpose matrix{L});    
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
    R := ring oiAlgebra M;
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
	   m := map(source imageEpMatrix, target imageGens_i, id_(target imageGens_i));
	   imageGenMatrix := imageEpMatrix*m*matrix(imageGens_i);
	   vectors = append(vectors, flatten(entries(imageGenMatrix)));
	   )	
	);
    transpose matrix(ring oiAlgebra M, vectors)
    )


image OIModuleMap := OIModule => (phi) -> (
    M := target phi;
    oiModule(oiAlgebra M, getWidthList M, Generators => phi, Relations => M#relations)
    )

coker OIModuleMap := OIModule => (phi) -> (
    M := target phi;
    A := oiAlgebra M;
    rels := if M#relations =!= null then (
	oiModuleMap(M,(source rels)++(source phi),(getImageGensList rels)|(getImageGensList phi))
	) else phi;
    oiModule(oiAlgebra M, getWidthList M, Generators => M#generators, Relations => rels)
    )

OIgb = method()
OIgb(OIModule) := M -> (
    A := oiAlgebra M;
    R := ring A;
    Mgens := gens M;
    G := getImageGensList Mgens; -- partial GB
    widths := getWidthList source Mgens;
    k := min widths;
    lastnewk := k;
    while k < 2*lastnewk do (
	Mkgb := gens gb (Mgens k); -- gb of M k
	inMk := leadComponent Mkgb; -- initial term positions of M k
    	Gmap := oiModuleMap(target Mgens, A^widths, G);
	inGk := leadComponent Gmap k; -- what inG generates in width k
	-- check if each initial term of M k is in inGk. if not, it's added to G.
	for i from 0 to #inMk-1 do (
	    if not member(inMk#i, inGk) then (
		G = append(G,Mkgb_{i});
		widths = append(widths,k);
		lastnewk = k;
		);
	    );
	k = k+1;
	);
    oiModuleMap(target Mgens, A^widths, G)
    )

kernel OIModuleMap := o -> (phi) -> (
    M := source phi;
    N := target phi;
    A := oiAlgebra M;
    idGens := getImageGensList(idOI M);
    phiGens := getImageGensList(phi);
    graphGens := apply(#phiGens, i->(idGens#i)||(phiGens#i));
    graphMap := oiModuleMap(M++N, M, graphGens);
    G := OIgb image graphMap;
    Gwidths := getWidthList (source G);
    Ggens := getImageGensList G;
    GelimIndices := select(#Ggens, i->(
	    k := position(flatten entries Ggens#i, i -> i != 0, Reverse => true);
	    k < numgens(M (Gwidths#i))
	    ));
    Gelim := apply(GelimIndices, i->Ggens#i);
    Gelimwidths := apply(GelimIndices, i->Gwidths#i);
    image oiModuleMap(M, A^Gelimwidths, Gelim)
    )

--composition of oiModuleMaps

OIModuleMap*OIModuleMap := OIModuleMap => (psi, phi) -> (
    vectors := getImageGensList phi;
    M := source phi;
    widthsSource := getWidthList M;
    newVectors := {};
    for i from 0 to ((length vectors)-1) do (
	newVectors = append(newVectors, (psi widthsSource_i)*vectors_i) 
	);    
    oiModuleMap(target psi, M, newVectors)
    )

beginDocumentation()
multidoc ///
-- front page of documentation
Node
    Key    
        OIModules
    Headline
        A Package computations with OIModules
    Description
        Text
	    Big-picture description of package goes here.
	    
Node 
     Key
          OIObject
	  (net,OIObject)
	  (toString,OIObject)
     Headline
          the class ordered finite sets
     Description
          Text
	       A finite ordered set, represented by the integers from 1 to n.
	       These are the objects of the category OI.  Therefore an OIModule
	       maps OIObjects to modules.  An OIModuleMap maps OIObjects to
	       module maps.
	  Example
	       A = oiAlgebra QQ
	       M = A^{1,2}
	       obj = oiObject 3
	       M obj

Node
    Key
    	oiObject
	(oiObject,ZZ)
	(oiObject,OIObject)
    Headline
        constructor for OIObject
    Usage
    	obj = oiObject(n)
    Inputs
	n:ZZ
    Outputs
    	obj:OIObject
    Description
    	Text
    	    Creates an OIObject representing an ordered set with n elements.

Node 
    Key
        OIMorphism
	(source,OIMorphism)
      	(target,OIMorphism)
	(net,OIMorphism)
	(symbol SPACE,OIMorphism,ZZ)
	(symbol SPACE,OIMorphism,OIMorphism)
	(symbol ==,OIMorphism,OIMorphism)
	(symbol ?,OIMorphism,OIMorphism)
    Headline
        the class of injective order-preserving maps
    Description
        Text
	    A map between two finite ordered sets that is injective and order-preserving.
	    These are the morphisms of the category OI.  Therefore OIModule maps
	    OIMorphisms to module maps.
	Text
	    One can ask for the source or target of @ofClass OIMorphism@. Morphisms can be 
	    composed if their sources and targets are compatible, and they can be applied 
	    to @ofClass ZZ@ in their domain.
	Example
	    epsilon = oiMorphism({1,4,5}, 7)
	    tau = oiMorphism({1,3,4,5,7,8,9})
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
	    The net used to represent @ofClass OIMorphism@ is the strings representing the 
	    images of the function, concatenated in order. This can lead to notational 
	    ambiguities where distinct morphism are printed with identical strings.
	Example
	    epsilon1 = oiMorphism {1,2,3,4}
	    epsilon2 = oiMorphism ({1,2,3,4},5)
	    epsilon3 = oiMorphism {12,34}
	    epsilon4 = oiMorphism {1,234}
	Text
	    Such concise notation was chosen because these objects are typically used as 
	    indices for @ofClass IndexedVariable@, where their primary purpose is bookkeeping 
	    for OI-algebras.


Node
    Key
    	oiMorphism
	(oiMorphism,List)
	(oiMorphism,List,ZZ)
    Headline
        constructor for OIMorphism
    Usage
    	epsilon = oiMorphism(images)
	epsilon = oiMorphism(images, n)
    Inputs
    	images:List
	    A list, specifying the images of the elements in the source.
	n:ZZ
	    A non-negative integer specifying the target of the morphism if the one 
	    inferred from the list of images is not correct.
    Outputs
    	epsilon:OIMorphism
    Description
    	Text
    	    A morphism $\epsilon: [n] \rightarrow [m]$ in the category OI is determined 
	    by the list of values $\{\epsilon(1), \epsilon(2), \ldots, \epsilon(n)\}$ as 
	    well as the target $[m]$. The constructor takes inputs specifying 
	    these data and produces @ofClass OIMorphism@. If a target is not specified, 
	    the minimal target is inferred from the list of images.
	Example
	    epsilon = oiMorphism({1,4,5}, 7)
	    tau = oiMorphism({1,3,4,5,7,8,9})
	

Node 
    Key
        OIAlgebra
	(ring,OIAlgebra)
	(symbol SPACE,OIAlgebra,OIObject)
    Headline
        the class of OI-algebras
    Description
        Text
	    An OIAlgebra is a functor from OI to algebras.
	    
	    Currently only constant OI-algebras are supported.  This means every
	    finite ordered set maps to the same algebra.  OI-algerbas can have
	    modules defined over them
	Example
	    R = QQ[x,y]
	    A = oiAlgebra R
	    M = A^{2}
	    M 3

Node
    Key
    	oiAlgebra
	(oiAlgebra,Ring)
	(oiAlgebra,OIModule)
    Headline
        constructor for OIAlgebra
    Usage
        A = oiAlgebra(R)
    Inputs
    	R:Ring
    Outputs
    	A:OIAlgebra
	    a constant OI-algebra
    Description
    	Text
    	    Produces the constant OI-algebra that maps every OIObject to algebra R.
        Example
	    R = QQ[x,y]
	    A = oiAlgebra R
	    obj = oiObject 3
	    A obj
	    
Node 
    Key
        OIModule
	(net,OIModule)
	(symbol SPACE,OIModule,OIObject)
	(symbol SPACE,OIModule,ZZ)
	(symbol SPACE,OIModule,OIMorphism)
	(symbol ++,OIModule,OIModule)
	(generators,OIModule)
    Headline
        the class of modules over OI-algebras
    Description
        Text
	    An OIModule represents a module over an OI-algebra A, which is a functor M from
	    finite ordered sets to modules, where each M(S) is an A(S)-module. 
	    
	    A principal projective module over A generated in width n is the module
	    in which M(S) is the free A(S)-module generated by the set of OI morphisms
	    (injective order-preserving maps) from [n] to S.  A direct sum of principal
	    projectives is constructed as follows.
	Example
	    R = ZZ/31991
	    A = oiAlgebra(R)
	    M = A^{2}
	    M 3
	Text
	    An OIModule is itself a functor from OI to modules, so it can be applied
	    to an OIMorphism to produce a map between modules.
	Example
	    rho = oiMorphism({1,2,4})
	    M rho
	Text
	    Every finitely generated module over A is a subquotient of a finite direct
	    sum of principal projectives.  Submodules and quotient modules can be defined
	    as the images or kernels of OIModuleMaps.
	Example
	    N = A^{1}
	    phi = oiModuleMap(N,M,{matrix{{1_R},{1}}})
	    P = image phi
	    generators P
	    Q = kernel phi
	Text
	    We can also take direct sums of OIModules
	Example
	    S = M ++ P
	    S 3

Node
    Key
    	oiModule
	(oiModule,OIAlgebra,List)
	(symbol ^,OIAlgebra,List)
	Generators
	Relations
	[oiModule,Generators]
	[oiModule,Relations]
    Headline
        constructor for OIModule
    Usage
        M = oiModule(A,L)
    Inputs
    	A:OIAlgebra
	L:List
	    of nonnegative integers
    Outputs
    	M:OIModule
	    a sum of principal projective modules
    Description
    	Text
    	    Produces the sum of principal projective A-modules generated in the widths
	    specified by list L.
        Example
	    R = QQ[x,y]
	    A = oiAlgebra R
	    M = oiModule(A,{1,2,2})
	    M 3
	Text
	    To produce subquotients of sums of principal projective, use the optional
	    inputs Generators and Relations, which each take an OIModuleMap as the
	    argument.
	Example
	    phi = oiModuleMap(M,A^{1},{matrix{{x}}})
	    psi = oiModuleMap(M,A^{2},{matrix{{0},{0},{y},{-y}}})
	    P = oiModule(A,{1,2,2}, Generators=>phi, Relations=>psi)
	    P 3

Node 
    Key
        OIModuleMap
	(image,OIModuleMap)
	(kernel,OIModuleMap)
	(cokernel,OIModuleMap)
	(source,OIModuleMap)
	(target,OIModuleMap)
	(symbol *,OIModuleMap,OIModuleMap)
	(symbol SPACE,OIModuleMap,OIObject)
	(symbol SPACE,OIModuleMap,ZZ)
    Headline
        the class of maps between modules over OI-algebras
    Description
        Text
	    An OIModuleMap represents a morphism between modules over an OI-Algebra A.
	    
	    

Node
    Key
    	oiModuleMap
	(oiModuleMap, OIModule, OIModule, List)
    Headline
        constructor for OIModuleMap
    Usage
    	phi = oiModuleMap(N,M,v)
    Inputs
    	N:OIModule
	    A free OI-module specifying the target of the map
	M:OIModule
	    A free OI-module, over the same OI-algebra as M, specifying the source of the map
	l:List
	    A list of vectors specifying the images of each of the generators of M.
    Outputs
    	phi:OIModuleMap
    Description
    	Text
    	    A map $\phi: M \rightarrow N$ between free OI-modules is determined by the list of vectors $\{v_1, v_2, \ldots, v_n\}$. The constructor oiModuleMap takes inputs specifying the modules and vectors and produces @ofClass OIModuleMap@.
	Example
	    R = ZZ/101[x,y,z]
	    A = oiAlgebra (R)
	    M = A^{2,3}
	    N = A^{1,2}
	    v1 = transpose (matrix {{1,0,1}})
	    v2 = transpose (matrix {{x^2,0,y^2,0,z^2,0}})
	    phi = oiModuleMap(N,M,{v1,v2})
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

A = oiAlgebra (ZZ/101[x,y,z])
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
A = oiAlgebra (R)
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
errorDepth = 0
R = QQ[x,y]
A = oiAlgebra R
M = oiModule(A,{1,2,2})
M 3
phi = oiModuleMap(M,A^{1},{matrix{{x}}})
psi = oiModuleMap(M,A^{2},{matrix{{0},{0},{y},{-y}}})
P = oiModule(A,{1,2,2}, Generators=>phi, Relations=>psi)
P 3
Q = oiModule(A,{1,2,2}, Relations=>psi)
Q 3
S = oiModule(A,{1,2,2}, Generators=>phi)
S 3

R = ZZ/31991[x,y]
A = oiAlgebra (R)

M = A^{2,3,5}
N = A^{1,1,2}
idOI M
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
