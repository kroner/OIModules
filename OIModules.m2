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
    "oiSyzZero",
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
    "getWidthList"
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


-*OISPairs = (a,b)->(
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
    return toList(set(temp))) *-
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
    (fold(vals, (x,y) -> (toString x) |","| (toString y)))|","| (net target epsilon)
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

getWidthList = method()

getWidthList OIModule := List => (M) -> (
    M#(symbol widthList)
    )

getOIAlgebra = method()

getOIAlgebra OIModule := ConstantOIAlgebra => (M) -> (
    M#(symbol OIAlgebra)
    )


OIModule ++ OIModule := OIModule => (M,N) -> (
    if ((getOIAlgebra M).ring) =!= ((getOIAlgebra N).ring) then
      error "expected OIModules over the same OIAlgebra";  
    new OIModule from {
	symbol cache => hashTable{},
	symbol numgens => M#(symbol numgens) + N#(symbol numgens),
	symbol widthList => getWidthList M | getWidthList N	
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

