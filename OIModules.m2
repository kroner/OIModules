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
    "makeOIAlgebra"
    }


---------------
-- New types --
---------------

FiniteTotallyOrderedSet = new Type of VisibleList
OrderPreservingInjectiveFunction = new Type of HashTable
ConstantOIAlgebra = new Type of HashTable
OIModule = new Type of HashTable

-----------------------
-- Type constructors --
-----------------------

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
    net A#(symbol ring)
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

ob1 = OIObject 3
ob2 = OIObject 6
OIHom(ob1, ob2)
ep = OIMorphism {1,2,4}
tau  = OIMorphism {1,3,5,8}

-- operator precedece

-- nets vs strings, printing in matrices

-- hashtable keys in package (symbol, string, etc)

-- coherence w/ type system, class vs parent

-- controlling precedence of operators

-- conflicts between dictionaries

-- some packages are symbols, some are packages