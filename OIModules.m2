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
	    Email => "email6"},	   
	},
    HomePage => "https://nathanfieldsteel.github.io",
    Headline => "A package for computations with OI-algebras and modules over OI-algebras",
    AuxiliaryFiles => false)

export {
    }

---------------
-- New types --
---------------

-----------------------
-- Type constructors --
-----------------------

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
