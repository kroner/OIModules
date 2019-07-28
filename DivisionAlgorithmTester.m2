quit

installPackage "OIModules"
	
a = OIMorphism({1,2,3},5)
b = OIMorphism({1,2,5},5)
OILCM(a,b)
OIGCD(a,b)
    

---------------------------------------------------------

a = oiMorphism({1,2,3},5)
b = oiMorphism{1,2,5}
c = oiMorphism{2,3,5}
d = oiMorphism{1,2,4}
e = oiMorphism({1,2,3},4)
S = OIElement(hashTable{{a,1},{b,1},{c,3}})
T = OIElement(hashTable{{d,1},{e,1}})

OIDivisionAlgorithm(S,{T})
OIDivisionAlgorithm(S,{S})



A = OIElement(hashTable{{a,1}})
B = OIElement(hashTable{{b,1}})
C = OIElement(hashTable{{c,1}})
D = OIElement(hashTable{{d,1}})
E = OIElement(hashTable{{e,1}})

oiMonomialsToHilbert({B,C})

---------------------------Groebner Functionality----------------------

---------------------------Behaves Randomly, even though I did not purposefully add any randomness
---------------------------May have to try quitting/restarting a few times. Will work on the bug soon

quit
installPackage "OIModules"
a = oiMorphism({1,2},3)
b = oiMorphism{1,3}
c = oiMorphism{2,3}
A = OIElement(hashTable{{a,1}})
B = OIElement(hashTable{{b,1}})
C = OIElement(hashTable{{c,1}})
repToHilb({A+B+C})


l = for i in OIHom(2,4) list {i,1}
S = OIElement(hashTable l)
repToHilb({S})
oiInitialTerms = L->(
    temp:={};
    for i in L do(
	temp = append(temp,OIElement(hashTable{{OIInitial i,1}})));
    return temp)



repToHilb({A+B,B+C})
oiInitialTerms ;l
oiInitialTerms l
j = oiInitialTerms l
oiMonomialsToHilbert j
