quit

installPackage "OIModules"
	
a = OIMorphism({1,2,3},5)
b = OIMorphism({1,2,5},5)
OILCM(a,b)
OIGCD(a,b)
    

---------------------------------------------------------

a = OIMorphism({1,2,3},5)
b = OIMorphism{1,2,5}
c = OIMorphism{2,3,5}
d = OIMorphism{1,2,4}
e = OIMorphism({1,2,3},4)
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


installPackage "OIModules"
a = oiMorphism({1,2},3)
b = oiMorphism{1,3}
c = oiMorphism{2,3}
A = OIElement(hashTable{{a,1}})
B = OIElement(hashTable{{b,1}})
C = OIElement(hashTable{{c,1}})
repToHilb({A+B+C})

OISPairs(A+B+C,A+B+C)

R = QQ[x,y,z]

I = ideal(x,y^2,y*z^2,z^3)
hilbertSeries(I)


S = R^{-2}
M=I*S
hilbertSeries(I*S)
