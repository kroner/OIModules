installPackage "OIModules"	
	
a = OIMorphism({1,2,3},5)
b = OIMorphism({1,2,5},5)
c = OIMorphism{2,3,5}
d = OIMorphism({1,2,4},4)
e = OIMorphism({1,2,3},4)

S = OIElement(hashTable{{a,1},{b,1},{c,3}})
T = OIElement(hashTable{{d,1},{e,1}})
OIDivisionAlgorithm(S,{T})

