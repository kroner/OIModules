quit

installPackage "OIModules"
	
a = OIMorphism({1,2,3},5)
b = OIMorphism({1,2,5},5)
OILCM(a,b)
OIGCD(a,b)



----------------------------------------------------



a = OIMorphism({1,2},4)
b = OIMorphism({2,3},4)
c = OIMorphism({2,4},4)
S = OIElement(hashTable({{a,1},{c,1}}))
T = OIElement(hashTable({{b,1},{c,1}}))

Lemon = OIGroebner({S,T})

for i in Lemon do(
    for j in keys i do(
	print(j,source j, target j)))

for i in Lemon do(
    print(i,OIInitial i,target OIInitial i))
    
---------------------------------------------------------
--DIVISION SEEMS TO WORK EXCEPT FOR WHEN YOU ARE DIVIDING SOMETHING BY ITSELF, CONFUSING
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


a = OIMorphism({1,2},3)
b = OIMorphism{1,3}
a<b


A = OIElement(hashTable{{a,1}})
B = OIElement(hashTable{{b,1}})
C = OIElement(hashTable{{c,1}})
D = OIElement(hashTable{{d,1}})
E = OIElement(hashTable{{e,1}})

oiMonomialsToHilbert({B,C})
