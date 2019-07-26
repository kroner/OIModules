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
--------------------------------------------------------------------
quit
installPackage "OIModules"
a = OIMorphism({1,2},3)
b = OIMorphism{1,3}
c = OIMorphism{2,3}
A = OIElement(hashTable{{a,1}})
B = OIElement(hashTable{{b,1}})
C = OIElement(hashTable{{c,1}})
OIGroebner({A+B+C})
OISPairs(A+B+C,A+B+C)
quit
a = OIMorphism({1,2},4)
b = OIMorphism({1,3},4)
s = OIMorphism({1,2},6)
t = OIMorphism({1,3},6)
X = OIElement(hashTable{{a,1},{b,-1}})
Y = OIElement(hashTable{{s,1},{t,-1}})

OIDivisionAlgorithm(Y,{B,X,A})
OIDivides(OIMorphism{2,3},OIMorphism{1,4})

aa = OIMorphism({1,2},4)
bb = OIMorphism({1,3},4)
cc = OIMorphism({1,4})
aaa = OIMorphism({1,2},5)
bbb = OIMorphism({1,3},5)

S = A+B+C
T = OIElement(hashTable{{aa,1},{bb,1},{cc,1}})
U = OIElement(hashTable{{aaa,-1},{bbb,1}})

OIDivisionAlgorithm(T,{T})
