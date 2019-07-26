
restart
needsPackage "RegularLanguages"
S = {"a","b","c"}
-- Automaton that accepts only the word "aab"
A = wordAutomaton(S, word "aab")
peek A

A "aab"
A "aba"

M = matrix{{0,0},{1,1}}
-- Automaton that accepts all words with length > 0
B = automaton(S,2,{M,M,M},{1})
B "aaaaa"
B ""

-- Hilbert series (aka generating functions)
T = frac(QQ[s,t])
automatonHS(B,{s,t,t})

-- operations on regular languages
As = kleeneStar A
AB = cat(A,B)
AcapB = intersection(A,B)
AcupB = union(A,B)
Ac = complement(A)

R = "aaab*[ac]*(bbb)*aa"
C = regexAutomaton(S,R)
C "aaabbbbbacacacaa"

-- OS^op-module languages 
D = surjectionToAutomaton({{1,1,2,1,2,3}})
automatonHS(D,{t,t,t})

viewHelp RegularLanguages

