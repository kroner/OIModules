restart
installPackage "OIModules"

-*
OI is the category where the objects are the totally ordered finite
sets, and the arrows are the order-preserving injective functions.

up to isomorphism, there's only one object in OI for each
non-negative n \in ZZ, namely {1, 2, ..., n} which we denote by
[n]. And there are binomial(m,n) arrows from [n] to [m].

We've implemented this category.
*-

k = oiObject 3
n = oiObject 5
m = oiObject 9

tau = oiMorphism {2,4,5}

source tau
target tau
set source tau
tau 1
tau 2
tau 3

epsilon = oiMorphism({1,2,4,5,8},9)
target epsilon

target tau == source epsilon
epsilon tau

-- and Hom, which we'll need later

OIHom(n,m)

-- as well as the "Lex" order on arrows in OI

sort oo

-*
for a fixed ring R, an OI-module is a functor from OI to R-mod.

Naive example: think: V : OI -> R-mod, where V([n]) is a free
R-module with basis indexed by [n], and where the arrows in OI
induce R-linear maps as expected R-linear maps

more generally, the principle projective OI-module P_n for
non-negative n has P_n([k]) the free R-module indexed by
Hom([n],[k]), with morphisms induced by post-composition

the finitely-generated free OI-modules are precisely the direct
sums of finitely many principle projectives. These are implemented.
*-

R = ZZ/59[x,y]
A = makeOIAlgebra R

-*
the naive example from above
*-

P1 = A^{1}

-*
OI-Modules are functors: you can plug in OI objects,
*-

P1 5
P1 9

-*
and you can plug in OI-morphisms.
*-

P1 epsilon

-*
Functors had better respect composition.
*-

P1 (epsilon tau) == (P1 epsilon) * (P1 tau)

-*
General (finitely-generated) free modules are implemented:
*-

F = A^{2,3,5}

-*
ranks grow binomially in [n].
Things can be a bit slow (about four seconds here:)
*-

time apply(20, i -> F i)

-- but OI-modules cache these computations, so its only slow once

time apply(20, i -> F i)

maps between (free) OI modules are natural transformations. For
maps between free modules, the entire map is specified by the
images of the generators of the source OI module

G = A^{1,1,2}

-*
to specify a map from F to G, we need to choose one element each of
*-

G 2
G 3
G 5

a = random(G 2, R^1)
b = random(G 3, R^1)
c = random(G 5, R^1)

-- (no net for this)
phi = oiModuleMap(G,F,{a,b,c})

phi 0
phi 1
phi 2
phi 3
phi 6

-*
To be a natural transformation, this square better commute:
(the horizontal maps come from phi, vertical from epsilon)

(G 5) <----- (F 5)
  |            |
  |            |
  |            |
  v            v
(G 9) <----- (F 9)

(it does)
*-

(G epsilon) * (phi 5) ==  (phi 9) * (F epsilon)

-*
Let's make another map, this one from G to a new free OIModule H:
*-

H = A^{2,2}
psi = oiModuleMap(H,G, {random(H 1, R^1), random(H 1, R^1),random(H 2, R^1)})

-*
we can compose maps between OIModules, just like with matrices
*-

psi * phi

-*
this looks correct but it should not be saying "free"
*-

coker psi
image phi

-*
Not implemented yet: Anything that would require a Groebner bases.

These exist for OI-modules, and can be implemented w/ some new stuff,
some existing M2 functionality.
*-

-*
the dream: to be able to do things like

gb image phi

res image phi -- (with a specified homological degree bound)

HH(psi,phi)

hilbertSeries ker phi (when this makes sense)

And, in the farther future:

more general OI-algebras, where (for example) A(n) = kk[x_1..x_n],
along with their ideal theory module theory.
*-