restart
installPackage "OIModules"

-- OI is the category where the objects are the totally ordered finite
-- sets, and the arrows are the order-preserving injective functions.

-- up to isomorphism, there's only one object in OI for each
-- non-negative n \in ZZ, namely {1, 2, ..., n} which we denote by
-- [n]. And there are binomial(m,n) arrows from [n] to [m].

-- We've implemented this category.

k = oiObject 3
n = oiObject 5
m = oiObject 9

tau = oiMorphism {2,4,5}

source tau
target tau
tau 1
tau 2
tau 3

epsilon = oiMorphism({1,2,4,5,8},9)

target tau == source epsilon
epsilon tau

-- and Hom, which we'll need later

OIHom(n,m)

-- as well as a "lex" order on arrows in OI:

sort oo

-- for a fixed ring R, an OI-module is a functor from OI to R-mod.

-- Naive example: think: V : OI -> R-mod, where V([n]) is a free
-- R-module with basis indexed by [n], and where the arrows in OI
-- induce R-linear maps as expected R-linear maps

-- more generally, the principle projective OI-module P_n for
-- non-negative n has P_n([k]) the free R-module indexed by
-- Hom([n],[k]), with morphisms induced by post-composition

-- the finitely-generated free OI-modules are precisely the direct
-- sums of finitely many principle projectives. These are implemented.

R = ZZ/31991[x,y]
A = makeOIAlgebra R

-- the naive example from above

P1 = A^{1}

-- OI-Modules are functors: you can plug in OI objects:

P1 5
P1 9


-- you can plug in OI-morphisms:

P1 epsilon

-- and it respects composition:

P1 (epsilon tau) == (P1 epsilon) * (P1 tau)

-- More general free modules are implemented:

F = A^{2,3,5}

-- ranks grow binomially. Things can be a bit slow (about five seconds here:)
time apply(20, i -> F i)

-- but OI-modules cache these computations, so its only slow once

time apply(20, i -> F i)

peek F.cache

-- (still a functor)

F (epsilon tau) == (F epsilon) * (F tau)

-- maps between (free) OI modules are natural transformations. For
-- maps between free modules, the entire map is specified by the
-- images of the generators of the source OI module

G = A^{1,1,2}

-- So to specify a map from F to G, we need to choose one element each of

G 2
G 3
G 5

a = random(G 2, R^1)
b = random(G 3, R^1)
c = random(G 5, R^1)

-- (no net for this)
phi = oiModuleMap(F,G,{a,b,c})

phi 0
phi 1
phi 2
phi 3

-- the farther future: using Groebner bases for kernels, images,
-- cokernels, free resolutions. Regular Languages for Hilbert
-- functions / series. Modules over more general (non-constant)
-- OI-algebras and OI-ideals. A lot.