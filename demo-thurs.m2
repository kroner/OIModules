restart
installPackage "OIModules"

-- OI is the category where the objects are the totally ordered finite
-- sets, and the arrows are the order-preserving injective functions.

-- up to isomorphism, there's only one object in OI for each
-- non-negative n \in ZZ, namely {1, 2, ..., n} which we denote by
-- [n]. And there are binomial(m,n) arrows from [n] to [m].

-- We've implemented this category.

k = OIObject 3
n = OIObject 5
m = OIObject 9

tau = OIMorphism {2,4,5}

source tau
target tau
tau 1
tau 2
tau 3

epsilon = OIMorphism({1,2,4,5,8},9)

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

-- the naive example from above (no net yet)

P1 = A^{1}

-- OI-Modules are functors:

P1 5
P1 9
P1 epsilon

-- And more general free modules are implemented:

F = A^{3,4,5}

-- ranks grow as binomial coeffs. Can be a bit slow (roughly five seconds here:)
time apply(20, i -> F i)

-- but OI-modules cache these computations, so its only slow once
time apply(20, i -> F i)

peek F.cache

-- still a functor

F epsilon

-- the immediate future: maps between free OI-modules (these are just
-- natural transformations), and OI-modules that aren't free.

-- the farther future: using Groebner bases for kernels, images,
-- cokernels, free resolutions. Regular Languages for Hilbert
-- functions / series. Modules over more general (non-constant)
-- OI-algebras and OI-ideals. A lot.