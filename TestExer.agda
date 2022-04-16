module TestExer where

import Exercise
open Exercise

----------------------
-------- (a) ---------
----------------------

testListC : ListC (Cons 3) ≡ 4
testListC = refl