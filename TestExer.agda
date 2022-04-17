module TestExer where

import Exercise
open Exercise

----------------------
-------- (a) ---------
----------------------

testListP : ListP (Cons 3) ≡ 1
testListP = refl

testListNil : nil ≡ Node Nil ListEnd
testListNil = refl

testListCons1Nil : cons 1 nil ≡ Node (Cons 1) (λ x → Node Nil ListEnd)
testListCons1Nil = refl


testListCons2Nil : cons 2 nil ≡ Node (Cons 2) (λ x → Node Nil ListEnd)
testListCons2Nil = refl


----------------------
-------- (b) ---------
----------------------

testTreeLeaf : leaf 1 ≡ Node (Leaf 1) TreeEnd
testTreeLeaf = refl


testTreeNode1 : node (leaf 0) (leaf 1) ≡ 
    Node Node (TreeNodeSubTrees 
        (Node (Leaf zero) TreeEnd) 
        (Node (Leaf 1) TreeEnd))
testTreeNode1 = refl


----------------------
-------- (c) ---------
----------------------

-- testCraftFin1 : craftFin 1 {fzero} ≡ fzero
-- testCraftFin1 = refl

-- testCraftFin2 : craftFin 2 {fzero} ≡ fsucc fzero
-- testCraftFin2 = refl

-- testSumFin1 : sumFin 1 forget ≡ 1
-- testSumFin1 = refl

-- testSumFin2 : sumFin 2 forget ≡ 2 --3
-- testSumFin2 = refl

-- testSumFin3 : sumFin 3 forget ≡ 3 --6
-- testSumFin3 = refl

-- testGsize1 : gsize {ListS} {ListP} (Node Nil λ x → {!   !}) ≡ 1
-- testGsize1 = refl

-- testGsize2 : gsize {ListS} {ListP} (Node (Cons 0) λ x → {!   !}) ≡ 2
-- testGsize2 = refl

-- testGsize3 : gsize {ListS} {ListP} (Node (Cons 1) λ x → {!   !}) ≡ 3
-- testGsize3 = refl

-- testGsize1tree : gsize {TreeS} {TreeP} (Node (Leaf 0) λ x → {!   !})
--     ≡ 1
-- testGsize1tree = refl

-- testGsize2tree : gsize {TreeS} {TreeP} (Node (Node (Leaf 0) (Leaf 1)) λ x → {!   !}) 
--     ≡ 2
-- testGsize2tree = refl

-- testGsize3tree : gsize {TreeS} {TreeP} (Node (Node (Leaf 0) (Node (Leaf 1) (Leaf 2))) λ x → {!   !}) 
--     ≡ 3
-- testGsize3tree = refl

