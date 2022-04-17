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


nodeSimple : TTree
nodeSimple = node (leaf 0) (leaf 1)


testTreeNodeSimple : nodeSimple ≡ 
    Node Node (TreeNodeSubTrees 
        (Node (Leaf zero) TreeEnd) 
        (Node (Leaf 1) TreeEnd))
testTreeNodeSimple = refl


----------------------
-------- (c) ---------
----------------------

testCraftFin1 : craftFin 1 {fzero} ≡ fzero
testCraftFin1 = refl

testCraftFin2 : craftFin 2 {fzero} ≡ fsucc fzero
testCraftFin2 = refl

testSumFinListNil : sumFin 1 (λ x → ListP Nil) ≡ zero
testSumFinListNil = refl

testSumFinListCons : sumFin 1 (λ x → ListP (Cons 2)) ≡ 1
testSumFinListCons = refl

testSumFinTreeLeaf : sumFin 2 (λ x → TreeP {!   !}) ≡ {!   !}
testSumFinTreeLeaf = refl

-- here above I see the limit of trying to transform TreeP using
-- sumFin

-- here below are some further old tests when I didn't understand
-- how to use sumFin so I used forget to make it compile

-- testSumFin2 : sumFin 2 forget ≡ 2 --3
-- testSumFin2 = refl

-- testSumFin3 : sumFin 3 forget ≡ 3 --6
-- testSumFin3 = refl

-- so I proceed implementing my own gsize and it works nicely

testGsizeListNil : gsize nil ≡ 1
testGsizeListNil = refl

testGsizeListCons2 : gsize (cons 1 nil) ≡ 2
testGsizeListCons2 = refl

testGsizeListCons3 : gsize (cons 1 (cons 0 nil)) ≡ 3
testGsizeListCons3 = refl


testGsizeTreeLeaf : gsize (leaf 0) ≡ 1
testGsizeTreeLeaf = refl


testGsizeTreeNodeSimple : gsize nodeSimple ≡ 4
testGsizeTreeNodeSimple = refl

-- we can see from the example `testTreeNodeSimple` above
-- that the number of `Node` constructors is indeed 4

node7 : TTree
node7 = node (leaf 0) (node (leaf 1) (leaf 2))

testNode7 : node7 ≡ 
    Node Node (TreeNodeSubTrees 
        (Node (Leaf zero) TreeEnd) 
        (Node Node (TreeNodeSubTrees 
            (Node (Leaf 1) TreeEnd) 
            (Node (Leaf 2) TreeEnd)))) 
testNode7 = refl

testGsizeTreeNode7 : gsize node7 ≡ 7
testGsizeTreeNode7 = refl

-- it's not simple to see how this scales,
-- but it works even for nested types!!

-- below are some old tests when I didn't understand how to terminate
-- the Tree..

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


----------------------
-------- (d) ---------
----------------------

showList : ListS → M
showList Nil = z
showList (Cons zero) = z +M z
showList (Cons (succ n)) = z +M showList (Cons n)

testFoldMapListNil : foldMap showList nil  ≡ z
testFoldMapListNil = refl

testFoldMapListCons0Nil : foldMap showList (cons 0 nil)  ≡ 
    ((z +M z) +M z)
testFoldMapListCons0Nil = refl

testFoldMapListCons1Nil : foldMap showList (cons 1 nil)  ≡ 
    ((z +M (z +M z)) +M z)
testFoldMapListCons1Nil = refl


testFoldMapListCons2Nil : foldMap showList (cons 2 nil)  ≡ 
    ((z +M (z +M (z +M z))) +M z)
testFoldMapListCons2Nil = refl

testFoldMapListCons1Cons2Nil : foldMap showList (cons 1 (cons 2 nil))  ≡ 
    ((z +M (z +M z)) +M ((z +M (z +M (z +M z))) +M z))
testFoldMapListCons1Cons2Nil = refl

showNode : TreeS → M
showNode Node = (z +M z) +M (z +M z)
showNode (Leaf zero) = z
showNode (Leaf (succ x)) = z +M showNode (Leaf x)

testFoldMapTreeLeaf0 : foldMap showNode (leaf 0) ≡ z
testFoldMapTreeLeaf0 = refl

testFoldMapTreeLeaf1 : foldMap showNode (leaf 1) ≡ (z +M z)
testFoldMapTreeLeaf1 = refl

testFoldMapTreeLeaf2 : foldMap showNode (leaf 2) ≡ (z +M (z +M z))
testFoldMapTreeLeaf2 = refl

testFoldMapTreeNodeSimple : foldMap showNode nodeSimple ≡
    (((z +M z) +M (z +M z)) +M ((z +M z) +M z))
testFoldMapTreeNodeSimple = refl

-- here the tree is processed in post-order i think
-- which means that first the right child, then the left child
testFoldMapTreeNode7 : foldMap showNode node7 ≡
    (((z +M z) +M (z +M z)) +M 
        -- node (leaf 1) (leaf 2)
        ((((z +M z) +M (z +M z)) +M ((z +M (z +M z)) +M (z +M z)))
        -- leaf 0
        +M z))
testFoldMapTreeNode7 = refl

