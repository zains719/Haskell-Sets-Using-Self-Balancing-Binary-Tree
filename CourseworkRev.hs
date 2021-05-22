{- DO NOT CHANGE MODULE NAME, if you do, the file will not load properly -}
module CourseworkRev where

import qualified Data.Set as HS (fromList, toList)
import Test.QuickCheck

{-
  Your task is to design a datatype that represents the mathematical concept of
  a (finite) set of elements (of the same type). We have provided you with an
  interface (do not change this!) but you will need to design the datatype and
  also support the required functions over sets. Any functions you write should
  maintain the following invariant: no duplication of set elements.

  There are lots of different ways to implement a set. The easiest is to use a
  list. Alternatively, one could use an algebraic data type, wrap a binary
  search tree, or even use a self-balancing binary search tree. Extra marks will
  be awarded for efficient implementations (a self-balancing tree will be more
  efficient than a linked list for example).

  You are **NOT** allowed to import anything from the standard library or other
  libraries. Your edit of this file should be completely self-contained.

  **DO NOT** change the type signatures of the functions below: if you do, we
  will not be able to test them and you will get 0% for that part. While sets
  are unordered collections, we have included the Ord constraint on some
  signatures: this is to make testing easier.

  You may write as many auxiliary functions as you need. Everything must be in
  this file.

  See the note **ON MARKING** at the end of the file.
-}

{-
   PART 1.
   You need to define a Set datatype.
-}

-- you **MUST** change this to your own data type. The declaration of Set a =
-- Int is just to allow you to load the file into ghci without an error, it
-- cannot be used to represent a set.
data Set a = EmptyTree | Node a (Set a) (Set a) deriving (Show, Ord)
    
{-
   PART 2.
   If you do nothing else, you must get the toList, fromList and equality working. If they
   do not work properly, it is impossible to test your other functions, and you
   will fail the coursework!
-}

-- toList {2,1,4,3} => [1,2,3,4]
-- the output must be sorted.
toList :: Ord a => Set a -> [a]
toList EmptyTree = []
toList (Node a left right) = isort $ toList left ++ [a] ++ toList right

-- fromList: do not forget to remove duplicates!
fromList :: Ord a => [a] -> Set a
fromList xs = buildBalanced . quickSort $ xs

quickSort :: (Ord a) => [a] -> [a]
quickSort [] = []
quickSort (x:xs) = quickSort (fst $ splitter (x:xs)) ++ [x] ++ quickSort (snd $ splitter (x:xs))

splitter :: (Ord a) => [a] -> ([a],[a])
splitter [] = ([],[])
splitter (x:xs) = (smaller, bigger)
  where smaller = [a | a <- xs, a < x]
        bigger = [a | a <- xs, a > x]

buildBalanced :: [a] -> Set a
buildBalanced [] = EmptyTree
buildBalanced xs = Node (xs !! half) (buildBalanced $ take half xs) (buildBalanced $ drop (half + 1) xs)
  where half = (length xs) `div` 2

-- Make sure you satisfy this property. If it fails, then all of the functions
-- on Part 3 will also fail their tests
toFromListProp :: IO ()
toFromListProp =
  quickCheck
    ((\xs -> (HS.toList . HS.fromList $ xs) == (toList . fromList $ xs)) :: [Int] -> Bool)

-- test if two sets have the same elements (pointwise equivalent).
instance (Ord a) => Eq (Set a) where
  s1 == s2 = (toList s1) == (toList s2)

-- you should be able to satisfy this property quite easily
eqProp :: IO ()
eqProp =
  quickCheck ((\xs -> (fromList . HS.toList . HS.fromList $ xs) == fromList xs) :: [Char] -> Bool)

{-
   PART 3. Your Set should contain the following functions. DO NOT CHANGE THE
   TYPE SIGNATURES.
-}

-- the empty set
empty :: Set a
empty = EmptyTree

-- is it the empty set?
isNull :: Set a -> Bool
isNull EmptyTree = True
isNull _ = False

-- build a one element Set
singleton :: a -> Set a
singleton a = Node a EmptyTree EmptyTree

-- insert an element *x* of type *a* into Set *s*. Make sure there are no
-- duplicates!
insert :: (Ord a) => a -> Set a -> Set a
insert x EmptyTree = singleton x
insert x (Node a left right) 
  | x == a = Node x left right
  | x < a = rotate (Node a (insert x left) right)
  | x > a = rotate (Node a left (insert x right))

rotate :: (Ord a) => Set a -> Set a
rotate EmptyTree = EmptyTree
rotate (Node a left right) 
  | not (balanced (Node a left right)) = rotate . rotateAux $ (Node a left right)
  | not (balanced left) = rotate $ Node a (rotateAux left) right
  | not (balanced right) = rotate $ Node a left (rotateAux right)
  | otherwise = Node a left right

rotateAux :: (Ord a) => Set a -> Set a
rotateAux EmptyTree = EmptyTree
rotateAux (Node a left right) 
  | cardinality left > cardinality right = (Node x (removeSet x left) (insert a right)) 
  | cardinality right > cardinality left = (Node y (insert a left) (removeSet y right))
    where x = rightMinNode left
          y = leftMinNode right

balanced :: (Ord a) => Set a -> Bool
balanced EmptyTree = True
balanced (Node a left right)
  | abs ((cardinality left) - (cardinality right)) > 1 = False
  | otherwise = True

rightMinNode :: (Set a) -> a
rightMinNode (Node a _ EmptyTree) = a
rightMinNode (Node a _ right) = rightMinNode right

-- join two Sets together be careful not to introduce duplicates.
union :: (Ord a) => Set a -> Set a -> Set a
union EmptyTree EmptyTree = EmptyTree
union EmptyTree set = set
union set EmptyTree = set
union (Node a left right) set2 = setfoldr (insert) set2 (Node a left right)

-- return, as a Set, the common elements between two Sets
intersection :: (Ord a) => Set a -> Set a -> Set a
intersection EmptyTree _  = EmptyTree
intersection _ EmptyTree = EmptyTree
intersection (Node a left right) set2 
  | member a set2 = rotate (Node a (intersection left set2) (intersection right set2))
  | otherwise = rotate . union (intersection left set2) $ (intersection right set2)

-- all the elements in *s1* not in *s2*
-- {1,2,3,4} `difference` {3,4} => {1,2}
-- {} `difference` {0} => {}
difference :: (Ord a) => Set a -> Set a -> Set a
difference EmptyTree _ = EmptyTree
difference set EmptyTree = set
difference (Node a left right) set2 
  | member a set2 = rotate . union (difference left set2) $ (difference right set2)
  | otherwise = rotate (Node a (difference left set2) (difference right set2))

-- is element *x* in the Set s1?
member :: (Ord a) => a -> Set a -> Bool
member _ EmptyTree = False
member x (Node a left right) 
  | x == a = True
  | x < a = member x left
  | x > a = member x right

-- how many elements are there in the Set?
cardinality :: Set a -> Int
cardinality EmptyTree = 0
cardinality (Node a left right) = 1 + cardinality left + cardinality right

-- apply a function to every element in the Set
setmap :: (Ord b) => (a -> b) -> Set a -> Set b
setmap _ EmptyTree = EmptyTree
setmap f set = setfoldr (\x acc -> insert (f x) acc) EmptyTree set

-- right fold a Set using a function *f*
setfoldr :: (a -> b -> b) -> b -> Set a -> b
setfoldr _ acc EmptyTree = acc
setfoldr f acc (Node a left right) = setfoldr f (f a (setfoldr f acc right)) left

-- remove an element *x* from the set
-- return the set unaltered if *x* is not present
removeSet :: (Ord a) => a -> Set a -> Set a
removeSet _ EmptyTree = EmptyTree
removeSet x (Node a left right) = rotate . removeItem x $ (Node a left right)
  where removeItem _ EmptyTree = EmptyTree
        removeItem x (Node a left right)
          | x == a = remove a (Node a left right)
          | x < a = Node a (removeItem x left) right
          | x > a = Node a left (removeItem x right)

remove :: (Ord a) => a -> Set a -> Set a
remove x (Node _ EmptyTree EmptyTree) = EmptyTree --delete leaf node
remove x (Node _ left EmptyTree) = left --delete node with one child
remove x (Node _ EmptyTree right) = right
remove x (Node _ left right) = Node a left right' --delete node with two children
  where a = leftMinNode right
        right' = (removeSet a right)

leftMinNode :: (Set a) -> a
leftMinNode (Node a EmptyTree _) = a
leftMinNode (Node a left _) = leftMinNode left

-- powerset of a set
-- powerset {1,2} => { {}, {1}, {2}, {1,2} }
powerSet :: Set a -> Set (Set a)
powerSet EmptyTree = Node EmptyTree EmptyTree EmptyTree
powerSet (Node a left right) =  setfoldr (powerSetAux) (Node EmptyTree EmptyTree EmptyTree) $ (Node a left right)

powerSetAux :: a ->  Set (Set a) -> Set (Set a)
powerSetAux x set = union' (setmap' (insert' x) set) set

isort :: (Ord a) => [a] -> [a]
isort [] = []
isort (x:xs) = isortInsert x (isort xs)

isortInsert :: (Ord a) => a -> [a] -> [a]
isortInsert x [] = x : []
isortInsert x (y:ys)
    | x < y = x : y : ys
    | otherwise = y : isortInsert x ys

--auxilary functions without ord
setmap' :: (a -> b) -> Set a -> Set b
setmap' _ EmptyTree = EmptyTree
setmap' f (Node a left right) = Node (f a) (setmap' f left) (setmap' f right)

union' :: Set a -> Set a -> Set a
union' EmptyTree EmptyTree = EmptyTree
union' EmptyTree set = set
union' set EmptyTree = set
union' (Node a left right) set2 = setfoldr (insert') set2 (Node a left right) 

insert' :: a -> Set a -> Set a
insert' x EmptyTree = singleton x
insert' x (Node a left right) = Node a left (insert' x right)

{-
   ON MARKING:

   Be careful! This coursework will be marked using QuickCheck, against
   Haskell's own Data.Set implementation. This testing will be conducted
   automatically via a marking script that tests for equivalence between your
   output and Data.Set's output. There is no room for discussion, a failing test
   means that your function does not work properly: you do not know better than
   QuickCheck and Data.Set! Even one failing test means 0 marks for that
   function. Changing the interface by renaming functions, deleting functions,
   or changing the type of a function will cause the script to fail to load in
   the test harness. This requires manual adjustment by a TA: each manual
   adjustment will lose 10% from your score. If you do not want to/cannot
   implement a function, leave it as it is in the file (with undefined).

   Marks will be lost for too much similarity to the Data.Set implementation.

   Pass: creating the Set type and implementing toList and fromList is enough
   for a passing mark of 40%, as long as both toList and fromList satisfy the
   toFromListProp function.

   The maximum mark for those who use Haskell lists to represent a Set is 70%.
   To achieve a higher grade than is, one must write a more efficient
   implementation. 100% is reserved for those brave few who write their own
   self-balancing binary tree.
-}
