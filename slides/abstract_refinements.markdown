% Abstract Refinements
% Niki Vazou, Patrick Rondon , and Ranjit Jhala
% February 25, 2013

## The maxInt example

~~~~~{.haskell}
maxInt     :: Int -> Int -> Int
maxInt x y = if x > y then x else y
~~~~~

- Given
    - 8  :: {v:Int | v > 0} <: Int  
    - 12 :: {v:Int | v > 0} <: Int  

- We **get**
    - maxInt 8 12 :: Int

- We **want** 
    - maxInt 8 12 :: {v : Int | v > 0}
 
## Typechecking Monomorphic Refinements

~~~~~{.haskell}
maxInt     :: forall <p :: Int -> Prop>. Int<p> -> Int<p> -> Int<p>
maxInt x y = if x > y then x else y
~~~~~

- Given 
     - p :: Int -> Prop
     - x :: Int \<p\>
     - y :: Int \<p\>
- We have
     - if x>y then x :: Int\<p\>
     - else        y :: Int\<p\>
     - maxInt x y    :: Int\<p\>


## Using Monomorphic Refinements

~~~~~{.haskell}
maxInt     :: forall <p :: Int -> Prop>. Int<p> -> Int<p> -> Int<p>
maxInt x y = if x > y then x else y
~~~~~

- Given
    - p  :: Int -> Prop
    - 8  :: {v:Int | v > 0}
    - 12 :: {v:Int | v > 0}

- Instantiate predicate
    - p = \v -> v > 0

- We get
    - `maxInt [\v -> v > 0] 8 12 :: {v:Int | v > 0}`
    - `maxInt [...] 8 12 :: {v:Int | v > 0}`

## Outline

- Introduction 
    - Monomorphic Refinements

- Applications
    - <strong>Refinements and Type Classes</strong>
    - Indexed Refinements
    - Recursive Refinements
    - Inductive Refinements
- Evaluation


## Ignoring Type Class Constraints
~~~~~{.haskell}
max    :: Ord a => a -> a -> a
max x y = if x > y then x else y
~~~~~

- Given
    - 8  :: {v:Int | v > 0}
    - 12 :: {v:Int | v > 0}

- Instantiate type variable
    - a = {v:Int | v > 0}

- We have
    - max 8 12 :: {v:Int | v > 0}

## Wrong Reasoning
~~~~~{.haskell}
minus    :: Num a => a -> a -> a
minus x y = x - y
~~~~~

- Given
    - 8  :: {v:Int | v > 0}
    - 12 :: {v:Int | v > 0}

- Instantiate type variable
    - a = {v:Int | v > 0}

- We have
    - minus 8 12 = -4 :: {v:Int | v > 0}

## Parametric Invariants and Type Classes

~~~~~{.haskell}
max     :: forall <p :: a -> Prop>. Ord a => a<p> -> a<p> -> a<p>
max x y = if x > y then x else y
~~~~~

- Given
    - p  :: Int -> Prop
    - 8  :: {v:Int | v > 0}
    - 12 :: {v:Int | v > 0}

- Instantiate predicate
    - p = \\v -> v > 0

- We have
    - max 8 12 :: {v:Int | v > 0}




## Outline
- Introduction 
    - Monomorphic Refinements
- Applications
    - Refinements and Type Classes
    - <strong>Indexed Refinements</strong>
    - Recursive Refinements
    - Inductive Refinements
- Evaluation

<!---
the loop example is induction on integers?
pair seems simpler, 
we supported, but with more complicated syntax
-->

## Depending Pairs

~~~~~{.haskell}
mkPair :: f:(i:a -> b) -> a -> (a, b)
mkPair f i = (i, f i)
~~~~~

- `f i` **depends** on `i`
- Abstract over all refinements that depend on `i`


## Indexted Refinements

~~~~~{.haskell}
mkPair :: forall<p :: a -> b -> Prop>.
           f:(i:a -> b<p i>) -> 
           a -> 
           (i:a, b<p i>)
mkPair f i = (i, f i)
~~~~~

- `f i` **depends** on `i`
- Abstract over all refinements that depend on `i`


## Using Indexted Refinements

~~~~~{.haskell}
mkPair :: forall<p :: a -> b -> Prop>.
           f:(i:a -> b<p i>) -> 
           a -> 
           (i:a, b<p i>)
mkPair f i = (i, f i)

incr :: Int -> (i:Int, {v:Int | v = i+1})
incr i = mkPair (+1) i
~~~~~

- Given 
  - `p :: a -> b -> Prop`
  - `(+1) :: i:Int -> {v:Int | v = i+1}`

- We **infer**
  - `p := \i -> {v:Int | v = i+1}`

- We **get**
  - `mkPair [\i -> {v:Int | v = i+1}] (+1) :: Int -> (i:Int, {v:Int | v = i+1})`

## Vector Initialization

~~~~~{.haskell}
initialize ::  x: a ->
               n: Int ->
               Vec a

initialize x n = initialize' 0 x n empty

initialize' i n x a
  | i >= n
  = a
  | otherwise 
  = initialize (i+1) n x (set i x a)
~~~~~

- The first _n_ elements are set to _x_
- At each iteration _i_, the _i_ th element  is set to _x_
- _Abstract_ over all invariants that depend on _i_


## A vector data type
~~~~~{.haskell}
data Vec a 
  = V {f :: i : Int -> a}
~~~~~

- Refine indices
      - d :: Int -> Prop

- Refine values depending on their index
      - r :: Int -> a -> Prop

## Index Refinements

~~~~~{.haskell}
data Vec a <d :: Int -> Prop, r :: Int -> a -> Prop>
  = V {f :: i : Int<d> -> a<r i>}
~~~~~

- Refine indices
      - d :: Int -> Prop

- Refine values depending on their index
      - r :: Int -> a -> Prop

## Empty Vector

~~~~~{.haskell}
empty = V $ \_ -> error "Undefined Vector"
~~~~~

- Refine indices : empty set
      - d = \\v -> False

- Refine values  : all values
      - r = \\i v -> True

~~~~~{.haskell}
create :: x:a -> Vec <\_ -> False, \_ _ -> True> a
~~~~~

## `get` a value

~~~~~{.haskell}
get i (V f) = f i
~~~~~

- Given
      - d :: Int -> Prop
      - r :: Int -> a -> Prop
      - i :: Int \<d\>
      - V f :: Vec \<d, r\>, so f :: i:Int -> a \<r i\>
- We have
      - f i :: a \<r i\>

~~~~~{.haskell}
get :: forall <d :: Int -> Prop, r :: Int -> a -> Prop>
         i :: Int <d> -> 
         Vec <d, r> a -> 
         a <r i>
~~~~~

## `set` a value

~~~~~{.haskell}
set i v (V f) = V $ \k -> if k == i then v else f k
~~~~~

- Given
      - d :: Int -> Prop
      - r :: Int -> a -> Prop
      - i :: Int \<d\>
      - v :: a \<r i\>
      - V f :: Vec \<d &and; {\\k -> k &ne; i}, r>, 
           so f :: i:Int \<d &and; {\\k -> k &ne; i}\>-> a \<r i\>
- We have
      - f i :: a \<r i\>

~~~~~{.haskell}
set :: forall <d :: Int -> Prop, r :: Int -> a -> Prop>
         i :: Int <d> ->
         v :: a <r i> -> 
         Vec <d and {\k -> k != i}, r> a -> 
         Vec <d, r> a
~~~~~

## Typechecking Vector Initializion
~~~~~{.haskell}
initialize :: x: a -> 
              n: Int -> 
              Vec <{\v -> 0 <= v && v < n}, {\_ v -> v == x}> a

initialize x n = initialize' 0 n x empty

initialize :: i:{v:Int | v >= 0} -> 
              x: a -> 
              n: Int -> 
              a: Vec <{\v -> 0 <= v && v < i}, {\_ v -> v == x}> a -> 
              Vec <{\v -> 0 <= v && v < n}, {\_ v -> v == x}> a

initialize' i n x a
  | i >= n
  = a
  | otherwise 
  = initialize' (i+1) n x (set i x a)
~~~~~

- At each iteration _i_, the _i_ th element is set to _x_
- At the end, then _n_ first elements are set to _x_


## Outline
- Introduction 
    - Monomorphic Refinements
- Applications
    - Refinements and Type Classes
    - Indexed Refinements
    - <strong>Recursive Refinements</strong>
    - Inductive Refinements
- Evaluation

## List Data Type

~~~~~{.haskell}
data [a] 
  = [] 
  | (:) h:a [a]
~~~~~

- Refine tail elements given the head:
    - p :: a -> a -> Prop

## Recursive Refinements

~~~~~{.haskell}
data [a] <p :: a -> a -> Prop> 
  = []<p>
  | (:) h:a [a<p h>]<p>
~~~~~

- h:tl :: [a]\<p\> iff h :: a &and; t :: [a \<p h\>]

## Unfolding Recursive Refinements (0/n)

~~~~~{.haskell}
data [a] <p :: a -> a -> Prop> 
  = []<p>
  | (:) h:a [a<p h>]<p>
~~~~~

- h<sub>1</sub>:h<sub>2</sub>:h<sub>3</sub>:...h<sub>n</sub>:[] :: [a]\<p\> 
    - h<sub>1</sub> :: a
    - h<sub>2</sub> :: a
    - h<sub>3</sub> :: a
    - ...
    - h<sub>n</sub> :: a
    - [] :: [a]
    
## Unfolding Recursive Refinements (1/n)

~~~~~{.haskell}
data [a] <p :: a -> a -> Prop> 
  = []<p>
  | (:) h:a [a<p h>]<p>
~~~~~

- h<sub>1</sub>:h<sub>2</sub>:h<sub>3</sub>:...h<sub>n</sub>:[] :: [a]\<p\> 
    - h<sub>1</sub> :: a
    - h<sub>2</sub> :: a\<p h<sub>1</sub>\>
    - h<sub>3</sub> :: a\<p h<sub>1</sub>\>
    - ...
    - h<sub>n</sub> :: a\<p h<sub>1</sub>\>
    - [] :: [a\<p h<sub>1</sub>\>]
    
## Unfolding Recursive Refinements (2/n)

~~~~~{.haskell}
data [a] <p :: a -> a -> Prop> 
  = []<p>
  | (:) h:a [a<p h>]<p>
~~~~~

- h<sub>1</sub>:h<sub>2</sub>:h<sub>3</sub>:...h<sub>n</sub>:[] :: [a]\<p\> 
    - h<sub>1</sub> :: a
    - h<sub>2</sub> :: a\<p h<sub>1</sub>\>
    - h<sub>3</sub> :: a\<p h<sub>1</sub> &and; p h<sub>2</sub>\>
    - ...
    - h<sub>n</sub> :: a\<p h<sub>1</sub> &and; p h<sub>2</sub>\>
    - [] :: [a\<p h<sub>1</sub> &and; p h<sub>2</sub>\>]

## Unfolding Recursive Refinements (n-1/n)

~~~~~{.haskell}
data [a] <p :: a -> a -> Prop> 
  = []<p>
  | (:) h:a [a<p h>]<p>
~~~~~

- h<sub>1</sub>:h<sub>2</sub>:h<sub>3</sub>:...h<sub>n</sub>:[] :: [a]\<p\> 
    - h<sub>1</sub> :: a
    - h<sub>2</sub> :: a\<p h<sub>1</sub>\>
    - h<sub>3</sub> :: a\<p h<sub>1</sub> &and; p h<sub>2</sub>\>
    - ...
    - h<sub>n</sub> :: a\<p h<sub>1</sub> &and; p h<sub>2</sub> &and; ... &and; p h<sub>n-1</sub>\>
    - [] :: [a\<p h<sub>1</sub> &and; p h<sub>2</sub> &and; ... &and; p h<sub>n-1</sub>\>]


## Unfolding Recursive Refinements (n/n)

~~~~~{.haskell}
data [a] <p :: a -> a -> Prop> 
  = []<p>
  | (:) h:a [a<p h>]<p>
~~~~~

- h<sub>1</sub>:h<sub>2</sub>:h<sub>3</sub>:...h<sub>n</sub>:[] :: [a]\<p\> 
    - h<sub>1</sub> :: a
    - h<sub>2</sub> :: a\<p h<sub>1</sub>\>
    - h<sub>3</sub> :: a\<p h<sub>1</sub> &and; p h<sub>2</sub>\>
    - ...
    - h<sub>n</sub> :: a\<p h<sub>1</sub> &and; p h<sub>2</sub> &and; ... &and; p h<sub>n-1</sub>\>
    - [] :: [a\<p h<sub>1</sub> &and; p h<sub>2</sub> &and; ... &and; p h<sub>n-1</sub> &and; p h<sub>n</sub>\>]


## Increasing List (1/4)

~~~~~{.haskell}
data [a] <p :: a -> a -> Prop> 
  = []<p>
  | (:) h:a [a<p h>]<p>

type IncrList a = [a] <\h v -> h <= v>
~~~~~

- h<sub>1</sub> : h<sub>2</sub> : h<sub>3</sub> : [] :: IncList a


## Increasing List (2/4)

~~~~~{.haskell}
data [a] <p :: a -> a -> Prop> 
  = []<p>
  | (:) h:a [a<p h>]<p>

type IncrList a = [a] <\h v -> h <= v>
~~~~~

- h<sub>1</sub> : h<sub>2</sub> : h<sub>3</sub> : [] :: IncList a
    - h<sub>1</sub> :: a 
    - h<sub>2</sub> :: a 
    - h<sub>3</sub> :: a 
    - []            :: IncrList a 



## Increasing List (2/4)

~~~~~{.haskell}
data [a] <p :: a -> a -> Prop> 
  = []<p>
  | (:) h:a [a<p h>]<p>

type IncrList a = [a] <\h v -> h <= v>
~~~~~

- h<sub>1</sub> : h<sub>2</sub> : h<sub>3</sub> : [] :: IncList a
    - h<sub>1</sub> :: a 
    - h<sub>2</sub> :: {v:a | h<sub>1</sub> &le; v}
    - h<sub>3</sub> :: {v:a | h<sub>1</sub> &le; v} 
    - [] :: IncList {v:a | h<sub>1</sub> &le; v}

## Increasing List (3/4)

~~~~~{.haskell}
data [a] <p :: a -> a -> Prop> 
  = []<p>
  | (:) h:a [a<p h>]<p>

type IncrList a = [a] <\h v -> h <= v>
~~~~~

- h<sub>1</sub> : h<sub>2</sub> : h<sub>3</sub> : [] :: IncList a
    - h<sub>1</sub> :: a 
    - h<sub>2</sub> :: {v:a | h<sub>1</sub> &le; v}
    - h<sub>3</sub> :: {v:a | h<sub>1</sub> &le; v &and; h<sub>2</sub> &le; v } 
    - [] :: IncList {v:a | h<sub>1</sub> &le; v &and; h<sub>2</sub> &le; v }

## Increasing List (4/4)

~~~~~{.haskell}
data [a] <p :: a -> a -> Prop> 
  = []<p>
  | (:) h:a [a<p h>]<p>

type IncrList a = [a] <\h v -> h <= v>
~~~~~

- h<sub>1</sub> : h<sub>2</sub> : h<sub>3</sub> : [] :: IncList a
    - h<sub>1</sub> :: a 
    - h<sub>2</sub> :: {v:a | h<sub>1</sub> &le; v}
    - h<sub>3</sub> :: {v:a | h<sub>1</sub> &le; v &and; h<sub>2</sub> &le; v } 
    - [] :: IncList {v:a | h<sub>1</sub> &le; v &and; h<sub>2</sub> &le; v &and; h<sub>3</sub> &le; v}


## insert to an IncrList (1/2)

~~~~~{.haskell}
insert :: y:a -> IncrList a -> IncrList a
insert y []     = []
insert y (x:xs) | y < x     = y : x : xs 
                | otherwise = y : insert y xs
~~~~~

- Given
    - x  :: a
    - xs :: IncrList {v:a | x &le; v}
- If y < x, then
    - xs     :: IncrList {v:a | x &le; v &and; y &le; v}
    - x      :: {v:a | y &le; v}
    - x:xs   :: IncrList {v:a | y &le; v}
    - y:x:xs :: IncrList a

## insert to an IncrList (2/2)

~~~~~{.haskell}
insert :: y:a -> IncrList a -> IncrList a
insert y []     = []
insert y (x:xs) | y < x     = y : x : xs 
                | otherwise = y : insert y xs
~~~~~

- Given
    - x  :: a
    - xs :: IncrList {v:a | x &le; v}
- Otherwise (x &le; y)
    - y             :: {v:a | x &le; v}
    - insert y xs   :: IncrList {v:a | x &le; v}
    - x:insert y xs :: IncrList a


## Outline
- Introduction 
    - Monomorphic Refinements
- Applications
    - Refinements and Type Classes
    - Indexed Refinements
    - Recursive Refinements
    - <strong>Inductive Refinements</strong>
- Evaluation



## length via foldr
~~~~~{.haskell}
length ys = foldr f 0 ys
   where f x acc -> acc + 1
~~~~~

- Relation : lengthR :: ([a], Int)
    - lengthR ys v <=> len ys = v
- Given 
     - lengthR([], 0)
     - lengthR(xs, length xs) => lengthR(x:xs, f x (length xs))
- We have
     - lengthR(ys, length ys)

## append via foldr
~~~~~{.haskell}
append ys zs = foldr f  zs ys
  where f x acc -> x:acc
~~~~~

- Relation : appendR :: ([a], [a])
    - appendR ys v <=> len v = len ys + len zs
- Given 
     - appendR([], zs)
     - appendR(xs, append xs zs) => appendR(x:xs, f x (append xs zs))
- We have 
     - appendR(ys, append ys zs)

## Generalize: Structural Induction
~~~~~{.haskell}
foldr f z []     = z
foldr f z (x:xs) = f x (foldr f z xs)
~~~~~

- Relation : R :: ([a], b)
- Given 
    - R([], z)
    - R(xs, foldr f z xs) => R(x:xs, f x (foldr f x xs))
- We have
    - R(ys, foldr f z ys)


## Structural Induction via Abstract Refinements

~~~~~{.haskell}
foldr f z []     = z
foldr f z (x:xs) = f x (foldr f z xs)
~~~~~

-------------------------------------------------------      ----------------------
Relation : R :: ([a], b)                                     p :: [a] -> b -> Prop 
R([], z)                                                     z :: b\<p []\>
R(xs, foldr f z xs) => R(x:xs, f x (foldr f x xs))           f :: xs:[a] -> x :a -> b\<xs\> -> b\<x:xs\>
-------------------------------------------------------      ----------------------

- We have
    - ys :: [a] -> foldr f z ys :: b\<ys\>

## Typechecking foldr

~~~~~{.haskell}
foldr' f z []     = z
foldr' f z (x:xs) = f xs x (foldr' f z xs)
~~~~~

-------------------------------------------------------      ----------------------
Relation : R :: ([a], b)                                     p :: [a] -> b -> Prop 
R([], z)                                                     z :: b\<p []\>
R(xs, foldr f z xs) => R(x:xs, f x (foldr f x xs))           f :: xs:[a] -> x :a -> b\<xs\> -> b\<x:xs\>
-------------------------------------------------------      ----------------------

- We have
    - ys :: [a] -> foldr f z ys :: b\<ys\>


~~~~~{.haskell}
foldr' :: forall <p :: [a] -> b -> Prop>
           op :: xs:[a] -> x:a -> b<p xs> -> b<p x:xs> -> 
           z  :: b <p []> -> 
           ys :: [a] -> 
           b<p ys>
~~~~~


## Typechecking length
~~~~~{.haskell}
length ys = foldr f 0 ys
   where f _ x acc -> acc + 1
~~~~~

- lengthR ys v <=> v = len ys
- p = \\ys v -> v = len ys

~~~~~{.haskell}
length :: ys : [a] -> {v:[a] | v = len ys}
~~~~~
 
## Typechecking append
~~~~~{.haskell}
append ys zs = foldr f  zs ys
  where f _ x acc -> x:acc
~~~~~

- appendR ys v <=> len v = len ys + len zs
- p = \\ys v -> len v = len xs + len ys

~~~~~{.haskell}
append :: xs : [a] -> ys : [a] -> {v:[a] | len v = len xs + len ys}
~~~~~
 

## Outline
- Introduction 
    - Monomorphic Refinements
- Applications
    - Refinements and Type Classes
    - Indexed Refinements
    - Recursive Refinements
    - Inductive Refinements
- <strong>Evaluation<strong>


## The tool

- HSolve : implemented in Haskell
- Implements liquid type algorithm
    - predicates: refinement variables + arguments
- Input
    - haskell code
    - type specifications
    - qualifiers
- Output
    - Safe + annotated program
    - Unsafe + error location

## Benchmarks

- Benchmarks

Program                      LOC   Annotation      Time(s)     
------------------- ------------ ------------ ------------
Micro                         32           23            2
Vector                        33           53            5
ListSort                      29            5            3
Data.List.Sort                71            4            8
Data.Set.Splay               136          152           13
Data.Map.Base               1696          261          136


- Challenges
      - ghost variables
      - reorder arguments
      - express complicated specifications

## Conclution

Abstract Refinements

- increase expressiveness without increasing complexity
- relate arguments with result, ie, maxInt
- relate expressions inside a stucture, ie, Vector, List 
- express recursive properties, ie, List
- express inductive properties, ie, foldr

