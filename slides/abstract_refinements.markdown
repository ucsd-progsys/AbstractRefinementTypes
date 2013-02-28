% Abstract Refinements
% Niki Vazou, Patrick Rondon , and Ranjit Jhala
% February 25, 2013

## The maxInt example

~~~~~{.haskell}
maxInt     :: Int -> Int -> Int
maxInt x y = if x > y then x else y
~~~~~

- Given
    - n1 :: {v:Int | v > 0} <: Int  
    - n2 :: {v:Int | v > 0} <: Int  

- We have
    - maxInt n1 n2 :: Int

- It should also be positive!

## Monomorphic Refinements (1/2)
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


## Monomorphic Refinements (2/2)

~~~~~{.haskell}
maxInt     :: forall <p :: Int -> Prop>. Int<p> -> Int<p> -> Int<p>
maxInt x y = if x > y then x else y
~~~~~

- Given
    - p  :: Int -> Prop
    - n1 :: {v:Int | v > 0}
    - n2 :: {v:Int | v > 0}

- Instantiate predicate
    - p = \\v -> v > 0

- We have
    - maxInt n1 n2 :: {v:a | v > 0}


## Outline
- Introduction 
    - Monomorphic Refinements
- Applications
    - <strong>Indexed Refinememts</strong>
    - Recursive Refinements
    - Inductive Refinements
- Evaluation

## A vector data type
~~~~~{.haskell}
data Vec a 
  = V {f :: i : Int -> a}
~~~~~

- Refine indices :
      - d :: Int -> Prop

- Refine values given their index :
      - r :: Int -> a -> Prop

## Index Refinements

~~~~~{.haskell}
data Vec a <d :: Int -> Prop, r :: Int -> a -> Prop>
  = V {f :: i : Int<d> -> a<r i>}
~~~~~

- Refine indices :
      - d :: Int -> Prop

- Refine values given their index :
      - r :: Int -> a -> Prop

## Constant Vector

~~~~~{.haskell}
create x = V $ \_ -> x
~~~~~

- Refine indices : all integers
      - d = \\v -> True 

- Refine values  : only x
      - r = \\i v -> v = x

~~~~~{.haskell}
create :: x:a -> Vec <\_ -> True, \_ v -> v = x> a
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

## Outline
- Introduction 
    - Monomorphic Refinements
- Applications
    - Indexed Refinememts
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

- Refine tail elements given the head:
    - p :: a -> a -> Prop

- h:tl :: [a]\<p\> iff h :: a &and; t :: [a \<p h\>]


## Increasing List (1/4)

~~~~~{.haskell}
data [a] <p :: a -> a -> Prop> 
  = []<p>
  | (:) h:a [a<p h>]<p>

type IncrList a = [a] <\h v -> h <= v>
~~~~~

- h1 : h2 : h3 : [] :: IncList a


## Increasing List (2/4)

~~~~~{.haskell}
data [a] <p :: a -> a -> Prop> 
  = []<p>
  | (:) h:a [a<p h>]<p>

type IncrList a = [a] <\h v -> h <= v>
~~~~~

- h1 :: a 
- h2:h3:[] :: IncList {v:a | h1 &le; v}

## Increasing List (3/4)

~~~~~{.haskell}
data [a] <p :: a -> a -> Prop> 
  = []<p>
  | (:) h:a [a<p h>]<p>

type IncrList a = [a] <\h v -> h <= v>
~~~~~

- h1 :: a 
- h2 :: {v:a | h1 &le; v}
- h3:[] :: IncList {v:a | h1 &le; v &and; h2 &le; v}

## Increasing List (4/4)

~~~~~{.haskell}
data [a] <p :: a -> a -> Prop> 
  = []<p>
  | (:) h:a [a<p h>]<p>

type IncrList a = [a] <\h v -> h <= v>
~~~~~

- h1 :: a 
- h2 :: {v:a | h1 &le; v}
- h3 :: {v:a | h1 &le; v &and; h2 &le; v}
- [] :: IncList {v:a | h1 &le; v &and; h2 &le; v &and; h3 &le; v}

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
    - Indexed Refinememts
    - Recursive Refinements
    - <strong>Inductive Refinements</strong>
- Evaluation



## A variant of foldr

~~~~~{.haskell}
foldr op z []     = z
foldr op z (x:xs) = op xs x (foldr op z xs)
~~~~~


## Typechecking foldr (1/3)

~~~~~{.haskell}
foldr op z []     = z
foldr op z (x:xs) = op xs x (foldr op z xs)
~~~~~

- Given 
    - p    :: [a] -> b -> Prop
    - op   :: xs:[a] -> x:a -> b\<xs\> -> b\<x:xs\>
    - z    :: b\<p []\>
    - x:xs :: [a]
- Assume 
    - foldr op z xs :: b\<xs\>
- Then 
    - op xs x (foldr op z xs) :: b\<x:xs\>
    - z                       :: b\<p []\>

## Typechecking foldr (2/3)

~~~~~{.haskell}
foldr op z []     = z
foldr op z (x:xs) = op xs x (foldr op z xs)
~~~~~

- Given 
    - p    :: [a] -> b -> Prop
    - op   :: xs:[a] -> x:a -> b\<xs\> -> b\<x:xs\>
    - z    :: b\<p []\>
    - x:xs :: [a]
- Assume 
    - foldr op z xs :: b\<xs\>
- Then 
    - foldr op z (x:xs)       :: b\<x:xs\>
    - foldr op z []           :: b\<x:xs\>

## Typechecking foldr (3/3)

~~~~~{.haskell}
foldr op z []     = z
foldr op z (x:xs) = op xs x (foldr op z xs)
~~~~~

- Given 
    - p    :: [a] -> b -> Prop
    - op   :: xs:[a] -> x:a -> b\<xs\> -> b\<x:xs\>
    - z    :: b\<p []\>
    - ys   :: [a]
- Then 
    - foldr op z ys           :: b\<ys\>

~~~~~{.haskell}
foldr :: forall <p :: [a] -> b -> Prop>
           op :: xs:[a] -> x:a -> b<p xs> -> b<p x:xs> -> 
           z  :: b <p []> -> 
           ys :: [a] -> 
           b<p ys>
~~~~~


## Using foldr (1/2)

~~~~~{.haskell}
foldr :: forall <p :: [a] -> b -> Prop>
           op :: xs:[a] -> x:a -> b<p xs> -> b<p x:xs> -> 
           z  :: b <p []> -> 
           ys :: [a] -> 
           b<p ys>
~~~~~

~~~~~{.haskell}
length = foldr (\_ _ n -> n+1) 0
~~~~~
 
p = \\xs v -> v = len xs

~~~~~{.haskell}
length :: zs : [a] -> {v:[a] | v = len zs}
~~~~~
 
## Using foldr (2/2)

~~~~~{.haskell}
foldr :: forall <p :: [a] -> b -> Prop>
           op :: xs:[a] -> x:a -> b<p xs> -> b<p x:xs> -> 
           z  :: b <p []> -> 
           ys :: [a] -> 
           b<p ys>
~~~~~

~~~~~{.haskell}
append ys zs = foldr (\_ -> (:)) zs ys
~~~~~
 
p = \\xs v -> len v = len xs + len ys

~~~~~{.haskell}
append :: xs : [a] -> ys : [a] -> {v:[a] | len v = len xs + len ys}
~~~~~
 

## Outline
- Introduction 
    - Monomorphic Refinements
- Applications
    - Indexed Refinememts
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

