module Data.List.Utils where

open import Data.List

open import Data.Empty
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

infix 3 _∈_

data _∈_ {A : Set} : (a : A) → (l : List A) → Set where
  in-keep : (a : A)(xs : List A) → a ∈ a ∷ xs
  in-drop : {a : A}{xs : List A} (x : A) → a ∈ xs → a ∈ x ∷ xs

_∉_ : {A : Set} (a : A)(l : List A) → Set
a ∉ l = ¬ (a ∈ l)

{- BASE global ⊥-elim cong cong₂ -}

lem-∈-eq : ∀ {A : Set} (a a' : A)(xs : List A) → a ≡ a' → a ∈ a' ∷ xs
lem-∈-eq .a' a' xs refl = in-keep a' xs

lem-∉-neq-tail : ∀ {A : Set} (a a' : A)(xs : List A) → a ≢ a' → a ∉ xs → a ∉ (a' ∷ xs)
lem-∉-neq-tail .a' a' xs neq a∉xs (in-keep .a' .xs) = neq refl
lem-∉-neq-tail a a' xs neq a∉xs (in-drop .a' y) = a∉xs y

lem-∉-cons : ∀ {A : Set} (a a' : A)(xs : List A) → a ∉ (a' ∷ xs) → a ≢ a'
lem-∉-cons a a' xs x eq rewrite eq = x (in-keep a' xs)


-- extension lemmas

lem-∈-extend-l : ∀ {A : Set} (a : A)(xs ys : List A) → a ∈ xs → a ∈ ys ++ xs
lem-∈-extend-l a xs [] inn = inn
lem-∈-extend-l a xs (x ∷ xs') inn = in-drop x (lem-∈-extend-l a xs xs' inn)

lem-∈-extend-r : ∀ {A : Set} (a : A)(xs ys : List A) → a ∈ xs → a ∈ xs ++ ys
lem-∈-extend-r a .(a ∷ xs) ys (in-keep .a xs) = in-keep a (xs ++ ys)
lem-∈-extend-r a .(x ∷ xs) ys (in-drop {.a} {xs} x y) = in-drop x (lem-∈-extend-r a xs ys y)

-- ∉ and ++

lem-∈-app-l : ∀ {A : Set} (a : A)(xs ys : List A) → a ∉ (xs ++ ys) → a ∉ xs
lem-∈-app-l a [] ys p ()
lem-∈-app-l a (x ∷ xs) ys nin axs = nin (lem-∈-extend-r a (x ∷ xs) ys axs) 

lem-∈-app-r : ∀ {A : Set} (a : A)(xs ys : List A) → a ∉ (xs ++ ys) → a ∉ ys
lem-∈-app-r a xs ys nin ays = nin (lem-∈-extend-l a ys xs ays)

lem-∈-inside : ∀ {A : Set}(a : A) (xs ys : List A) → a ∈ xs ++ (a ∷ ys)
lem-∈-inside a [] ys = in-keep a ys
lem-∈-inside a (x ∷ xs) ys = in-drop x (lem-∈-inside a xs ys)

lem-∈-neq : ∀ {A : Set}(a a' : A) (xs : List A) → a ≢ a' → a ∈ a' ∷ xs → a ∈ xs
lem-∈-neq .a' a' xs neq (in-keep .a' .xs) = ⊥-elim (neq refl)
lem-∈-neq a a' xs neq (in-drop .a' y) = y

lem-∈-app : ∀ {A : Set}(a : A) (xs ys : List A) → (cmp : ∀ (a1 a2 : A) → Dec (a1 ≡ a2)) → a ∈ xs ++ ys → a ∈ xs ⊎ a ∈ ys
lem-∈-app a [] ys cmp inn = inj₂ inn
lem-∈-app a (x ∷ xs) ys cmp inn with cmp a x
lem-∈-app a (x ∷ xs) ys cmp inn | yes p rewrite p = inj₁ (in-keep x xs)
lem-∈-app .x (x ∷ xs) ys cmp (in-keep .x .(xs ++ ys)) | no ¬p = inj₁ (in-keep x xs)
lem-∈-app a (x ∷ xs) ys cmp (in-drop .x y) | no ¬p with lem-∈-app a xs ys cmp y
lem-∈-app a (x ∷ xs) ys cmp (in-drop .x y) | no ¬p | inj₁ l = inj₁ (in-drop x l)
lem-∈-app a (x ∷ xs) ys cmp (in-drop .x y) | no ¬p | inj₂ r = inj₂ r

{- BASE in lem-∈-app-l lem-∈-app-r lem-∈-app lem-∈-neq lem-∈-inside lem-∈-extend-l lem-∈-extend-r -}

-- properties of permutations

data Permutation {A : Set} : (l1 l2 : List A) → Set where
  p-nil   : Permutation [] []
  p-cons  : (x : A) (xs xs' : List A) → Permutation xs xs' → Permutation (x ∷ xs) (x ∷ xs')
  p-swap  : (x y : A)(l : List A) → Permutation (x ∷ y ∷ l) (y ∷ x ∷ l)
  p-trans : (l1 l2 l3 : List A) → Permutation l1 l2 → Permutation l2 l3 → Permutation l1 l3


perm-id : ∀ {A : Set}(l : List A) → Permutation l l
perm-id [] = p-nil
perm-id (x ∷ xs) = p-cons x xs xs (perm-id xs)

perm-sym : ∀ {A : Set}(l1 l2 : List A) → Permutation l1 l2 → Permutation l2 l1
perm-sym .[] .[] p-nil = p-nil
perm-sym .(x ∷ xs) .(x ∷ xs') (p-cons x xs xs' y) = p-cons x xs' xs (perm-sym xs xs' y)
perm-sym .(x ∷ y ∷ l) .(y ∷ x ∷ l) (p-swap x y l) = p-swap y x l
perm-sym l1 l2 (p-trans .l1 l3 .l2 y y') = p-trans l2 l3 l1 (perm-sym l3 l2 y') (perm-sym l1 l3 y)

{- BASE perm perm-id perm-sym -}

perm-in : ∀ {A : Set}(x : A)(l l' : List A) → (cmp : ∀ (a1 a2 : A) → Dec (a1 ≡ a2)) → 
          Permutation l l' →  x ∈ l → x ∈ l'
perm-in x .[] .[] cmp p-nil x∈l = x∈l
perm-in .x' .(x' ∷ xs) .(x' ∷ xs') cmp (p-cons x' xs xs' y) (in-keep .x' .xs) = in-keep x' xs'
perm-in x .(x' ∷ xs) .(x' ∷ xs') cmp (p-cons x' xs xs' y) (in-drop .x' y') = in-drop x' (perm-in x xs xs' cmp y y')
perm-in .x' .(x' ∷ y ∷ l) .(y ∷ x' ∷ l) cmp (p-swap x' y l) (in-keep .x' .(y ∷ l)) = in-drop y (in-keep x' l)
perm-in .y .(x' ∷ y ∷ l) .(y ∷ x' ∷ l) cmp (p-swap x' y l) (in-drop .x' (in-keep .y .l)) = in-keep y (x' ∷ l)
perm-in x .(x' ∷ y ∷ l) .(y ∷ x' ∷ l) cmp (p-swap x' y l) (in-drop .x' (in-drop .y y')) = in-drop y (in-drop x' y')
perm-in x l l' cmp (p-trans .l l2 .l' y y') x∈l = perm-in x l2 l' cmp y' (perm-in x l l2 cmp y x∈l)


perm-in-rev : ∀ {A : Set}(x : A)(l l' : List A) → (cmp : ∀ (a1 a2 : A) → Dec (a1 ≡ a2)) → 
               Permutation l l' →  x ∈ l' → x ∈ l
perm-in-rev x .[] .[] x' p-nil x1 = x1
perm-in-rev .x0 .(x0 ∷ xs) .(x0 ∷ xs') x' (p-cons x0 xs xs' y) (in-keep .x0 .xs') = in-keep x0 xs
perm-in-rev x .(x0 ∷ xs) .(x0 ∷ xs') x' (p-cons x0 xs xs' y) (in-drop .x0 y') = in-drop x0 (perm-in-rev x xs xs' x' y y')
perm-in-rev .y .(x0 ∷ y ∷ l) .(y ∷ x0 ∷ l) x' (p-swap x0 y l) (in-keep .y .(x0 ∷ l)) = in-drop x0 (in-keep y l)
perm-in-rev .x0 .(x0 ∷ y ∷ l) .(y ∷ x0 ∷ l) x' (p-swap x0 y l) (in-drop .y (in-keep .x0 .l)) = in-keep x0 (y ∷ l)
perm-in-rev x .(x0 ∷ y ∷ l) .(y ∷ x0 ∷ l) x' (p-swap x0 y l) (in-drop .y (in-drop .x0 y')) = in-drop x0 (in-drop y y')
perm-in-rev x l l' x' (p-trans .l l2 .l' y y') x1 = perm-in-rev x l l2 x' y (perm-in-rev x l2 l' x' y' x1)

{- BASE in perm-in perm-in-rev -}

perm-swap : ∀ {A : Set}(x y : A)(l1 l2 : List A) → Permutation l1 l2 → Permutation (x ∷ y ∷ l1) (y ∷ x ∷ l2)
perm-swap x y .[] .[] p-nil = p-swap x y []
perm-swap x y .(x' ∷ xs) .(x' ∷ xs') (p-cons x' xs xs' y') = p-trans (x ∷ y ∷ x' ∷ xs) (y ∷ x ∷ x' ∷ xs) (y ∷ x ∷ x' ∷ xs')
                                                               (p-swap x y (x' ∷ xs))
                                                               (p-cons y (x ∷ x' ∷ xs) (x ∷ x' ∷ xs')
                                                                (p-cons x (x' ∷ xs) (x' ∷ xs') (p-cons x' xs xs' y')))
perm-swap x y .(x' ∷ y' ∷ l) .(y' ∷ x' ∷ l) (p-swap x' y' l) = p-trans (x ∷ y ∷ x' ∷ y' ∷ l) (y ∷ x ∷ x' ∷ y' ∷ l)
                                                                 (y ∷ x ∷ y' ∷ x' ∷ l) (p-swap x y (x' ∷ y' ∷ l))
                                                                 (p-cons y (x ∷ x' ∷ y' ∷ l) (x ∷ y' ∷ x' ∷ l)
                                                                  (p-cons x (x' ∷ y' ∷ l) (y' ∷ x' ∷ l) (p-swap x' y' l)))
perm-swap x y l1 l2 (p-trans .l1 l3 .l2 y' y0) = p-trans (x ∷ y ∷ l1) (y ∷ x ∷ l3) (y ∷ x ∷ l2)
                                                   (perm-swap x y l1 l3 y')
                                                   (p-cons y (x ∷ l3) (x ∷ l2) (p-cons x l3 l2 y0)) 


perm-nil : ∀ {A : Set}(l : List A) → Permutation [] l → l ≡ []
perm-nil [] perm = refl
perm-nil (x ∷ xs) (p-trans .[] l2 .(x ∷ xs) y y') rewrite (perm-nil l2 y) = perm-nil (x ∷ xs) y' 

{- BASE perm perm-swap perm-nil -}

postulate
  perm-app : ∀ {A : Set}(xs xs' ys ys' : List A) → Permutation xs xs' → Permutation ys ys' → Permutation (xs ++ ys) (xs' ++ ys')


{- the following proof typechecks, but may not be terminating -}
{-
perm-app : ∀ {A : Set}(xs xs' ys ys' : List A) → Permutation xs xs' → Permutation ys ys' → Permutation (xs ++ ys) (xs' ++ ys')
perm-app .[] .[] ys ys' p-nil perm-ys' = perm-ys'
perm-app .(x ∷ xs) .(x ∷ xs') ys ys' (p-cons x xs xs' y) perm-ys' = p-cons x (xs ++ ys) (xs' ++ ys')
                                                                      (perm-app xs xs' ys ys' y perm-ys')
perm-app .(x ∷ y ∷ l) .(y ∷ x ∷ l) ys ys' (p-swap x y l) perm-ys' = perm-swap x y (l ++ ys) (l ++ ys') (perm-app l l ys ys' (perm-id l) perm-ys')
perm-app xs xs' ys ys' (p-trans .xs l2 .xs' y y') perm-ys' = p-trans ((xs ++ ys)) ((l2 ++ ys')) ((xs' ++ ys')) p1 p2 where
  p1 : Permutation (xs ++ ys) (l2 ++ ys')
  p1 = perm-app xs l2 ys ys' y perm-ys'  

  p2 : Permutation (l2 ++ ys') (xs' ++ ys')
  p2 = perm-app l2 xs' ys' ys' y' (perm-id ys')
-}

{- BASE perm perm-app -}
