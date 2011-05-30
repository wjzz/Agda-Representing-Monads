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

{- BASE in lem-∈-app-l lem-∈-app-r lem-∈-app lem-∈-neq lem-∈-inside lem-∈-extend-l lem-∈-extend-r  -}

-- properties of permutations
data Permutation {A : Set} : (l l2 : List A) → Set where
  p-nil : Permutation [] []
  p-cons : (x : A) (xs xs' ys ys' : List A) → Permutation xs xs' → Permutation ys ys' →
    Permutation (x ∷ (xs ++ ys)) (xs' ++ (x ∷ ys'))


perm-in : ∀ {A : Set}(x : A)(l l' : List A) → (cmp : ∀ (a1 a2 : A) → Dec (a1 ≡ a2)) → 
          Permutation l l' →  x ∈ l → x ∈ l'
perm-in x .[] .[] cmp p-nil x∈l = x∈l
perm-in x .(x' ∷ xs ++ ys) .(xs' ++ x' ∷ ys') cmp (p-cons x' xs xs' ys ys' y y') x∈l with cmp x x'
perm-in x .(x' ∷ xs ++ ys) .(xs' ++ x' ∷ ys') cmp (p-cons x' xs xs' ys ys' y y') x∈l | yes p rewrite p = lem-∈-inside x' xs' ys'
perm-in x .(x' ∷ xs ++ ys) .(xs' ++ x' ∷ ys') cmp (p-cons x' xs xs' ys ys' y y') x∈l | no ¬p with lem-∈-app x xs ys cmp (lem-∈-neq x x' (xs ++ ys) ¬p x∈l)
perm-in x .(x' ∷ xs ++ ys) .(xs' ++ x' ∷ ys') cmp (p-cons x' xs xs' ys ys' y y') x∈l | no ¬p | inj₁ l with perm-in x xs xs' cmp y l
perm-in x .(x' ∷ xs ++ ys) .(xs' ++ x' ∷ ys') cmp (p-cons x' xs xs' ys ys' y y') x∈l | no ¬p | inj₁ l | rec 
  = lem-∈-extend-r x xs' (x' ∷ ys') rec
perm-in x .(x' ∷ xs ++ ys) .(xs' ++ x' ∷ ys') cmp (p-cons x' xs xs' ys ys' y y') x∈l | no ¬p | inj₂ r with perm-in x ys ys' cmp y' r
perm-in x .(x' ∷ xs ++ ys) .(xs' ++ x' ∷ ys') cmp (p-cons x' xs xs' ys ys' y y') x∈l | no ¬p | inj₂ r | rec 
  = lem-∈-extend-l x (x' ∷ ys') xs' (in-drop x' rec)

perm-in-rev : ∀ {A : Set}(x : A)(l l' : List A) → (cmp : ∀ (a1 a2 : A) → Dec (a1 ≡ a2)) → 
               Permutation l l' →  x ∈ l' → x ∈ l
perm-in-rev x .[] .[] cmp p-nil x∈l' = x∈l'
perm-in-rev x .(x' ∷ xs ++ ys) .(xs' ++ x' ∷ ys') cmp (p-cons x' xs xs' ys ys' y y') x∈l' with lem-∈-app x xs' (x' ∷ ys') cmp x∈l'
perm-in-rev x .(x' ∷ xs ++ ys) .(xs' ++ x' ∷ ys') cmp (p-cons x' xs xs' ys ys' y y') x∈l' | inj₁ l 
  = in-drop x' (lem-∈-extend-r x xs ys (perm-in-rev x xs xs' cmp y l))
perm-in-rev x .(x ∷ xs ++ ys) .(xs' ++ x ∷ ys') cmp (p-cons .x xs xs' ys ys' y y') x∈l'   | inj₂ (in-keep .x .ys') 
  = in-keep x (xs ++ ys)
perm-in-rev x .(x' ∷ xs ++ ys) .(xs' ++ x' ∷ ys') cmp (p-cons x' xs xs' ys ys' y y') x∈l' | inj₂ (in-drop .x' z) 
  = in-drop x' (lem-∈-extend-l x ys xs (perm-in-rev x ys ys' cmp y' z))

{- BASE in perm-in perm-in-rev -}


