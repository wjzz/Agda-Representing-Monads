module Terms where

open import Data.Empty
open import Data.Fin hiding (_+_)
open import Data.Fin.Props renaming (_≟_ to _≟Fin_) 
open import Data.Nat renaming (_≤_ to _≤ℕ_)
open import Data.Vec
open import Data.Product

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import FinUtils

postulate
  Name    : Set

-- the notion of sets via vectors --

set : Set
set = ∃ (Vec Name)

size : set → ℕ
size (n , v) = n

carrier : (s : set) → Vec Name (size s)
carrier (_ , y) = y

-- we postulate the existence of a set of names

postulate
  -- equality of names is decidable
  _≟Name_ : Decidable {A = Name} _≡_

  x       : Name

  -- we can always generate a name fresh from a given finite set
  fresh   : (s : set) → Σ[ x ∶ Name ](¬ (x ∈ (carrier s)))

-- preterms --

-- Term n is a term with at most n binders = n bound variables

data Term : ℕ → Set where
  fvar : {n : ℕ} → (x   : Name)         → Term n
  bvar : {n : ℕ} → (m   : Fin n)        → Term n
  _∙_  : {n : ℕ} → (s t : Term n)       → Term n
  ƛ_   : {n : ℕ} → (t   : Term (suc n)) → Term n

-- example terms --

ω : Term 0
ω = ƛ (bvar (# 0) ∙ bvar (# 0))

Ω : Term 0
Ω = ω ∙ ω 

-----------------------
-- variable renaming --
-----------------------

{-
  Lifting of variables.

  The terms themselves do not change, but the scope of the 
  bound indexes are extended from n to m.

  example: 
    λ x . x (λ y. x y) ≈
    λ (0 ∙ (λ (1 ∙ 0)) ≈
    λ (0_1 ∙ (λ (1_2 ∙ 0_2))) may become (n = 0 ; m = 2)
    λ (0_3 ∙ (λ (1_4 ∙ 0_4)))
-}

rename : {n m : ℕ} → Term n → n ≤ℕ m → Term m
rename (fvar x) _ = fvar x
rename (bvar m) p = bvar (inject≤ m p)
rename (s ∙ t)  p = rename s p ∙ rename t p
rename (ƛ t)    p = ƛ rename t (s≤s p)

-- opening the outermost binder

openIter : {n : ℕ} → (i : Fin (suc n)) → maximal i → Term (suc n) → Name → Term n
openIter i max (fvar x) z = fvar x
openIter i max (bvar m) z with m ≟Fin i
... | yes p = fvar z
... | no ¬p = bvar (reduce m i max (nonMaximal max ¬p))
openIter i max (t ∙ u)  z = openIter i max t z ∙ openIter i max u z
openIter i max (ƛ t)    z = ƛ openIter (suc i) (suc max) t z

-- the type makes it clear that closing the 
-- outermost binder is pointless in a closed term

opening : {n : ℕ} → Term (suc n) → Name → Term n
opening {n} t x = openIter (proj₁ (getMaximal n)) (proj₂ (getMaximal n)) t x

-- substitution --

_[_:=_] : {n : ℕ}(t : Term n)(x : Name)(s : Term 0) → Term n
fvar z   [ x := s ] with z ≟Name x
... | yes p = rename s z≤n
... | no ¬p = fvar z
bvar m   [ x := s ] = bvar m
(t ∙ t') [ x := s ] = t [ x := s ] ∙ t' [ x := s ]
(ƛ t)    [ x := s ] = ƛ (t [ x := s ])

-- substitution for the outermost binder

-- INV: i points to the outermost lambda (zero at first)
substOuterIter : {n : ℕ} → (i : Fin (suc n)) → maximal i → Term (suc n) → Term 0 → Term n
substOuterIter i max (fvar x) s = fvar x
substOuterIter i max (bvar m) s with m ≟Fin i
... | yes p = rename s z≤n
... | no ¬p = bvar (reduce m i max (nonMaximal max ¬p))
substOuterIter i max (t ∙ u)  s = substOuterIter i max t s ∙ substOuterIter i max u s
substOuterIter i max (ƛ t)    s = ƛ substOuterIter (suc i) (suc max) t s

-- the type makes it clear that closing the 
-- outermost binder is pointless in a closed term

substOuter : {n : ℕ} → Term (suc n) → Term 0 → Term n
substOuter {n} t s = substOuterIter (proj₁ (getMaximal n)) (proj₂ (getMaximal n)) t s

-- abstraction --

-- abstracting over an existing variable by replacing it with a pointer 
-- to the topmost binder (but without adding it yet)

abstractIter : {n : ℕ} → Fin (suc n) → Term n → Name → Term (suc n)
abstractIter i (fvar z) x with x ≟Name z
... | yes p = bvar i
... | no ¬p = fvar z
abstractIter i (bvar m) x = bvar (suc m) -- or raise?
abstractIter i (s ∙ t)  x = abstractIter i s x ∙ abstractIter i t x
abstractIter i (ƛ t)    x = ƛ (abstractIter (suc i) t x)

abstraction : {n : ℕ} → Term n → Name → Term (suc n)
abstraction t x = abstractIter zero t x 

----------------------
-- notion of values --
----------------------

data value : Term 0 → Set where
  abs : (t : Term 1) → value (ƛ t)

--------------------
-- free variables --
--------------------

FV : {n : ℕ} → Term n → set
FV (fvar x) = _ , x ∷ []
FV (bvar m) = _ , []
FV (s ∙ t) with FV s | FV t
... | n , v1 | m , v2 = n + m , v1 ++ v2
FV (ƛ t) = FV t

--------------------
-- beta reduction --
--------------------

infix 4 _⟶β_

data _⟶β_ : Term 0 → Term 0 → Set where
  beta : (t : Term 1){s : Term 0}
       → (v : value s)
       → (ƛ t) ∙ s   ⟶β   substOuter t s 

  fun  : {t t' : Term 0}(s : Term 0)
       → (ind : t ⟶β t')
       → (t ∙ s ⟶β t' ∙ s)

  arg  : {s s' t : Term 0}
       → (v : value t)
       → (ind : s ⟶β s')
       → t ∙ s   ⟶β    t ∙ s'

-- examples of reductions --

postulate 
  lem-rename0 : (t : Term 0) → rename t z≤n ≡ t
  lem-rename1 : (t : Term 1) → rename t (s≤s z≤n) ≡ t
{-
lem-rename (fvar x) = refl
lem-rename (bvar zero) = refl
lem-rename (bvar (suc ()))
lem-rename (s ∙ t) rewrite lem-rename s | lem-rename t = refl
lem-rename (ƛ t) = {!!}

this proof needs generalization of 1 to pass the ƛ case
-}

-- (λx.x) t ⟶β t
id-red : ∀ (t : Term 1) → (ƛ (bvar zero)) ∙ (ƛ t) ⟶β (ƛ t)
id-red t with beta (bvar zero) (abs t)
... | lem rewrite lem-rename1 t = lem

Ω-red : Ω ⟶β Ω
Ω-red = beta _ (abs _)

