module SimpleDeBruijinTheorems where

open import Data.Empty
open import Data.Nat
open import Data.Nat.Theorems
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import SimpleDeBruijin

{- 
  Reductions and shifts
-}

lem-up-and-down : ∀ (n : ℕ) (t : Term) → t ≡ ↓[ n ] (↑[ 1 ∶ n ] t)
lem-up-and-down n (# n')  with inspect (n ≤? n')
lem-up-and-down n (# n') | yes p with-≡ eq rewrite eq with inspect (n ≤? suc n')
... | yes p2 with-≡ eq2 rewrite eq2 = refl
... | no ¬p2 with-≡ eq2 = ⊥-elim (¬p2 (lem-≤-l+ n 1 n' p))
lem-up-and-down n (# n') | no ¬p with-≡ eq rewrite eq with 1 ≡ 1
... | lem rewrite eq = refl
lem-up-and-down n (f $ a) = cong₂ (λ x y → x $ y) (lem-up-and-down n f) (lem-up-and-down n a)
lem-up-and-down n (ƛ t)   = cong ƛ (lem-up-and-down (suc n) t)


-- id t →β t
beta-id : ∀ (t : Term) → beta (# 0) t ≡ t
beta-id (# n)   = refl
beta-id (f $ a) = cong₂ (λ x y → x $ y) (beta-id f) (beta-id a)
beta-id (ƛ t)   = cong ƛ (sym (lem-up-and-down (suc zero) t))

{-
  ≡βη properties
-}

-- id t ≡βη t
lem-beta2 : ∀ (t : Term) → beta (# 0) t ≡βη t
lem-beta2 t rewrite beta-id t = refl t

lem-beta : ∀ (t : Term) → (ƛ (# 0)) $ t ≡βη t
lem-beta t = tran (β (# zero) t) (lem-beta2 t)  

{-
  ⟶β properties
-}

ω : Term
ω = (ƛ (# 0 $ # 0)) $ (ƛ (# 0 $ # 0))

-- the ⟶β relation can have cycles - that is, some expressions diverge when evaluated
lem-ω : ω ⟶β ω
lem-ω = β (# zero $ # zero) (ƛ (# zero $ # zero)) (abs (# zero $ # zero))


{-
  properties of normal forms
-}

lem-var-nf : ∀ (n : ℕ) → inNormalForm (# n)
lem-var-nf n = nf (# n) (λ t' → λ ())

lem-abs-nf : ∀ (t : Term) → inNormalForm (ƛ t)
lem-abs-nf t = nf (ƛ t) (λ t' → λ ())

-- inversion lemma, characterization of NFs
-- this lemma is false : t ≡ # 0 $ # 1 cannot be reduced, yet it is not in the given form
-- lem-nfs : ∀ (t : Term) → inNormalForm t → ∃ (λ n → t ≡ # n) ⊎ ∃ (λ t' → t ≡ ƛ t')
