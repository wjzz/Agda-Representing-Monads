module SimpleDeBruijinTheorems where

open import Data.Empty
open import Data.Nat
open import Data.Nat.Theorems
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import SimpleDeBruijin

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

