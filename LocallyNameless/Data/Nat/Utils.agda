module Data.Nat.Utils where

open import Data.Empty
open import Data.Nat
open import Data.Product
open import Data.Sum

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
{- 
  ------------------------------------
            Properties of _≟_
  ------------------------------------
-}

lem-≟-refl : ∀ (n : ℕ) → (n ≟ n) ≡ yes refl
lem-≟-refl zero = refl
lem-≟-refl (suc n) rewrite lem-≟-refl n = refl


lem-less-means-no : ∀ (n m : ℕ) → (n < m) → (p : n ≡ m) → ⊥
lem-less-means-no .(suc n) .(suc n) (s≤s {.(suc n)} {n} m≤n) refl = lem-less-means-no n n m≤n refl