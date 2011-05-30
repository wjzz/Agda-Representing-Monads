{- An formalization of the λ calculus using DeBruijin indices as explained in TAPL, Pierce -}

module DeBruijin where

open import Data.Nat
open import Data.Nat.Theorems

open import Data.Product

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


{- Terms are indexed by the maximum depth of the binder stack -}

data Term : ℕ → Set where
  #⟨_,_⟩ : {k : ℕ} → (n : ℕ) → n < k → Term k
  _$_    : {k : ℕ} → (t₁ t₂ : Term k) → Term k
  ƛ      : {k : ℕ} → (t : Term (1 + k)) → Term k 
  

{- Some auxillary functions. Defined for practice. -}

depth : {k : ℕ} → Term k → ℕ
depth (#⟨ n , y ⟩) = 0
depth (t₁ $ t₂)    = depth t₁ ⊔ depth t₂
depth (ƛ t)        = 1 + depth t

size : {k : ℕ} → Term k → ℕ
size (#⟨ n , y ⟩) = 1
size (t₁ $ t₂)    = size t₁ + size t₂
size (ƛ t)        = 1 + size t

lem-depth-<-size : ∀ {k} (t : Term k) → depth t < size t
lem-depth-<-size #⟨ n , y ⟩ = s≤s z≤n
lem-depth-<-size (t₁ $ t₂)  = lem-<-cong (lem-depth-<-size t₁) (lem-depth-<-size t₂)
lem-depth-<-size (ƛ t)      = s≤s (lem-depth-<-size t)

{- The shifting operations -}

-- upshift
↑[_] : {k : ℕ} → (n : ℕ) → (t : Term k) → ∃ Term
↑[ n ] #⟨ n' , y ⟩ = {!!}
↑[ n ] (t₁ $ t₂) = ?
↑[ n ] (ƛ t) = {!!}