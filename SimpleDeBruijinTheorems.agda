module SimpleDeBruijinTheorems where

open import Data.Empty
open import Data.List
open import Data.List.Theorems
open import Data.Nat
open import Data.Nat.Theorems
open import Data.Maybe
open import Data.Product hiding (map)
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


{- Some auxillary functions. Defined for practice. -}

depth : Term → ℕ
depth (# n)   = 0
depth (f $ a) = depth f ⊔ depth a
depth (ƛ t)   = 1 + depth t

size : Term → ℕ
size (# n)   = 1
size (f $ a) = size f + size a
size (ƛ t)   = 1 + size t

lem-depth-<-size : ∀ (t : Term) → depth t < size t
lem-depth-<-size (# n)      = s≤s z≤n
lem-depth-<-size (t₁ $ t₂)  = lem-<-cong (lem-depth-<-size t₁) (lem-depth-<-size t₂)
lem-depth-<-size (ƛ t)      = s≤s (lem-depth-<-size t)



{- Can we formalize the upshifting operation somehow? -}

-- a path
data Direction : Set where 
  Left Right Down : Direction

path : Set
path = List Direction          -- empty list represents a "Here" value

-- walking down the path
walk : (t : Term) (p : path) → Maybe ℕ

-- right directions
walk (# n)   []           = just n
walk (f $ a) (Left ∷ xs)  = walk f xs
walk (f $ a) (Right ∷ xs) = walk a xs
walk (ƛ t)   (Down ∷ xs)  = walk t xs

-- wrong cases
walk (f $ a) [] = nothing
walk (ƛ t) [] = nothing
walk (# n) (Left ∷ xs) = nothing
walk (ƛ t) (Left ∷ xs) = nothing
walk (# n) (Right ∷ xs) = nothing
walk (ƛ t) (Right ∷ xs) = nothing
walk (# n) (Down ∷ xs) = nothing
walk (f $ a) (Down ∷ xs) = nothing


-- paths to all variables
vars : (t : Term) → List path
vars (# n)   = [] ∷ []
vars (f $ a) = map (λ l → Left ∷ l) (vars f) ++ map (λ l → Right ∷ l) (vars a)
vars (ƛ t)   = map (λ l → Down ∷ l) (vars t)


-- paths to all bound variables
bound-vars-level : (k : ℕ) → (t : Term) → List path
bound-vars-level k (# n) with suc n ≤? k             -- is n < k ?
...                      | yes p = [] ∷ []           -- n is bound
...                      | no ¬p = []                -- n is unbound
bound-vars-level k (f $ a) = map (λ l → Left ∷ l) (bound-vars-level k f) ++ map (λ l → Right ∷ l) (bound-vars-level k a)
bound-vars-level k (ƛ t)   = map (λ l → Down ∷ l) (bound-vars-level (1 + k) t)

bound-vars : (t : Term) → List path
bound-vars t = bound-vars-level 0 t


-- paths to all free variables
free-vars-level : (k : ℕ) → (t : Term) → List path
free-vars-level k (# n) with suc n ≤? k             -- is n < k ?
...                      | no ¬p = [] ∷ []           -- n is free
...                      | yes p = []                -- n is bound
free-vars-level k (f $ a) = map (λ l → Left ∷ l) (free-vars-level k f) ++ map (λ l → Right ∷ l) (free-vars-level k a)
free-vars-level k (ƛ t)   = map (λ l → Down ∷ l) (free-vars-level (1 + k) t)

free-vars : (t : Term) → List path
free-vars t = free-vars-level 0 t


-- now we can express the corectness of the upshifting operation

-- all paths returned by vars are correct:
lem-vars-correct : ∀ (t : Term) (p : path) → p ∈ vars t → ∃ (λ n → just n ≡ walk t p)
lem-vars-correct (# n) [] pin = n , refl
lem-vars-correct (# n) (Left ∷ xs) (∈-drop .(Left ∷ xs) .[] .[] ())
lem-vars-correct (# n) (Right ∷ xs) (∈-drop .(Right ∷ xs) .[] .[] ())
lem-vars-correct (# n) (Down ∷ xs) (∈-drop .(Down ∷ xs) .[] .[] ())
lem-vars-correct (f $ a) p pin = {!!}
lem-vars-correct (ƛ t) [] pin = {!!}
lem-vars-correct (ƛ t) (x ∷ xs) pin = {!!}
