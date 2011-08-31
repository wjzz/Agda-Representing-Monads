module FinUtils where

open import Data.Empty
open import Data.Fin hiding (_<_)
--open import Data.Fin.Props renaming (_≟_ to _≟Fin_)
open import Data.Nat renaming (_≤_ to _≤ℕ_)
open import Data.Product

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- maximal {0,1,2,...,n-1} = n-1

data maximal : {n : ℕ} → Fin n → Set where
  zero : maximal {1} zero
  suc  : {n : ℕ} → {i : Fin n} 
       → maximal {n} i 
       → maximal (suc i)

getMaximal : (n : ℕ) → Σ[ i ∶ Fin (suc n) ](maximal i)
getMaximal zero = zero , zero
getMaximal (suc n) with getMaximal n
... | i , max = suc i , suc max 

data _<Fin<_ : {n : ℕ} → Fin n → Fin n → Set where
  z<s : {n : ℕ} → {i   : Fin n} → zero <Fin< suc i 
  s<s : {n : ℕ} → (i j : Fin n) → i <Fin< j → suc i <Fin< suc j

postulate
  nonMaximal : {n : ℕ} {i m : Fin n} → maximal m → i ≢ m → i <Fin< m

-- helper for cases when pattern matching breaks
max-inv : {n : ℕ}{i : Fin n} → maximal (suc i) → maximal i
max-inv (suc y) = y

fin0 : {A : Set} → Fin 0 → A
fin0 ()

reduce : {n : ℕ} (i m : Fin (suc n)) → maximal m → i <Fin< m → Fin n
reduce {zero} i .zero zero ()
reduce {zero} i .(suc i') (suc {.0} {i'} y) rel = fin0 i'
reduce {suc n} .zero .(suc i) max (z<s {.(suc n)} {i}) = zero
reduce {suc n} .(suc i) .(suc j) (suc y) (s<s i j y')  = suc (reduce i j y y')
  
