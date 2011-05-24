{- A formalization of some notions from the untyped lambda calculus.

  The main goal is to check how will the locally nameless approach (de Bruijn indices for
  bound variables and names for free variables) work in practice for me.
  
  If it proves to be useful then this work will get extended to formalize the Simply Typed Lambda Calcules.
-}

module UntypedLC where

open import Data.Nat
open import Data.Fin

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- the main module is parametrized by the name type, a notion of equality and a comparison that decided the equality

module Untyped (Name : Set) (_≈_ : Name → Name → Set) (_==_ : (n1 n2 : Name) → Dec (n1 ≈ n2)) where
  
  -- the type of terms, parametrized by an upper bound on the number of abstractions (binders)

  -- B is the bounded variable const., use of Fin allows us to statically guarantee that the indexes are
  -- correct (however terms like B zero are still allowed, even though they don't represent a λ-term)
  data Term : ℕ → Set where
    B   : (n : ℕ) → (i : Fin n)        → Term n                   
    F   : (n : ℕ) → (z : Name)         → Term n
    _$_ : {n : ℕ} → (t1 t2 : Term n)   → Term n
    ƛ   : {n : ℕ} → (t : Term (suc n)) → Term n
  
  
  -- now we want to define the main two functions from the McBride & McKinna paper

  abstraction-iter : {n : ℕ} → (z : Name) → (t : Term n) → (Term (suc n)

  
  -- abstract takes a name and binds it at the top-most level
  -- i.e. abstract x (λ. 0 x) ==> λ (λ 0 1)
  abstraction : {n : ℕ} → (z : Name) → (t : Term n) → Term (suc n)
  abstraction z t = abstraction-iter z t 0