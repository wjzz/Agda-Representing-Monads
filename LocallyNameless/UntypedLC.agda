{- A formalization of some notions from the untyped lambda calculus.

  The main goal is to check how will the locally nameless approach (de Bruijn indices for
  bound variables and names for free variables) work in practice for me.
  
  If it proves to be useful then this work will get extended to formalize the Simply Typed Lambda Calcules.
-}

module UntypedLC where

open import Data.Nat
open import Data.Nat.Theorems
open import Data.Fin

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- the main module is parametrized by the name type, a notion of equality and a comparison that decided the equality


module Untyped (Name : Set) (_≈_ : Name → Name → Set) (≈-equiv : IsEquivalence _≈_)(_==_ : (n1 n2 : Name) → Dec (n1 ≈ n2)) where
  
  -- the type of terms
  infixl 5 _$_

  data Term : Set where
    B   : (i : ℕ)    → Term                   
    F   : (z : Name) → Term
    _$_ : (t1 t2 : Term) → Term
    ƛ   : (t : Term) → Term
  
  
  -- now we want to define the main two functions from the McBride & McKinna paper:
  -- * abstract

  abstraction-iter : (z : Name) → (t : Term) → ℕ → Term
  abstraction-iter z (B i) l = B i
  abstraction-iter z (F x) l with z == x
  abstraction-iter z (F x) l | yes p = B l
  abstraction-iter z (F x) l | no ¬p = F x
  abstraction-iter z (t1 $ t2) l = abstraction-iter z t1 l $ abstraction-iter z t2 l
  abstraction-iter z (ƛ t) l     = ƛ (abstraction-iter z t (suc l))


  -- abstract takes a name and binds it at the top-most level
  -- i.e. abstract x (λ. 0 x) ==> λ (λ 0 1)
  abstraction : (z : Name) → (t : Term) → Term
  abstraction z t = abstraction-iter z t 0

  -- and
  -- * instantiate
    
  instantiate-iter : (t : Term) → (s : Term) → ℕ → Term
  instantiate-iter (B i) s l with i ≟ l
  instantiate-iter (B i) s l | yes p = s
  instantiate-iter (B i) s l | no ¬p = B i
  instantiate-iter (F z) s l = F z
  instantiate-iter (t1 $ t2) s l = instantiate-iter t1 s l $ instantiate-iter t2 s l
  instantiate-iter (ƛ t) s l     = ƛ (instantiate-iter t s (suc l))


  -- instantiate takes a term t that came from ƛ t and replaces all occurences of the
  -- bound variable quantified at the top-most level by the given term s
  instantiate : (t s : Term) → Term
  instantiate t s = instantiate-iter t s 0

  
  -- having defined instantiate and abstraction we can now define subst as
  -- subst t x s ≡ t [ x ↦ s ] = instantiate (abstraction x t) s
  --
  -- however we will implement it directly, by essentially fusing the two functions

  _[_↦_] : (t : Term) → (x : Name) → (s : Term) → Term
  B i       [ x ↦ s ] = B i
  F z       [ x ↦ s ] with x == z
  F z       [ x ↦ s ] | yes p = s
  F z       [ x ↦ s ] | no ¬p = F z
  (t1 $ t2) [ x ↦ s ] = t1 [ x ↦ s ] $ t2 [ x ↦ s ]
  ƛ t       [ x ↦ s ] = ƛ (t [ x ↦ s ])


  infix 4 _≡βη_

  -- the βη equality
  data _≡βη_ : (t s : Term) → Set where
  
    -- equivalence relation rules
    refl : {t     : Term} → t ≡βη t
    symm : {t s   : Term} → t ≡βη s → s ≡βη t
    tran : {t s u : Term} → t ≡βη s → s ≡βη u → t ≡βη u

    -- congruence rules
    app : {t1 s1 t2 s2 : Term} → t1 ≡βη s1 → t2 ≡βη s2 → t1 $ t2 ≡βη s1 $ s2
    abs : {t s         : Term} → t  ≡βη s → ƛ t ≡βη ƛ s

    -- computational rules
    η : {t : Term} → ƛ (t $ B 0) ≡βη t
    β : (t s : Term) → (ƛ t) $ s ≡βη instantiate t s



{-
-----------------------------------------------------
   Some theorems about the notions defined so far
-----------------------------------------------------
-}

  -- derived automatically
  lem-apply-id : ∀ (t : Term) → (ƛ (B 0)) $ t ≡βη t
  lem-apply-id t = β (B zero) t

  -- unpacking some properties of ≈ (Name equality)

  ≈-refl : Reflexive (_≈_)
  ≈-refl = IsEquivalence.refl ≈-equiv
  
  {- Some false-starts 
  lem-subst-alternate : ∀ (t s : Term) (x : Name) → t [ x ↦ s ] ≡ instantiate (abstraction x t) s
  lem-subst-alternate-iter : ∀ (n : ℕ) (t s : Term) (x : Name) → t [ x ↦ s ] ≡ instantiate-iter (abstraction-iter x t n) s n
  -}