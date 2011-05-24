{- A formalization of some notions from the Simply Typed lambda calculus. -}

module STLC where

open import Data.Empty
open import Data.List
open import Data.List.Utils
open import Data.Nat
open import Data.Nat.Utils

open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary


open import UntypedLC

-- the main module is parametrized by the name type, a notion of equality and a comparison that decided the equality


module SimplyTyped (Name : Set) (_≈_ : Name → Name → Set)(_==_ : (n1 n2 : Name) → Dec (n1 ≡ n2)) where

  
  open Untyped Name _≈_ _==_ 

  
  
  
  -- simple types

  data Type : Set where
    γ : Type
    _⇒_ : (τ1 τ2 : Type) → Type

  
  -- for contexts we will use a sugared notation for lists instead
  -- of a seperate datatype to minimalize the number of needed lemmas

  infix  3 _⟶β_
  infixl 40 _,_
  infix  50 _∶_
  infixr 60 _⇒_
   
  data Assingment : Set where
    _∶_ : (x : Name) → (τ : Type) → Assingment               -- variable type declaration/assignment

  Context : Set
  Context = List Assingment

  ∅ : Context
  ∅ = []

  _,_ : (Γ : Context) → (j : Assingment) → Context      -- a single assingment with the rest of the context
  Γ , j = j ∷ Γ
  

  -- for starters, we do not force the context to be a set wrt to the names

  data _⊢_∶_ : (Γ : Context) → (t : Term) → (τ : Type) → Set where
    ass : {z : Name}{τ : Type} {Γ : Context} → (z ∶ τ) ∈ Γ → Γ ⊢ F z ∶ τ

    app : {Γ : Context} {t s : Term} (τ₁ τ₂ : Type) →
          Γ ⊢ t ∶ τ₁ ⇒ τ₂   →   Γ ⊢ s ∶ τ₁   →    Γ ⊢ t $ s ∶ τ₂

    abs : {Γ : Context}{z : Name}{t : Term} (α τ : Type) →
          Γ , z ∶ α ⊢ t ∶ τ   →    Γ ⊢ ƛ (abstraction z t) ∶ α ⇒ τ

    -- other possibility
    -- this one is actually used in the document
    -- the approaches seem to be equivalent
  {-
    abs2 : {Γ : Context}{z : Name}{t : Term} (α τ : Type) →
           Γ , z ∶ α ⊢ instantiate (F z) t ∶ τ   →    Γ ⊢ ƛ t ∶ α ⇒ τ
  -}

  
  data value : (t : Term) → Set where
    abs : (t : Term) → value (ƛ t)

  value? : (t : Term) → Dec (value t)
  value? (B i)       = no (λ ())
  value? (F z)       = no (λ ())
  value? (_$_ t1 t2) = no (λ ())
  value? (ƛ t)       = yes (abs t)

  
  -- small-step reduction relation
  data _⟶β_ : (t t' : Term) → Set where
    β     : {t s : Term} → value s → (ƛ t) $ s ⟶β instantiate t s
    app-f : {t t' s : Term} → t ⟶β t'  → t $ s ⟶β t' $ s
    app-a : {t s s' : Term} → value t → s ⟶β s'  → t $ s ⟶β t $ s'


  {- some examples -}
  lem-id : (t : Term) → value t → (ƛ (B 0)) $ t ⟶β t
  lem-id t v = β v

  ω : Term
  ω = ƛ (B 0 $ B 0)

  Ω : Term
  Ω = ω $ ω

  lem-omega : Ω ⟶β Ω
  lem-omega = β (abs (Untyped._$_ (Untyped.B zero) (Untyped.B zero)))