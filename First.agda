module First where

open import Data.Char

{- Untyped terms -}

data Term : Set where
  var : (v : Char) → Term
  _$_ : (m n : Term) → Term
  _↦_ : (v : Char) → Term → Term

-- example terms

t-id : Term
t-id = 'x' ↦ var 'x'

t-app-id : Term
t-app-id = t-id $ t-id

{- Simply-typed terms -}

data Type : Set where
  γ : Type
  _⇛_ : (τ₁ τ₂ : Type) → Type

data Judgement : Set where
  _∷_ : (t : Term) → (τ : Type) → Judgement

data Context : Set where
  ∅ : Context
  _▹_ : (Γ : Context) → (j : Judgement) → Context

infixl 40 _▹_
infix 50 _∷_
infix 60 _↦_
infix 60 _⇛_

data _⊢_∷_ : (Γ : Context) → (t : Term) → (τ : Type) → Set where
  ass : {Γ : Context} {t : Term} {α : Type} → 
        Γ ▹ t ∷ α ⊢ t ∷ α

  abs : {Γ : Context} {t : Term}{x : Char}{α β : Type} → 
        Γ ▹ (var x) ∷ α ⊢ t ∷ β  →  Γ ⊢ x ↦ t ∷ α ⇛ β

  app : {Γ : Context} {m n : Term}{α β : Type} → 
        Γ ⊢ m ∷ α ⇛ β  →  Γ ⊢ n ∷ α  →  Γ ⊢ m $ n ∷ β

  weak : {Γ : Context} {t t' : Term}{α β : Type} → 
        Γ ⊢ t ∷ β  →  Γ ▹ t' ∷ α ⊢ t ∷ β

{- Example judgments with derivations -}

id : ∅ ⊢ t-id ∷ γ ⇛ γ
id = abs ass

id-x : ∅ ▹ var 'x' ∷ γ ⊢ t-id $ var 'x' ∷ γ
id-x = {!!}


data TT : Type → Set where
  _$_ : {τ₁ τ₂ : Type} → (m : TT (τ₁ ⇛ τ₂)) → (n : TT τ₁) → TT τ₂