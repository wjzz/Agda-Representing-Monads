module Second where

{- the only difference with First is the use of naturals instead of chars.
   this way automation works again (it complained about literals in types)
-}

open import Data.Nat

{- Untyped terms-}

data Term : Set where
  var : (v : ℕ) → Term
  _$_ : (m n : Term) → Term
  _↦_ : (v : ℕ) → Term → Term

-- example terms

t-id : Term
t-id = zero ↦ var zero

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
infixr 60 _↦_
infixr 60 _⇛_
infixl 65 _$_

data _⊢_∷_ : (Γ : Context) → (t : Term) → (τ : Type) → Set where
  ass : {Γ : Context} {t : Term} {α : Type} → 
        Γ ▹ t ∷ α ⊢ t ∷ α

  abs : {Γ : Context} {t : Term}{x : ℕ}{α β : Type} → 
        Γ ▹ (var x) ∷ α ⊢ t ∷ β  →  Γ ⊢ x ↦ t ∷ α ⇛ β

  app : {Γ : Context} {m n : Term}{α β : Type} → 
        Γ ⊢ m ∷ α ⇛ β  →  Γ ⊢ n ∷ α  →  Γ ⊢ m $ n ∷ β

  weak : {Γ : Context} {t t' : Term}{α β : Type} → 
        Γ ⊢ t ∷ β  →  Γ ▹ t' ∷ α ⊢ t ∷ β

{- Example judgments with derivations -}

id : ∅ ⊢ t-id ∷ γ ⇛ γ
id = abs ass

id-x : ∅ ▹ var zero ∷ γ ⊢ t-id $ var zero ∷ γ
id-x = app (abs ass) ass

data Program : Term → Type → Set where
  typed : {t : Term} {τ : Type} → (der : ∅ ⊢ t ∷ τ) → Program t τ

ex-id : ∀ {x τ} → Program (x ↦ var x) (τ ⇛ τ)
ex-id = typed (abs ass)

ex-k : ∀ {x y τ₁ τ₂} → Program (x ↦ y ↦ var x) (τ₁ ⇛ τ₂ ⇛ τ₁)
ex-k = typed (abs (abs (weak ass)))