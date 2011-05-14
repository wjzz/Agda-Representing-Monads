module WithMonads where

{- 
  We add monadic reflection to the language and try to formalize some notions
  from Andrzej Filinski's "Representing Monads"
-}

open import Data.Nat


-- set of variables
V : Set
V = ℕ

{- Untyped terms with monadic reflection and reification -}

{- The object language -}

data Term : Set where
  var : (v : V) → Term
  _$_ : (m n : Term) → Term
  _↦_ : (v : V) → (e : Term) → Term
  [_] : (t : Term) → Term
  μ   : (t : Term) → Term

-- example terms

t-id : Term
t-id = zero ↦ var zero

t-app-id : Term
t-app-id = t-id $ t-id



data Type : Set where
  γ   : Type
  T   : (τ : Type) → Type
  _⇛_ : (τ₁ τ₂ : Type) → Type

data Judgement : Set where
  _∷_ : (t : Term) → (τ : Type) → Judgement

data Context : Set where
  ∅ : Context
  _▹_ : (Γ : Context) → (j : Judgement) → Context

infixl 40 _▹_
infix  50 _∷_
infixr 60 _↦_
infixr 60 _⇛_
infixl 65 _$_

data _⊢_∷_ : (Γ : Context) → (t : Term) → (τ : Type) → Set where
  ass : {Γ : Context} {t : Term} {α : Type} → 
        Γ ▹ t ∷ α ⊢ t ∷ α

  abs : {Γ : Context} {t : Term}{x : V}{α β : Type} → 
        Γ ▹ (var x) ∷ α ⊢ t ∷ β  →  Γ ⊢ x ↦ t ∷ α ⇛ β

  app : {Γ : Context} {m n : Term}{α β : Type} → 
        Γ ⊢ m ∷ α ⇛ β  →  Γ ⊢ n ∷ α  →  Γ ⊢ m $ n ∷ β

  weak : {Γ : Context} {t t' : Term}{α β : Type} → 
        Γ ⊢ t ∷ β  →  Γ ▹ t' ∷ α ⊢ t ∷ β

  refl : {Γ : Context} {t : Term} {α : Type} → 
        Γ ⊢ t ∷ T α  →  Γ ⊢ μ t ∷ α

  reif : {Γ : Context} {t : Term} {α : Type} → 
        Γ ⊢ t ∷ α  →  Γ ⊢ [ t ] ∷ T α

data HasType : Term → Type → Set where
  typed : {t : Term} {τ : Type} → (der : ∅ ⊢ t ∷ τ) → HasType t τ


{- When (if?) we define βη equality we should include the monadic reflection laws:
  [ μ v ] ≡βη v and 
  μ [ T ] ≡βη T
-}


data MTerm : Set where
  var : (v : V) → MTerm
  _$_ : (m n : MTerm) → MTerm
  _↦_ : (v : V) → (e : MTerm) → MTerm
 
  -- monadic constants
  return : (t : MTerm) → MTerm
  _>>=_  : (m f : MTerm) → MTerm


data MType : Set where
  γ   : MType
  T   : (τ : MType) → MType
  _⇛_ : (τ₁ τ₂ : MType) → MType

data MJudgement : Set where
  _∷_ : (t : MTerm) → (τ : MType) → MJudgement

data MContext : Set where
  ∅ : MContext
  _▹_ : (Γ : MContext) → (j : MJudgement) → MContext

{-
infixl 40 _▹_
infix  50 _∷_
infixr 60 _↦_
infixr 60 _⇛_
infixl 65 _$_
-}

data _⊢T_∷_ : (Γ : MContext) → (t : MTerm) → (τ : MType) → Set where
  ass : {Γ : MContext} {t : MTerm} {α : MType} → 
        Γ ▹ t ∷ α ⊢T t ∷ α

  abs : {Γ : MContext} {t : MTerm} {x : V} {α β : MType} → 
        Γ ▹ (var x) ∷ α ⊢T t ∷ β  →  Γ ⊢T x ↦ t ∷ α ⇛ β

  app : {Γ : MContext} {m n : MTerm} {α β : MType} → 
        Γ ⊢T m ∷ α ⇛ β  →  Γ ⊢T n ∷ α  →  Γ ⊢T m $ n ∷ β

  weak : {Γ : MContext} {t t' : MTerm} {α β : MType} → 
        Γ ⊢T t ∷ β  →  Γ ▹ t' ∷ α ⊢T t ∷ β

  ret  : {Γ : MContext} {t : MTerm} {α : MType} → 
        Γ ⊢T t ∷ α  →  Γ ⊢T return t ∷ T α

  bind : {Γ : MContext} {m f : MTerm} {α β : MType} → 
        Γ ⊢T m ∷ T α  →  Γ ⊢T f ∷ α ⇛ T β  →  Γ ⊢T m >>= f ∷ T β


data MHasType : MTerm → MType → Set where
  typed : {t : MTerm} {τ : MType} → (der : ∅ ⊢T t ∷ τ) → MHasType t τ


{- Translations into monadic style and CPS -}

-- do we need functions like 
-- Context → MContext ?

f : V
f = 0

x : V
x = 1

-- we start by ignoring types

⟦_⟧M : Term → MTerm
⟦ (var v) ⟧M = return (var v)
⟦ (v ↦ e) ⟧M = return (v ↦ ⟦ e ⟧M )
⟦ (m $ n) ⟧M = ⟦ m ⟧M >>= (f ↦ ⟦ n ⟧M >>= (x ↦ var f $ var x))
⟦ [ t ]   ⟧M = return ⟦ t ⟧M 
⟦ (μ t)   ⟧M = ⟦ t ⟧M >>= (x ↦ var x)

{- Now we do it with types -}

-- type translation

⟦_⟧τM : Type → MType
⟦ γ ⟧τM       = γ
⟦ T τ ⟧τM     = T ⟦ τ ⟧τM
⟦ τ₁ ⇛ τ₂ ⟧τM = ⟦ τ₁ ⟧τM ⇛ T ⟦ τ₂ ⟧τM

-- mapping type translation in the context

⟦_⟧ΓM : Context → MContext
⟦ ∅ ⟧ΓM = ∅
⟦ Γ ▹ t ∷ τ ⟧ΓM = {!⟦ Γ ⟧ΓM ▹ t ∷ ⟦ τ ⟧τM !}

{- Example judgments with derivations -}

id : ∅ ⊢ t-id ∷ γ ⇛ γ
id = abs ass

id-x : ∅ ▹ var zero ∷ γ ⊢ t-id $ var zero ∷ γ
id-x = app (abs ass) ass

{-
ex-id : ∀ {x τ} → Program (x ↦ var x) (τ ⇛ τ)
ex-id = typed (abs ass)

ex-k : ∀ {x y τ₁ τ₂} → Program (x ↦ y ↦ var x) (τ₁ ⇛ τ₂ ⇛ τ₁)
ex-k = typed (abs (abs (weak ass)))
-}