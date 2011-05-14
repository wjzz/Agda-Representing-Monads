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
  _∷_ : (x : V) → (τ : Type) → Judgement

data Context : Set where
  ∅ : Context
  _▹_ : (Γ : Context) → (j : Judgement) → Context

infixl 40 _▹_
infix  50 _∷_
infixr 60 _↦_
infixr 60 _⇛_
infixl 65 _$_
infixr 65 _>>=_

data _⊢_∷_ : (Γ : Context) → (t : Term) → (τ : Type) → Set where
  ass : {Γ : Context} {t : V} {α : Type} → 
        Γ ▹ t ∷ α ⊢ var t ∷ α

  abs : {Γ : Context} {t : Term} {x : V} {α β : Type} → 
        Γ ▹ x ∷ α ⊢ t ∷ β  →  Γ ⊢ x ↦ t ∷ α ⇛ β

  app : {Γ : Context} {m n : Term} (α : Type) {β : Type} → 
        Γ ⊢ m ∷ α ⇛ β  →  Γ ⊢ n ∷ α  →  Γ ⊢ m $ n ∷ β

  weak : {Γ : Context} {t : Term} {x : V} {α β : Type} → 
        Γ ⊢ t ∷ β  →  Γ ▹ x ∷ α ⊢ t ∷ β

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
  _∷_ : (x : V) → (τ : MType) → MJudgement

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
  ass : {Γ : MContext} {x : V} {α : MType} → 
        Γ ▹ x ∷ α ⊢T var x ∷ α

  abs : {Γ : MContext} {t : MTerm} {x : V} {α β : MType} → 
        Γ ▹ x ∷ α ⊢T t ∷ β  →  Γ ⊢T x ↦ t ∷ α ⇛ β

  app : {Γ : MContext} {m n : MTerm} {α β : MType} → 
        Γ ⊢T m ∷ α ⇛ β  →  Γ ⊢T n ∷ α  →  Γ ⊢T m $ n ∷ β

  weak : {Γ : MContext} {t : MTerm} {x : V} {α β : MType} → 
        Γ ⊢T t ∷ β  →  Γ ▹ x ∷ α ⊢T t ∷ β

  ret  : {Γ : MContext} {t : MTerm} {α : MType} → 
        Γ ⊢T t ∷ α  →  Γ ⊢T return t ∷ T α

  bind : {Γ : MContext} {m f : MTerm} {α β : MType} → 
        Γ ⊢T m ∷ T α  →  Γ ⊢T f ∷ α ⇛ T β  →  Γ ⊢T m >>= f ∷ T β


data MHasType : MTerm → MType → Set where
  typed : {t : MTerm} {τ : MType} → (der : ∅ ⊢T t ∷ τ) → MHasType t τ


{- Translations into monadic style and CPS -}

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
⟦ Γ ▹ x ∷ τ ⟧ΓM = ⟦ Γ ⟧ΓM ▹ x ∷ ⟦ τ ⟧τM 

-- the relation before the types before and after the translation
-- the proof was generated automatically after manually matching first on τ then on the derivation

monad-validness : ∀ Γ t τ   →   Γ ⊢ t ∷ τ   →   ⟦ Γ ⟧ΓM ⊢T ⟦ t ⟧M ∷ T ⟦ τ ⟧τM
monad-validness .(Γ ▹ t ∷ γ) .(var t) γ (ass {Γ} {t}) = ret ass
monad-validness Γ .(m $ n) γ (app {.Γ} {m} {n} α y y') = bind (monad-validness Γ m (α ⇛ γ) y)
                                                           (abs
                                                            (bind (weak (monad-validness Γ n α y'))
                                                             (abs (app (weak ass) ass))))
monad-validness .(Γ ▹ x ∷ α) t γ (weak {Γ} {.t} {x} {α} y) = weak (monad-validness Γ t γ y)
monad-validness Γ .(μ t) γ (refl {.Γ} {t} y) = bind (monad-validness Γ t (T γ) y) (abs ass)
monad-validness .(Γ ▹ t ∷ T τ) .(var t) (T τ) (ass {Γ} {t}) = ret ass
monad-validness Γ .(m $ n) (T τ) (app {.Γ} {m} {n} α y y') = bind (monad-validness Γ m (α ⇛ T τ) y)
                                                               (abs
                                                                (bind (weak (monad-validness Γ n α y'))
                                                                 (abs (app (weak ass) ass))))
monad-validness .(Γ ▹ x ∷ α) t (T τ) (weak {Γ} {.t} {x} {α} y) = weak (monad-validness Γ t (T τ) y)
monad-validness Γ .(μ t) (T τ) (refl {.Γ} {t} y) = bind (monad-validness Γ t (T (T τ)) y) (abs ass)
monad-validness Γ .([ t ]) (T τ) (reif {.Γ} {t} y) = ret (monad-validness Γ t τ y)
monad-validness .(Γ ▹ t ∷ τ₁ ⇛ τ₂) .(var t) (τ₁ ⇛ τ₂) (ass {Γ} {t}) = ret ass
monad-validness Γ .(x ↦ t) (τ₁ ⇛ τ₂) (abs {.Γ} {t} {x} y) = ret (abs (monad-validness (Γ ▹ x ∷ τ₁) t τ₂ y))
monad-validness Γ .(m $ n) (τ₁ ⇛ τ₂) (app {.Γ} {m} {n} α y y') = bind (monad-validness Γ m (α ⇛ τ₁ ⇛ τ₂) y)
                                                                   (abs
                                                                    (bind (weak (monad-validness Γ n α y'))
                                                                     (abs (app (weak ass) ass))))
monad-validness .(Γ ▹ x ∷ α) t (τ₁ ⇛ τ₂) (weak {Γ} {.t} {x} {α} y) = weak (monad-validness Γ t (τ₁ ⇛ τ₂) y)
monad-validness Γ .(μ t) (τ₁ ⇛ τ₂) (refl {.Γ} {t} y) = bind (monad-validness Γ t (T (τ₁ ⇛ τ₂)) y) (abs ass)


{- Example judgments with derivations -}

id : ∅ ⊢ t-id ∷ γ ⇛ γ
id = abs ass

id-x : ∅ ▹ zero ∷ γ ⊢ t-id $ var zero ∷ γ
id-x = app γ (abs ass) ass

{-
ex-id : ∀ {x τ} → Program (x ↦ var x) (τ ⇛ τ)
ex-id = typed (abs ass)

ex-k : ∀ {x y τ₁ τ₂} → Program (x ↦ y ↦ var x) (τ₁ ⇛ τ₂ ⇛ τ₁)
ex-k = typed (abs (abs (weak ass)))
-}