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


data MType : Set where
  ο   : MType 
  γ   : MType
  T   : (τ : MType) → MType
  _⇛_ : (τ₁ τ₂ : MType) → MType

data MTerm : Set where
  var : (v : V) → MTerm
  _$_ : (m n : MTerm) → MTerm
  _↦_ : (v : V) → (e : MTerm) → MTerm
 
  -- monadic constants
  return : (t : MTerm) → MTerm
  _>>=_  : (m f : MTerm) → MTerm

  -- casts to and from ο
  ο↑ : (τ : MType) → (t : MTerm) → MTerm
  ο↓ : (t : MTerm) → MTerm

data MJudgement : Set where
  _∷_ : (x : V) → (τ : MType) → MJudgement

data MContext : Set where
  ∅ : MContext
  _▹_ : (Γ : MContext) → (j : MJudgement) → MContext


data _⊢T_∷_ : (Γ : MContext) → (t : MTerm) → (τ : MType) → Set where
  ass : {Γ : MContext} {x : V} {α : MType} → 
        Γ ▹ x ∷ α ⊢T var x ∷ α

  abs : {Γ : MContext} {t : MTerm} {x : V} {α β : MType} → 
        Γ ▹ x ∷ α ⊢T t ∷ β  →  Γ ⊢T x ↦ t ∷ α ⇛ β

  app : {Γ : MContext} {m n : MTerm} (α : MType) {β : MType} → 
        Γ ⊢T m ∷ α ⇛ β  →  Γ ⊢T n ∷ α  →  Γ ⊢T m $ n ∷ β

  weak : {Γ : MContext} {t : MTerm} {x : V} {α β : MType} → 
        Γ ⊢T t ∷ β  →  Γ ▹ x ∷ α ⊢T t ∷ β

  ret  : {Γ : MContext} {t : MTerm} {α : MType} → 
        Γ ⊢T t ∷ α  →  Γ ⊢T return t ∷ T α

  bind : {Γ : MContext} {m f : MTerm} {α β : MType} → 
        Γ ⊢T m ∷ T α  →  Γ ⊢T f ∷ α ⇛ T β  →  Γ ⊢T m >>= f ∷ T β

  ⟶ο  : {Γ : MContext} {t : MTerm} {α : MType} → 
        Γ ⊢T t ∷ α  →  Γ ⊢T ο↑ α t ∷ ο 

  ⟵ο  : {Γ : MContext} {t : MTerm} {α : MType} → 
        Γ ⊢T ο↑ α t ∷ ο  →  Γ ⊢T ο↓ (ο↑ α t) ∷ α 

data MHasType : MTerm → MType → Set where
  typed : {t : MTerm} {τ : MType} → (der : ∅ ⊢T t ∷ τ) → MHasType t τ


{- Translation into monadic style -}

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
-- the proof was generated automatically after manually matching first on t then on the derivation

monad-validness : ∀ Γ t τ   →   Γ ⊢ t ∷ τ   →   ⟦ Γ ⟧ΓM ⊢T ⟦ t ⟧M ∷ T ⟦ τ ⟧τM
monad-validness .(Γ ▹ v ∷ τ) (var v) τ (ass {Γ}) = ret ass
monad-validness .(Γ ▹ x ∷ α) (var v) τ (weak {Γ} {.(var v)} {x} {α} y) = weak (monad-validness Γ (var v) τ y)
monad-validness Γ (m $ n) τ (app α y y') = bind (monad-validness Γ m (α ⇛ τ) y)
                                             (abs
                                              (bind (weak (monad-validness Γ n α y'))
                                               (abs (app ⟦ α ⟧τM (weak ass) ass))))
monad-validness .(Γ ▹ x ∷ α) (m $ n) τ (weak {Γ} {.(m $ n)} {x} {α} y) = weak (monad-validness Γ (m $ n) τ y)
monad-validness Γ (v ↦ e) .(α ⇛ β) (abs {.Γ} {.e} {.v} {α} {β} y) = ret (abs (monad-validness (Γ ▹ v ∷ α) e β y))
monad-validness .(Γ ▹ x ∷ α) (v ↦ e) τ (weak {Γ} {.(v ↦ e)} {x} {α} y) = weak (monad-validness Γ (v ↦ e) τ y)
monad-validness .(Γ ▹ x ∷ α) [ t ] τ (weak {Γ} {.([ t ])} {x} {α} y) = weak (monad-validness Γ [ t ] τ y)
monad-validness Γ [ t ] .(T α) (reif {.Γ} {.t} {α} y) = ret (monad-validness Γ t α y)
monad-validness .(Γ ▹ x ∷ α) (μ t) τ (weak {Γ} {.(μ t)} {x} {α} y) = weak (monad-validness Γ (μ t) τ y)
monad-validness Γ (μ t) τ (refl y) = bind (monad-validness Γ t (T τ) y) (abs ass)

{- Translation to CPS -}

k : V
k = 2

-- bare terms

⟦_⟧K : Term → MTerm
⟦ var v ⟧K = k ↦ var k $ var v
⟦ v ↦ e ⟧K = k ↦ var k $ (v ↦ ⟦ e ⟧K) 
⟦ m $ n ⟧K = k ↦ ⟦ m ⟧K $ (f ↦ ⟦ n ⟧K $ (x ↦ var f $ var x $ var k))
⟦ μ t   ⟧K = k ↦ ⟦ t ⟧K $ (x ↦ var x >>= var k) 
⟦ [ t ] ⟧K = k ↦ var k $ (⟦ t ⟧K $ (x ↦ return (var x)))

-- should be like this, but return is a constructor, not a term
-- ⟦ [ t ] ⟧K = k ↦ var k $ (⟦ t ⟧K $ return)

-- type translation

K : MType → MType
K τ = (τ ⇛ T ο) ⇛ T ο

⟦_⟧τK : Type → MType
⟦ γ ⟧τK = γ
⟦ T τ ⟧τK = T ⟦ τ ⟧τK
⟦ τ₁ ⇛ τ₂ ⟧τK = ⟦ τ₁ ⟧τK ⇛ K ⟦ τ₂ ⟧τK

-- context translation

⟦_⟧ΓK : Context → MContext
⟦ ∅ ⟧ΓK = ∅
⟦ Γ ▹ x ∷ τ ⟧ΓK = ⟦ Γ ⟧ΓK ▹ x ∷ ⟦ τ ⟧τK 

-- the relation before the types before and after the translation
-- the proof was generated automatically after manually matching first on τ then on the derivation

cps-validness : ∀ Γ t τ   →   Γ ⊢ t ∷ τ   →   ⟦ Γ ⟧ΓK ⊢T ⟦ t ⟧K ∷ K ⟦ τ ⟧τK
cps-validness .(Γ ▹ v ∷ τ) (var v) τ (ass {Γ}) = abs (app ⟦ τ ⟧τK ass (weak ass))
cps-validness .(Γ ▹ x ∷ α) (var v) τ (weak {Γ} {.(var v)} {x} {α} y) = weak (cps-validness Γ (var v) τ y)
cps-validness Γ (m $ n) β (app α m-der n-der) 
  = abs (app ((⟦ α ⟧τK ⇛ (⟦ β ⟧τK ⇛ T ο) ⇛ T ο) ⇛ T ο) (weak (cps-validness Γ m (α ⇛ β) m-der)) 
  (abs (app (⟦ α ⟧τK ⇛ T ο) (weak (weak (cps-validness Γ n α n-der))) 
  (abs (app (⟦ β ⟧τK ⇛ T ο) (app ⟦ α ⟧τK (weak ass) ass)
          (weak (weak ass)))))))

cps-validness .(Γ ▹ x ∷ α) (m $ n) τ (weak {Γ} {.(m $ n)} {x} {α} y) = weak (cps-validness Γ (m $ n) τ y)
cps-validness Γ (v ↦ e) .(α ⇛ β) (abs {.Γ} {.e} {.v} {α} {β} y) 
  = abs (app (⟦ α ⟧τK ⇛ (⟦ β ⟧τK ⇛ T ο) ⇛ T ο) ass (weak (abs (cps-validness (Γ ▹ v ∷ α) e β y))))
cps-validness .(Γ ▹ x ∷ α) (v ↦ e) τ (weak {Γ} {.(v ↦ e)} {x} {α} y) = weak (cps-validness Γ (v ↦ e) τ y)
cps-validness .(Γ ▹ x ∷ α) [ t ] τ (weak {Γ} {.([ t ])} {x} {α} y) = weak (cps-validness Γ [ t ] τ y)
cps-validness Γ [ t ] .(T α) (reif {.Γ} {.t} {α} y) = {!!}
cps-validness .(Γ ▹ x ∷ α) (μ t) τ (weak {Γ} {.(μ t)} {x} {α} y) = weak (cps-validness Γ (μ t) τ y)
cps-validness Γ (μ t) τ (refl y) = abs (app (T ⟦ τ ⟧τK ⇛ T ο) (weak (cps-validness Γ t (T τ) y)) (abs (bind ass (weak ass)))) 
