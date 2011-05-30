module WithMonads where

{- 
  We add monadic reflection to the language and try to formalize some notions
  from Andrzej Filinski's "Representing Monads"
-}

open import Data.Nat
open import Data.Product

-- set of variables
V : Set
V = ℕ

{- Untyped terms with monadic reflection and reification -}

{- The object language -}

data Term : Set where
  var : (v : V) → Term                               -- variable
  _$_ : (m n : Term) → Term                          -- function application
  _↦_ : (v : V) → (e : Term) → Term                  -- lambda abstraction
  [_] : (t : Term) → Term                            -- monadic reification
  μ   : (t : Term) → Term                            -- monadic reflexion

-- example terms

t-id : Term
t-id = zero ↦ var zero

t-app-id : Term
t-app-id = t-id $ t-id



data Type : Set where
  γ   : Type                                           -- atomic (ground) type
  T   : (τ : Type) → Type                              -- monadic constructor
  _⇒_ : (τ₁ τ₂ : Type) → Type                          -- arrow type

data Assingment : Set where
  _∷_ : (x : V) → (τ : Type) → Assingment               -- variable type declaration/assignment

data Context : Set where
  ∅ : Context                                          -- empty context
  _▹_ : (Γ : Context) → (j : Assingment) → Context      -- a single assingment with the rest of the context

infixl 40 _▹_
infix  50 _∷_
infixr 60 _↦_
infixr 60 _⇒_
infixl 65 _$_
infixr 65 _>>=_

data _⊢_∷_ : (Γ : Context) → (t : Term) → (τ : Type) → Set where
  ass : {Γ : Context} {t : V} {α : Type} → 
        Γ ▹ t ∷ α ⊢ var t ∷ α

  abs : {Γ : Context} {t : Term} {x : V} {α β : Type} → 
        Γ ▹ x ∷ α ⊢ t ∷ β  →  Γ ⊢ x ↦ t ∷ α ⇒ β

  app : {Γ : Context} {m n : Term} (α : Type) {β : Type} → 
        Γ ⊢ m ∷ α ⇒ β  →  Γ ⊢ n ∷ α  →  Γ ⊢ m $ n ∷ β

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
  _⇒_ : (τ₁ τ₂ : MType) → MType

data MTerm : Set where
  var : (v : V) → MTerm
  _$_ : (m n : MTerm) → MTerm
  _↦_ : (v : V) → (e : MTerm) → MTerm
 
  -- monadic constants
  return : (t : MTerm) → MTerm
  _>>=_  : (m f : MTerm) → MTerm

  -- casts to and from ο
  ο↑ : (t : MTerm) → MTerm                                   -- [up]cast to ο
  ο↓ : (t : MTerm) → MTerm                                   -- [down]cast to o

data MAssingment : Set where
  _∷_ : (x : V) → (τ : MType) → MAssingment

data MContext : Set where
  ∅ : MContext
  _▹_ : (Γ : MContext) → (j : MAssingment) → MContext


data _⊢T_∷_ : (Γ : MContext) → (t : MTerm) → (τ : MType) → Set where
  ass : {Γ : MContext} {x : V} {α : MType} → 
        Γ ▹ x ∷ α ⊢T var x ∷ α

  abs : {Γ : MContext} {t : MTerm} {x : V} {α β : MType} → 
        Γ ▹ x ∷ α ⊢T t ∷ β  →  Γ ⊢T x ↦ t ∷ α ⇒ β

  app : {Γ : MContext} {m n : MTerm} {α : MType} {β : MType} → 
        Γ ⊢T m ∷ α ⇒ β  →  Γ ⊢T n ∷ α  →  Γ ⊢T m $ n ∷ β

  weak : {Γ : MContext} {t : MTerm} {x : V} {α β : MType} → 
        Γ ⊢T t ∷ β  →  Γ ▹ x ∷ α ⊢T t ∷ β

  ret  : {Γ : MContext} {t : MTerm} {α : MType} → 
        Γ ⊢T t ∷ α  →  Γ ⊢T return t ∷ T α

  bind : {Γ : MContext} {m f : MTerm} {α β : MType} → 
        Γ ⊢T m ∷ T α  →  Γ ⊢T f ∷ α ⇒ T β  →  Γ ⊢T m >>= f ∷ T β

  ⟶ο  : {Γ : MContext} {t : MTerm} {α : MType} → 
        Γ ⊢T t ∷ α  →  Γ ⊢T ο↑ t ∷ ο 

  ο⟶  : {Γ : MContext} {t : MTerm} {α : MType} → 
        Γ ⊢T t ∷ ο  →  Γ ⊢T ο↓ t ∷ α 

data MHasType : MTerm → MType → Set where
  typed : {t : MTerm} {τ : MType} → (der : ∅ ⊢T t ∷ τ) → MHasType t τ


{- Translation into monadic style -}
 
-- we bind some variables with nice names to be able to use
-- good names in lambda abstractions
f = 0 ; x = 1 ; k = 2 ; m = 3 ; y = 4 ; a = 5 ; b = 6


-- we start by ignoring types

⟦_⟧M : Term → MTerm
⟦ var v ⟧M = return (var v)
⟦ v ↦ e ⟧M = return (v ↦ ⟦ e ⟧M )
⟦ m $ n ⟧M = ⟦ m ⟧M >>= (f ↦ ⟦ n ⟧M >>= (x ↦ var f $ var x))
⟦ [ t ] ⟧M = return ⟦ t ⟧M 
⟦ μ t   ⟧M = ⟦ t ⟧M >>= (x ↦ var x)

{- Now we do it with types -}

-- type translation

⟦_⟧τM : Type → MType
⟦ γ ⟧τM       = γ
⟦ T τ ⟧τM     = T ⟦ τ ⟧τM
⟦ τ₁ ⇒ τ₂ ⟧τM = ⟦ τ₁ ⟧τM ⇒ T ⟦ τ₂ ⟧τM

-- mapping type translation in the context

⟦_⟧ΓM : Context → MContext
⟦ ∅ ⟧ΓM = ∅
⟦ Γ ▹ x ∷ τ ⟧ΓM = ⟦ Γ ⟧ΓM ▹ x ∷ ⟦ τ ⟧τM 

-- the relation before the types before and after the translation
-- the proof was generated automatically after manually matching first on t then on the derivation

monad-validness : ∀ Γ t τ   →   Γ ⊢ t ∷ τ   →   ⟦ Γ ⟧ΓM ⊢T ⟦ t ⟧M ∷ T ⟦ τ ⟧τM
monad-validness .(Γ ▹ v ∷ τ) (var v) τ (ass {Γ}) = ret ass
monad-validness .(Γ ▹ x ∷ α) (var v) τ (weak {Γ} {.(var v)} {x} {α} y) = weak (monad-validness Γ (var v) τ y)
monad-validness Γ (m $ n) τ (app α y y') = bind (monad-validness Γ m (α ⇒ τ) y)
                                             (abs
                                              (bind (weak (monad-validness Γ n α y'))
                                               (abs (app (weak ass) ass))))
monad-validness .(Γ ▹ x ∷ α) (m $ n) τ (weak {Γ} {.(m $ n)} {x} {α} y) = weak (monad-validness Γ (m $ n) τ y)
monad-validness Γ (v ↦ e) .(α ⇒ β) (abs {.Γ} {.e} {.v} {α} {β} y) = ret (abs (monad-validness (Γ ▹ v ∷ α) e β y))
monad-validness .(Γ ▹ x ∷ α) (v ↦ e) τ (weak {Γ} {.(v ↦ e)} {x} {α} y) = weak (monad-validness Γ (v ↦ e) τ y)
monad-validness .(Γ ▹ x ∷ α) [ t ] τ (weak {Γ} {.([ t ])} {x} {α} y) = weak (monad-validness Γ [ t ] τ y)
monad-validness Γ [ t ] .(T α) (reif {.Γ} {.t} {α} y) = ret (monad-validness Γ t α y)
monad-validness .(Γ ▹ x ∷ α) (μ t) τ (weak {Γ} {.(μ t)} {x} {α} y) = weak (monad-validness Γ (μ t) τ y)
monad-validness Γ (μ t) τ (refl y) = bind (monad-validness Γ t (T τ) y) (abs ass)


{- Translation to CPS -}

{- Paper notation:

⟦ v ⟧     = λk. k v
⟦ λv. e ⟧ = λk. k (λv. ⟦ e ⟧)
⟦ m n ⟧   = λk. ⟦ m ⟧ (λf. ⟦ n ⟧ (λa. f a k))
⟦ μ t ⟧   = λk. ⟦ t ⟧ (λx. x >>= k)
⟦ [t] ⟧   = λk. k (⟦ t ⟧ ∘ return)  -- with omitted ο↑ and ο↓ 

-}

-- bare terms

⟦_⟧K : Term → MTerm
⟦ var v ⟧K = k ↦ var k $ var v
⟦ v ↦ e ⟧K = k ↦ var k $ (v ↦ ⟦ e ⟧K) 
⟦ m $ n ⟧K = k ↦ ⟦ m ⟧K $ (f ↦ ⟦ n ⟧K $ (x ↦ var f $ var x $ var k))
⟦ μ t   ⟧K = k ↦ ⟦ t ⟧K $ (x ↦ var x >>= var k) 
⟦ [ t ] ⟧K = k ↦ var k $ ((m ↦ var m >>= (x ↦ return (ο↓ (var x))))  -- fmap o↓ 
                       $ (⟦ t ⟧K $ (x ↦ return (ο↑ (var x)))))

--⟦ [ t ] ⟧K = k ↦ var k $ (⟦ t ⟧K $ (x ↦ return (var x)))

-- should be like this, but return is a term constructor, not a term
-- ⟦ [ t ] ⟧K = k ↦ var k $ (⟦ t ⟧K $ return)

-- with explicit coersions
-- ⟦ [ t ] ⟧K = k ↦ var k $ [fmap ο↓] (⟦ t ⟧K $ return ∘ ο↑)


-- type translation

-- This is actually the constructor of the continuation monad transformer
K : MType → MType
K τ = (τ ⇒ T ο) ⇒ T ο

⟦_⟧τK : Type → MType
⟦ γ ⟧τK = γ
⟦ T τ ⟧τK = T ⟦ τ ⟧τK
⟦ τ₁ ⇒ τ₂ ⟧τK = ⟦ τ₁ ⟧τK ⇒ K ⟦ τ₂ ⟧τK


-- context translation

⟦_⟧ΓK : Context → MContext
⟦ ∅ ⟧ΓK = ∅
⟦ Γ ▹ x ∷ τ ⟧ΓK = ⟦ Γ ⟧ΓK ▹ x ∷ ⟦ τ ⟧τK 

-- the relation before the types before and after the translation
-- the proof was generated automatically after manually matching first on τ then on the derivation

cps-validness : ∀ Γ t τ   →   Γ ⊢ t ∷ τ   →   ⟦ Γ ⟧ΓK ⊢T ⟦ t ⟧K ∷ K ⟦ τ ⟧τK
cps-validness .(Γ ▹ v ∷ τ) (var v) τ (ass {Γ}) = abs (app ass (weak ass))
cps-validness .(Γ ▹ x ∷ α) (var v) τ (weak {Γ} {.(var v)} {x} {α} y) = weak (cps-validness Γ (var v) τ y)
cps-validness Γ (m $ n) τ (app α y y') 
  = abs (app (weak (cps-validness Γ m (α ⇒ τ) y))
    (abs (app (weak (weak (cps-validness Γ n α y'))) 
     (abs (app (app (weak ass) ass) (weak (weak ass)))))))
cps-validness .(Γ ▹ x ∷ α) (m $ n) τ (weak {Γ} {.(m $ n)} {x} {α} y) = weak (cps-validness Γ (m $ n) τ y)
cps-validness Γ (v ↦ e) .(α ⇒ β) (abs {.Γ} {.e} {.v} {α} {β} y) = abs (app ass (weak (abs (cps-validness (Γ ▹ v ∷ α) e β y))))
cps-validness .(Γ ▹ x ∷ α) (v ↦ e) τ (weak {Γ} {.(v ↦ e)} {x} {α} y) = weak (cps-validness Γ (v ↦ e) τ y)
cps-validness .(Γ ▹ x ∷ α) [ t ] τ (weak {Γ} {.([ t ])} {x} {α} y) = weak (cps-validness Γ [ t ] τ y)
cps-validness Γ [ t ] .(T α) (reif {.Γ} {.t} {α} y) 
 = abs (app ass (app (abs (bind ass (abs (ret (ο⟶ ass))))) (app (weak (cps-validness Γ t α y)) (abs (ret (⟶ο ass))))))
cps-validness .(Γ ▹ x ∷ α) (μ t) τ (weak {Γ} {.(μ t)} {x} {α} y) = weak (cps-validness Γ (μ t) τ y)
cps-validness Γ (μ t) τ (refl y) = abs (app (weak (cps-validness Γ t (T τ) y)) (abs (bind ass (weak ass))))



{-
  Having defined the translations to both monadic and continuation-passing style,
  the next step is to define and prove the relationship between the two styles.
-}

{- 
  The φ and ψ retractions

  φ[ α ] : ⟦ α ⟧τM → ⟦ α ⟧τK
  ψ[ α ] : ⟦ α ⟧τK → ⟦ α ⟧τM

  φ[γ]       = id
  φ[T α]     = fmap φ[α]
  φ[α ⇒ β] t = λx. λk. t (ψ[α] x) >>= (k ∘ φ[β])

  ψ[γ] = id
  ψ[T α] = fmap ψ α
  ψ[α ⇒ β] t = λa. t (φ[α] a) (return ∘ ψ[β])

  We want <φ, ψ> to form a retraction pair, so we need to show
     ψ ∘ φ ≡βη id

  Proof.
  ⑴ If τ ≡ γ the thm is trivial.

  ⑵ Suppose t : ⟦T α⟧M ≡ T ⟦α⟧M. Then

    (ψ[T α] ∘ φ[T α]) t     ≡   -- omiting types for brevity
    (ψ ∘ φ) t               ≡   -- ∘ def.
     ψ (φ t)                ≡   -- T α case of ψ
    fmap ψ[α] (φ t)         ≡   -- T α case of φ
    fmap ψ[α] (fmap φ[α] t) ≡   -- fmap comp law
    fmap (ψ[α] ∘ φ[α]) t    ≡   -- induction hyp.
    fmap id t               ≡   -- fmap id law
    t

   By extentionality rule we get the thm.

  ⑶ suppose t : ⟦α ⇒ β⟧M ≡ ⟦α⟧M ⇒ T ⟦β⟧M. Then

  φ[α ⇒ β] t = λx. λk. t (ψ[α] x) >>= (k ∘ φ[β])
  ψ[α ⇒ β] t = λa. t (φ[α] a) (return ∘ ψ[β])

  (ψ[T α] ∘ φ[T α]) t                                                  ≡ omiting types for brevity
  (ψ ∘ φ) t                                                            ≡ ∘ def.
   ψ (φ t)                                                             ≡ α ⇒ β case of φ
   ψ (λx. λk. t (ψ[α] x) >>= (k ∘ φ[β]))                               ≡ α ⇒ β case of ψ
   λa. [λx. λk. t (ψ[α] x) >>= (k ∘ φ[β])] (φ[α] a) (return ∘ ψ[β])    ≡ subst. for x and k
   λa. t (ψ[α] (φ[α] a)) >>= (return ∘ ψ[β] ∘ φ[β])                    ≡ ind. hyp. x 2
   λa. t a >>= return                                                  ≡ right return monad law
   λa. t a                                                             ≡ η rule
   t ∎
-}

{- 
  Weak specification 
-}

-- implementation

mutual
  φ⟨_⟩ : (α : Type) → (tM : MTerm) → MTerm
  φ⟨ γ ⟩     t = t
  φ⟨ T α ⟩   t = t >>= (x ↦ return (φ⟨ α ⟩ (var x))) -- ≡ fmap φ τ
  φ⟨ α ⇒ β ⟩ t = x ↦ k ↦ (t $ ψ⟨ α ⟩ (var x)) >>= (y ↦ var k $ φ⟨ β ⟩ (var y))

  ψ⟨_⟩ : (α : Type) → (tK : MTerm) → MTerm
  ψ⟨ γ ⟩     t = t
  ψ⟨ T α ⟩   t = t >>= (x ↦ return (ψ⟨ α ⟩ (var x))) -- ≡ fmap ψ τ
  ψ⟨ α ⇒ β ⟩ t = a ↦ (m ↦ var m >>= (x ↦ return (ο↓ (var x)))) 
                      $ (t $ φ⟨ α ⟩ (var a) $ (b ↦ return (ο↑ (ψ⟨ β ⟩ (var b)))))


-- Type-wise correctness of the implementation

mutual
  φ-cor : (Γ : MContext) (α : Type) (tM : MTerm) →   Γ ⊢T tM ∷ ⟦ α ⟧τM   →  Γ ⊢T (φ⟨ α ⟩ tM) ∷ ⟦ α ⟧τK
  φ-cor Γ γ tMm der = der
  φ-cor Γ (T τ) tMm der = bind der
                            (abs (ret (φ-cor (Γ ▹ x ∷ ⟦ τ ⟧τM) τ (var x) ass)))
  φ-cor Γ (α ⇒ β) tMm der = abs (abs (bind (app (weak (weak der)) (weak (ψ-cor (Γ ▹ x ∷ ⟦ α ⟧τK) α (var x) ass))) 
                           (abs (app (weak ass) (φ-cor (Γ ▹ x ∷ ⟦ α ⟧τK ▹ k ∷ ⟦ β ⟧τK ⇒ T ο ▹ y ∷ ⟦ β ⟧τM) 
                                                       β (var y) ass)))))

  ψ-cor : (Γ : MContext) (α : Type) (tK : MTerm) →   Γ ⊢T tK ∷ ⟦ α ⟧τK   →  Γ ⊢T (ψ⟨ α ⟩ tK) ∷ ⟦ α ⟧τM
  ψ-cor Γ γ tK der = der
  ψ-cor Γ (T τ) tK der = bind der
                           (abs (ret (ψ-cor (Γ ▹ x ∷ ⟦ τ ⟧τK) τ (var x) ass)))
  ψ-cor Γ (α ⇒ β) tK der = abs (app (abs (bind ass (abs (ret (ο⟶ ass))))) 
                          (app (app (weak der) (φ-cor (Γ ▹ a ∷ ⟦ α ⟧τM) α (var a) ass)) 
                          (abs (ret (⟶ο (ψ-cor (Γ ▹ a ∷ ⟦ α ⟧τM ▹ b ∷ ⟦ β ⟧τK) β (var b) ass))))))

{- 
  Strong specification 
  
  We don't have to construct it from scratch, it sufficess to packages the φ function and φ-cor proof
  together.
-}


φ[_] : (α : Type) (Γ : MContext) (tM : MTerm) →   Γ ⊢T tM ∷ ⟦ α ⟧τM   →  Σ[ tK ∶ MTerm ]  Γ ⊢T tK ∷ ⟦ α ⟧τK
φ[ α ] Γ tM der = φ⟨ α ⟩ tM , φ-cor Γ α tM der

ψ[_] : (α : Type) (Γ : MContext) (tK : MTerm) →   Γ ⊢T tK ∷ ⟦ α ⟧τK   →  Σ[ tM ∶ MTerm ]  Γ ⊢T tM ∷ ⟦ α ⟧τM
ψ[ α ] Γ tM der = ψ⟨ α ⟩ tM , ψ-cor Γ α tM der


{- The relationship between the two translations. -}

{-
 with 
   x₁ : α₁ ▹ x₂ : α₂ ▹ ... ⊢ E : β
 we have 
   ⟦ E ⟧M ≡ ⟦ E ⟧K {φ[α]} (return ∘ ψ[β])

   ⟦ E ⟧M >>= k  ≡   ⟦ E ⟧K {φ[α]} (k ∘ ψ[β])

 where the E { σ } notation means a substitution of the free variables
 in E by σ.

-}


{- Shift & reset come into play -}

{- Recall the definitions:

  ⟦ S E ⟧K = λk. ⟦ E ⟧K (λf. f (λv. λk'. k' (k v)) (λx. x))
  ⟦ # E ⟧K = λk. k (⟦ E ⟧K (λx. x))

-}

{- We suppose that we can express return and >>= in the target language 
   as pure functions.

   We can then derive that:

   ⟦ returnK ⟧K = λk. k (λa. λk'. k' (return a))
   
   ⟦ >>= f ⟧K = λk. k (λa. λk'. k' (a >>= Φ)) where
       ⟦ f ⟧K = λk. k (λa. λk'. k' (Φ a))

   
   The interesting thing:

   ⟦ # (return E)    ⟧K   ≡βη   ⟦ [ E ] ⟧K
   ⟦ S (λk. E >>= k) ⟧K   ≡βη   ⟦  μ E  ⟧K

-}
