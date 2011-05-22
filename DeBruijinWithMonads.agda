{- An formalization of the λ calculus using DeBruijin indices as explained in TAPL, Pierce -}

module DeBruijinWithMonads where

open import Data.Nat
open import Data.Nat.Theorems
open import Relation.Nullary
--open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality

infixr 60 _⇒_
infixl 70 _$_
infixr 65 _>>=_
infix  20 _≡βη_

data Term : Set where
 #   : (n : ℕ) → Term          -- de Bruijin index
 _$_ : (f a : Term) → Term
 ƛ   : (t : Term) → Term

 -- monadic constants
 return : (t : Term) → Term
 _>>=_  : (m f : Term) → Term

 -- casting operations
 ο↑ : (t : Term) → Term                                   -- [up]cast to ο
 ο↓ : (t : Term) → Term                                   -- [down]cast to o
 
{- The shifting operations -}

-- upshift

↑[_∶_] : (n d : ℕ) → (t : Term) → Term
↑[ n ∶ d ] (# n') with d ≤? n'
...               | yes p = # (n + n')           -- n' is not a bound variable - shift is needed
...               | no ¬p = # n'                 -- n' is bound - no shifting!
↑[ n ∶ d ] (ƛ t)      = ƛ (↑[ n ∶ 1 + d ] t)

-- other cases just rebuild the term after the rec. call:
↑[ n ∶ d ] (f $ a)    = ↑[ n ∶ d ] f $ ↑[ n ∶ d ] a
↑[ n ∶ d ] (return t) = return (↑[ n ∶ d ] t)
↑[ n ∶ d ] (m >>= f)  = ↑[ n ∶ d ] m >>= ↑[ n ∶ d ] f
↑[ n ∶ d ] (ο↑ t)     = ο↑ (↑[ n ∶ d ] t)
↑[ n ∶ d ] (ο↓ t)     = ο↓ (↑[ n ∶ d ] t)


↑[_] : (n : ℕ) → (t : Term) → Term
↑[ n ] t = ↑[ n ∶ 0 ] t

-- downshift (used in beta reduction)

↓[_] : (d : ℕ) → (t : Term) → Term
↓[ d ] (# n') with d ≤? n'
...               | yes p = # (pred n')           -- n' is not a bound variable - shift is needed
...               | no ¬p = # n'                 -- n' is bound - no shifting!
↓[ d ] (ƛ t)      = ƛ (↓[ 1 + d ] t)

-- trivial cases
↓[ d ] (f $ a)    = ↓[ d ] f $ ↓[ d ] a
↓[ d ] (return t) = return (↓[ d ] t)
↓[ d ] (m >>= f)  = ↓[ d ] m >>= ↓[ d ] f
↓[ d ] (ο↑ t)     = ο↑ (↓[ d ] t)
↓[ d ] (ο↓ t)     = ο↓ (↓[ d ] t)

↓ : (t : Term) → Term
↓ t = ↓[ 0 ] t


{- substitution -}

_[_↦_] : (t : Term) → (n : ℕ) → (s : Term) → Term
# k   [ n ↦ s ] with k ≟ n
...             | yes p = s
...             | no ¬p = # k
ƛ t   [ n ↦ s ] = ƛ (t [ (1 + n) ↦ (↑[ 1 ] s) ])

-- trivial cases
f $ a     [ n ↦ s ] = (f [ n ↦ s ]) $ (a [ n ↦ s ])
return t  [ n ↦ s ] = return (t [ n ↦ s ])
(m >>= f) [ n ↦ s ] = (m [ n ↦ s ]) >>= (f [ n ↦ s ])
ο↑ t      [ n ↦ s ] = ο↑ (t [ n ↦ s ])
ο↓ t      [ n ↦ s ] = ο↓ (t [ n ↦ s ])

{- beta reduction -}

-- (λ t) v ⇒β downshift (t [ 0 ↦ upshift v])
beta : (t : Term) → (v : Term) → Term
beta t v = ↓ (t [ 0 ↦ ↑[ 1 ] v ])


{- The βη-equality -}

data _≡βη_ : Term → Term → Set where
  -- rules of equivalence relations
  refl : (t     : Term) → t ≡βη t
  symm : {t s   : Term} → t ≡βη s → s ≡βη t
  tran : {t s u : Term} → t ≡βη s → s ≡βη u → t ≡βη u

  -- congruence rules
  app  : {t₁ t₂ s₁ s₂ : Term} → t₁ ≡βη t₂ → s₁ ≡βη s₂ → t₁ $ s₁ ≡βη t₂ $ s₂
  abs  : {t s         : Term} → t  ≡βη s  → ƛ t ≡βη ƛ s
  ret  : {t s         : Term} → t  ≡βη s  → return t ≡βη return s
  bnd  : {t₁ t₂ s₁ s₂ : Term} → t₁ ≡βη t₂ → s₁ ≡βη s₂ → t₁ >>= s₁ ≡βη t₂ >>= s₂

  οup  : {t s         : Term} → t  ≡βη s  → ο↑ t ≡βη ο↑ s
  οdw  : {t s         : Term} → t  ≡βη s  → ο↓ t ≡βη ο↓ s

  -- reduction rules
  β    : (t v : Term) → (ƛ t) $ v ≡βη beta t v
  η    : (t   : Term) →  ƛ (t $ (# 0)) ≡βη t

  -- monadic laws
  r-zero : (t     : Term) → t >>= (ƛ (return (# 0))) ≡βη t
  l-zero : (x t   : Term) → return x >>= t ≡βη t $ x
  assoc  : (m f g : Term) → m >>= (ƛ (f $ (# 0) >>= g)) ≡βη (m >>= f) >>= g


{- Small step operational semantics -}

-- values

data isValue : (t : Term) → Set where
  abs : (t : Term) → isValue (ƛ t)

isValue? : (t : Term) → Dec (isValue t)
isValue? (# n) = no (λ ())
isValue? (f $ a) = no (λ ())
isValue? (ƛ t) = yes (abs t)
isValue? (return t) = no (λ ())
isValue? (m >>= f) = no (λ ())
isValue? (ο↑ t) = no (λ ())
isValue? (ο↓ t) = no (λ ())

-- This part has to be redone

{-
data _⟶β_ : (t t' : Term) → Set where
  β : (t v : Term) → isValue v → (ƛ t) $ v ⟶β beta t v
  
  app-fun : (t v t' : Term) → isValue v → t ⟶β t' → t $ v ⟶β t' $ v 

  app-arg : (t x x' : Term) → x ⟶β x'  →  t $ x ⟶β t $ x' 


{- The notion of normal forms -}
data inNormalForm : Term → Set where
  nf : (t : Term) → (∀ (t' : Term) → ¬ t ⟶β t') → inNormalForm t
-}

{-
  --------------
     TESTS
  --------------
-}

{- Example upshiftings -}

ex-t : Term
ex-t = ƛ (ƛ (# 0  $  # 1  $  # 2  $  # 3))

ex-t' : Term
ex-t' = ↑[ 2 ] ex-t


{- Example substitutions -}

subst-1 : (ƛ (# 0)) [ 0 ↦ (ƛ (ƛ (# 0 $ # 0))) ] ≡ (ƛ (# 0))
subst-1 = refl

subst-2 : (# 0) [ 0 ↦ (ƛ (ƛ (# 0 $ # 0))) ] ≡ ƛ (ƛ (# 0 $ # 0))
subst-2 = refl

subst-3 : (ƛ (# 0 $ # 1)) [ 0 ↦ (ƛ (ƛ (# 0 $ # 0))) ] ≡ ƛ (# 0 $ ƛ (ƛ (# 0 $ # 0)))
subst-3 = refl

subst-4 : (# 0 $ # 0) [ 0 ↦ (ƛ (# 1 $ # 1)) ] ≡ ƛ (# 1 $ # 1) $ ƛ (# 1 $ # 1)
subst-4 = refl

subst-5 : ƛ (# 1 $ # 1) [ 0 ↦ (ƛ (# 1 $ # 1)) ] ≡ ƛ (ƛ (# 2 $ # 2) $ ƛ (# 2 $ # 2))
subst-5 = refl

{- Example β reductions -}

beta-1 : beta (# 0) (ƛ (# 1)) ≡ (ƛ (# 1))
beta-1 = refl

beta-2 : beta (# 1) (ƛ (# 1)) ≡ # 0
beta-2 = refl

beta-3 : beta (ƛ (# 1 $ # 0)) (ƛ (# 1)) ≡ ƛ (ƛ (# 2) $ # 0)
beta-3 = refl

{- The development from Representing Monads -}

data Type : Set where
--  ο   : Type 
  γ   : Type
  T   : (τ : Type) → Type
  _⇒_ : (τ₁ τ₂ : Type) → Type

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
  φ⟨_⟩ : (α : Type) → (tM : Term) → Term
  φ⟨ γ ⟩     t = t
  φ⟨ T α ⟩   t = t >>= (ƛ (return (φ⟨ α ⟩ (# 0)))) -- ≡ fmap φ τ
  φ⟨ α ⇒ τ ⟩ t = ƛ (ƛ (t $ ψ⟨ α ⟩ (# 1)) >>= (ƛ (# 1 $ φ⟨ τ ⟩ (# 0))))

  ψ⟨_⟩ : (α : Type) → (tK : Term) → Term
  ψ⟨ γ ⟩     t = t
  ψ⟨ T α ⟩   t = t >>= (ƛ (return (ψ⟨ α ⟩ (# 0)))) -- ≡ fmap ψ τ
  ψ⟨ α ⇒ τ ⟩ t = ƛ (ƛ (# 0 >>= (ƛ (return (ο↓ (# 0))))))
                      $ (t $ φ⟨ α ⟩ (# 0) $ (ƛ (return (ο↑ (ψ⟨ τ ⟩ (# 0))))))

mutual
  φ-comm-beta : (α : Type) → (t v : Term) → beta (φ⟨ α ⟩ t) v ≡ φ⟨ α ⟩ (beta t v)
  φ-comm-beta a t v = {!!}

  ψ-comm-beta : (α : Type) → (t v : Term) → beta (ψ⟨ α ⟩ t) v ≡ ψ⟨ α ⟩ (beta t v)
  ψ-comm-beta a t v = {!!}

  φ-comm : (α : Type) → (t : Term) → ↓[ 0 ] (φ⟨ α ⟩ t [ 0 ↦ # 1 ]) ≡βη φ⟨ α ⟩ (↓[ 0 ] (t [ 0 ↦ # 1 ]))
  φ-comm = {!!}
  
-- main theorem about bare retractions

lem-retraction : ∀ (α : Type)(t : Term) → ψ⟨ α ⟩ (φ⟨ α ⟩ t) ≡βη t
lem-retraction γ t = refl t
lem-retraction (T τ) t = 
  tran (symm (assoc t (ƛ (return (φ⟨ τ ⟩ (# zero)))) (ƛ (return (ψ⟨ τ ⟩ (# zero)))))) 
  (tran (bnd (refl t) (abs (bnd (β (return (φ⟨ τ ⟩ (# zero))) (# zero)) (refl (ƛ (return (ψ⟨ τ ⟩ (# zero)))))))) 
  (tran (bnd (refl t) (abs (bnd (ret lem) (refl (ƛ (return (ψ⟨ τ ⟩ (# zero)))))))) 
  (tran (bnd (refl t) (abs (tran (l-zero (φ⟨ τ ⟩ (# zero)) (ƛ (return (ψ⟨ τ ⟩ (# zero))))) 
  (tran (β (return (ψ⟨ τ ⟩ (# zero))) (φ⟨ τ ⟩ (# zero))) 
  (ret (tran lem2 (lem-retraction τ (# zero)))))))) 
  (r-zero t)))) where
    lem : ↓[ 0 ] (φ⟨ τ ⟩ (# 0) [ 0 ↦ # 1 ]) ≡βη φ⟨ τ ⟩ (# 0)
    lem = φ-comm τ (# 0)
  
    lem2 : ↓[ 0 ] (ψ⟨ τ ⟩ (# 0) [ 0 ↦ ↑[ 1 ∶ 0 ] (φ⟨ τ ⟩ (# 0)) ]) ≡βη ψ⟨ τ ⟩ (φ⟨ τ ⟩ (# 0))
    lem2 = {!!}

    -- potrzeba lematu dotyczacego tego, ze ψ i φ nie dodaja nowych zmiennych wolnych
    -- zatem komutuja z podstawieniami
lem-retraction (τ₁ ⇒ τ₂) t = {!!}
