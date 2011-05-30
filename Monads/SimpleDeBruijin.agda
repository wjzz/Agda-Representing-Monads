{- An formalization of the λ calculus using DeBruijin indices as explained in TAPL, Pierce -}

module SimpleDeBruijin where

open import Data.Nat
open import Data.Nat.Theorems
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

infixl 50 _$_

data Term : Set where
 #   : (n : ℕ) → Term          -- de Bruijin index
 _$_ : (f a : Term) → Term
 ƛ   : (t : Term) → Term


{- The shifting operations -}

-- upshift

↑[_∶_] : (n d : ℕ) → (t : Term) → Term
↑[ n ∶ d ] (# n') with d ≤? n'
...               | yes p = # (n + n')           -- n' is not a bound variable - shift is needed
...               | no ¬p = # n'                 -- n' is bound - no shifting!
↑[ n ∶ d ] (f $ a) = ↑[ n ∶ d ] f $ ↑[ n ∶ d ] a
↑[ n ∶ d ] (ƛ t)   = ƛ (↑[ n ∶ 1 + d ] t)

↑[_] : (n : ℕ) → (t : Term) → Term
↑[ n ] t = ↑[ n ∶ 0 ] t

-- downshift (used in beta reduction)

↓[_] : (d : ℕ) → (t : Term) → Term
↓[ d ] (# n') with d ≤? n'
...               | yes p = # (pred n')           -- n' is not a bound variable - shift is needed
...               | no ¬p = # n'                 -- n' is bound - no shifting!
↓[ d ] (f $ a) = ↓[ d ] f $ ↓[ d ] a
↓[ d ] (ƛ t)   = ƛ (↓[ 1 + d ] t)

↓ : (t : Term) → Term
↓ t = ↓[ 0 ] t


{- substitution -}

_[_↦_] : (t : Term) → (n : ℕ) → (s : Term) → Term
# k   [ n ↦ s ] with k ≟ n
...             | yes p = s
...             | no ¬p = # k
f $ a [ n ↦ s ] = (f [ n ↦ s ]) $ (a [ n ↦ s ])
ƛ t   [ n ↦ s ] = ƛ (t [ (1 + n) ↦ (↑[ 1 ] s) ])


{- beta reduction -}

-- (λ t) v ⇒β downshift (t [ 0 ↦ upshift v])
beta : (t : Term) → (v : Term) → Term
beta t v = ↓ (t [ 0 ↦ ↑[ 1 ] v ])


{- The βη-equality -}

data _≡βη_ : Term → Term → Set where
  refl : (t     : Term) → t ≡βη t
  symm : {t s   : Term} → t ≡βη s → s ≡βη t
  tran : {t s u : Term} → t ≡βη s → s ≡βη u → t ≡βη u

  app  : {t₁ t₂ s₁ s₂ : Term} → t₁ ≡βη t₂ → s₁ ≡βη s₂ → t₁ $ s₁ ≡βη t₂ $ s₂
  abs  : {t s         : Term} → t  ≡βη s  → ƛ t ≡βη ƛ s

  β    : (t v : Term) → (ƛ t) $ v ≡βη beta t v
  η    : (t   : Term) →  ƛ (t $ (# 0)) ≡βη t


{- Small step operational semantics -}

-- values

data isValue : (t : Term) → Set where
  abs : (t : Term) → isValue (ƛ t)

isValue? : (t : Term) → Dec (isValue t)
isValue? (# n) = no (λ ())
isValue? (f $ a) = no (λ ())
isValue? (ƛ t) = yes (abs t)

data _⟶β_ : (t t' : Term) → Set where
  β : (t v : Term) → isValue v → (ƛ t) $ v ⟶β beta t v
  
  app-fun : (t v t' : Term) → isValue v → t ⟶β t' → t $ v ⟶β t' $ v 

  app-arg : (t x x' : Term) → x ⟶β x'  →  t $ x ⟶β t $ x' 


{- The notion of normal forms -}
data inNormalForm : Term → Set where
  nf : (t : Term) → (∀ (t' : Term) → ¬ t ⟶β t') → inNormalForm t


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
