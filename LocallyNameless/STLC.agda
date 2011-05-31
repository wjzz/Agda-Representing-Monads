{- A formalization of some notions from the Simply Typed lambda calculus. -}

module STLC where

open import Data.Empty
open import Data.List
open import Data.List.Utils
open import Data.Nat
open import Data.Nat.Theorems
open import Data.Sum
open import Data.Product renaming (_,_ to _,,_)

open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary


open import Terms
open Syntax
open import Contexts
open TypeTechnicalities


module SimplyTyped where

  data _⊢_∶_ : (Γ : Context) → (t : Term) → (τ : Type) → Set where
    ass : {z : Name}{τ : Type} {Γ : Context} → ok Γ → (z ∶ τ) ∈ Γ → Γ ⊢ F z ∶ τ

    app : {Γ : Context} {t s : Term} (τ₁ τ₂ : Type) →
          (v1 : valid t) → (v2 : valid s) → (o : ok Γ) →
          (d1 : Γ ⊢ t ∶ τ₁ ⇒ τ₂)   →   (d2 : Γ ⊢ s ∶ τ₁)   →    Γ ⊢ t $ s ∶ τ₂

    abs : {Γ : Context}{t : Term} (α τ : Type) → ok Γ
          → ((z : Name) → z ∉ fv t → z ∉ dom Γ → Γ , z ∶ α ⊢ (instantiate t (F z)) ∶ τ)
          → Γ ⊢ ƛ t ∶ α ⇒ τ


  infix  3 _⟶β_
  
  -- small-step reduction relation
  data _⟶β_ : (t t' : Term) → Set where
    β     : {t s : Term} → value s → (ƛ t) $ s ⟶β instantiate t s
    app-f : {t t' s : Term} → t ⟶β t'  → t $ s ⟶β t' $ s
    app-a : {t s s' : Term} → value t → s ⟶β s'  → t $ s ⟶β t $ s'


  -----------------
  -- some examples 
  -----------------

  lem-id : (t : Term) → value t → (ƛ (B 0)) $ t ⟶β t
  lem-id t v = β v

  ω : Term
  ω = ƛ (B 0 $ B 0)

  Ω : Term
  Ω = ω $ ω

  lem-omega : Ω ⟶β Ω
  lem-omega = β (abs (B zero $ B zero))

  id-type : ∀ {τ} → ∅ ⊢ (ƛ (B 0)) ∶ τ ⇒ τ
  id-type {τ} = abs τ τ ok-nil (λ z x x' → ass (ok-cons z [] τ x' ok-nil) (in-keep (z ∶ τ) []))

  s-comb : ∀ {α τ} → ∃ (λ t → ∅ ⊢ t ∶ α ⇒ τ ⇒ α)
  s-comb {α} {τ} = ƛ (ƛ (B 1)) ,, abs α (τ ⇒ α) ok-nil (λ z x x' →
    abs τ α (ok-cons z [] α x' ok-nil) (λ z' x0 x1 →  ass (ok-cons z' (z ∶ α ∷ []) τ x1 (ok-cons z [] α x' ok-nil))
    (in-drop (z' ∶ τ) (in-keep (z ∶ α) []))))




  valid-red : ∀ (t t' : Term) → t ⟶β t' → valid t → valid t'
  valid-red .(ƛ t $ s) .(instantiate-iter t s 0) (β {t} {s} y) (app .(ƛ t) .s (abs .t y') v2) = valid-instantiate-iter-suc zero t s y' v2
  valid-red .(t $ s) .(t' $ s) (app-f {t} {t'} {s} y) (app .t .s v1 v2) = app t' s (valid-red t t' y v1) v2
  valid-red .(t $ s) .(t $ s') (app-a {t} {s} {s'} y y') (app .t .s v1 v2) = app t s' v1 (valid-red s s' y' v2)

  {- BASE valid valid-red -}

  -- postulate
  -- P xs xs' → P ys ys' → ok (x :: xs ++ ys) → ok (x :: xs' ++ ys')
  -- P xs xs' → P (x : xs) → P (x : ys')


  -- permutation lemma
  perm : ∀ (Γ Γ' : Context)(τ : Type)(t : Term) → Permutation Γ Γ' → 
         Γ ⊢ t ∶ τ   →    Γ' ⊢ t ∶ τ
  perm .[] .[] τ t p-nil der = der
  perm .(x ∷ xs ++ ys) .(xs' ++ x ∷ ys') τ .(F z) (p-cons x xs xs' ys ys' y y') (ass {z} y0 y1) 
    = ass (dom-ok (x ∷ xs ++ ys) (xs' ++ x ∷ ys') (p-cons x xs xs' ys ys' y y') y0) 
      (perm-in (z ∶ τ) (x ∷ xs ++ ys) (xs' ++ x ∷ ys') ass-dec (p-cons x xs xs' ys ys' y y') y1)
  perm .(x ∷ xs ++ ys) .(xs' ++ x ∷ ys') τ .(t $ s) (p-cons x xs xs' ys ys' y y') (app {.(x ∷ xs ++ ys)} {t} {s} τ₁ .τ v1 v2 o d1 d2) 
    = {!!}
  perm .(x ∶ τ' ∷ xs ++ ys) .(xs' ++ x ∶ τ' ∷ ys') .(α ⇒ τ) .(ƛ t) (p-cons .(x ∶ τ') xs xs' ys ys' y y') (abs {.(x ∶ τ' ∷ xs ++ ys)} {t} α τ 
    (ok-cons x .(xs ++ ys) τ' y0 y1) y2) = abs α τ (dom-ok (x ∶ τ' ∷ xs' ++ ys') (xs' ++ x ∶ τ' ∷ ys') 
      (p-cons (x ∶ τ') xs' xs' ys' ys' (perm-id xs') (perm-id ys')) {!!}) (λ z z∉t z∉dom → {!!})

  weak : ∀ (Γ : Context)(τ α : Type)(t : Term)(x : Name) →
         Γ ⊢ t ∶ α   →    Γ , x ∶ τ ⊢ t ∶ α
  weak = {!!}

  progress : ∀ (t : Term) (τ : Type) → valid t → ∅ ⊢ t ∶ τ → value t ⊎ ∃ (λ t' → t ⟶β t')
  progress = {!!}

  lem-assingment-neq : ∀ (x1 x2 : Name)(τ1 τ2 : Type) → x1 ≢ x2 → x1 ∶ τ1 ≢ x2 ∶ τ2
  lem-assingment-neq .x2 x2 .τ2 τ2 neq refl = neq refl
  
  lem-subst : ∀ (Γ : Context)(x : Name)(α τ : Type)(t t2 : Term) → 
              Γ , x ∶ α ⊢ t ∶ τ   → Γ ⊢ t2 ∶ α   → Γ ⊢ t [ x ↦ t2 ] ∶ τ
  lem-subst = {!!}

  lem-subsitution-iter : ∀ (n : ℕ) (Γ : Context)(t t2 : Term) (τ₁ τ₂ : Type) → valid-iter (ƛ t) n → valid-iter t2 n → value t2 
    → Γ ⊢ ƛ t ∶ τ₁ ⇒ τ₂    → Γ ⊢ t2 ∶ τ₁     →  Γ ⊢ instantiate-iter t t2 n ∶ τ₂
  lem-subsitution-iter = {!!}
  
  lem-subsitution : ∀ (t t2 : Term) (τ₁ τ₂ : Type) → valid (ƛ t) → valid t2 → value t2 → ∅ ⊢ ƛ t ∶ τ₁ ⇒ τ₂ → ∅ ⊢ t2 ∶ τ₁
                    → ∅ ⊢ instantiate t t2 ∶ τ₂
  lem-subsitution = lem-subsitution-iter zero ∅


  lem-type-presservation : ∀ (t t' : Term) (τ : Type) → valid t → ∅ ⊢ t ∶ τ → (t ⟶β t') → ∅ ⊢ t' ∶ τ
  lem-type-presservation = {!!}

  lem-well-typed-cant-go-bad : ∀ (t : Term) (τ : Type) → valid t → ∅ ⊢ t ∶ τ → ∃ (λ val → value val × (t ≡ val ⊎ t ⟶β val))
  lem-well-typed-cant-go-bad = {!!}

