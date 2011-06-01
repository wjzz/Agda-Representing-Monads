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

  -- the typing relation

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


  ---------------------------
  -- some examples of typings
  ---------------------------

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


  ------------------------------------------------------
  -- Main results about the Simply Typed Lambda Calculus
  ------------------------------------------------------

  -- reduction preserves validness

  valid-red : ∀ (t t' : Term) → t ⟶β t' → valid t → valid t'
  valid-red .(ƛ t $ s) .(instantiate-iter t s 0) (β {t} {s} y) (app .(ƛ t) .s (abs .t y') v2) = valid-instantiate-iter-suc zero t s y' v2
  valid-red .(t $ s) .(t' $ s) (app-f {t} {t'} {s} y) (app .t .s v1 v2) = app t' s (valid-red t t' y v1) v2
  valid-red .(t $ s) .(t $ s') (app-a {t} {s} {s'} y y') (app .t .s v1 v2) = app t s' v1 (valid-red s s' y' v2)

  {- BASE valid valid-red -}

  -- postulate
  -- P xs xs' → P ys ys' → ok (x :: xs ++ ys) → ok (x :: xs' ++ ys')
  -- P xs xs' → P (x : xs) → P (x : ys')
  
  {- BASE dom dom-ok lem-dom-app-inv-l lem-dom-app-inv-r lem-dom-app-inv lem-dom-not-head lem-ok-app-inv-l lem-ok-app-inv-r -}
  {- BASE perm lem-∉-cons perm-in perm-in-rev lem-∈-app-l lem-∈-app-r perm-in lem-∈-app lem-∈-neq lem-∈-inside -}
  {- BASE perm lem-∈-extend-l lem-∈-extend-r ass-dec dom-inv dom-in dom-perm dom-perm-rev perm-app -}

  -- context permutation lemma

  perm : ∀ (Γ Γ' : Context)(τ : Type)(t : Term) → Permutation Γ Γ' → 
         Γ ⊢ t ∶ τ   →    Γ' ⊢ t ∶ τ
  perm Γ Γ' τ .(F z) perm (ass {z} y y') = ass (dom-ok Γ Γ' perm y) (perm-in (z ∶ τ) Γ Γ' ass-dec perm y')
  perm Γ Γ' τ .(t $ s) permu (app {.Γ} {t} {s} τ₁ .τ v1 v2 o d1 d2) = app τ₁ τ v1 v2 (dom-ok Γ Γ' permu o) 
      (perm Γ Γ' (τ₁ ⇒ τ) t permu d1) (perm Γ Γ' τ₁ s permu d2)
  perm Γ Γ' .(α ⇒ τ) .(ƛ t) permu (abs {.Γ} {t} α τ y y') = abs α τ (dom-ok Γ Γ' permu y) lem where
    lem : (z : Name) → (z ∉ fv t) → (z ∉ dom Γ') → (z ∶ α ∷ Γ') ⊢ instantiate-iter t (F z) 0 ∶ τ
    lem z z∉fv-t z∉Γ' = perm (z ∶ α ∷ Γ) (z ∶ α ∷ Γ') τ (instantiate-iter t (F z) zero) (p-cons (z ∶ α) Γ Γ' permu) 
                             (y' z z∉fv-t (dom-perm-rev Γ Γ' z permu z∉Γ'))  

  {- BASE perm perm lem-∉-cons sym -}


  -- context weakening lemma

  weak : ∀ (Γ : Context)(τ α : Type)(t : Term)(x : Name) →
         Γ ⊢ t ∶ α   →    x ∉ dom Γ → x ∉ fv t → Γ , x ∶ τ ⊢ t ∶ α
  weak Γ τ α .(F z) x (ass {z} y y') x∉dom x∉fv = ass (ok-cons x Γ τ x∉dom y) (in-drop (x ∶ τ) y')
  weak Γ τ α .(t $ s) x (app {.Γ} {t} {s} τ₁ .α v1 v2 o d1 d2) x∉dom x∉fv = 
    app τ₁ α v1 v2 (ok-cons x Γ τ x∉dom o) 
               (weak Γ τ ((τ₁ ⇒ α)) t x d1 x∉dom (λ x' → x∉fv (lem-∈-extend-r x (fv t) (fv s) x'))) 
               (weak Γ τ τ₁ s x d2 x∉dom (λ x' → x∉fv (lem-∈-extend-l x (fv s) (fv t) x')))
  weak Γ τ .(α ⇒ τ') .(ƛ t) x (abs {.Γ} {t} α τ' y y') x∉dom x∉fv = abs α τ' (ok-cons x Γ τ x∉dom y) lem where
    lem : (z : Name) → (z ∉ fv t) → (z ∉ (x ∷ dom Γ)) → (z ∶ α ∷ x ∶ τ ∷ Γ) ⊢ instantiate-iter t (F z) 0 ∶ τ'
    lem z z∉fv z∉dom = perm (x ∶ τ ∷ z ∶ α ∷ Γ) ((z ∶ α ∷ x ∶ τ ∷ Γ)) τ' ((instantiate-iter t (F z) 0)) (p-swap (x ∶ τ) (z ∶ α) Γ) 
                       (weak ((z ∶ α ∷ Γ)) τ τ' ((instantiate-iter t (F z) 0)) x (y' z z∉fv (λ x' → z∉dom (in-drop x x'))) 
                       (lem-∉-neq-tail x z ((dom Γ)) (λ x' → lem-∉-cons z x (dom Γ) z∉dom (sym x')) x∉dom) 
                       (lem-instantiate-fresh t x z x∉fv (λ x' → lem-∉-cons z x (dom Γ) z∉dom (sym x'))))


  -- the progress lemma

  progress : ∀ (t : Term) (τ : Type) → valid t → ∅ ⊢ t ∶ τ → value t ⊎ ∃ (λ t' → t ⟶β t')
  progress = {!!}


  lem-assingment-neq : ∀ (x1 x2 : Name)(τ1 τ2 : Type) → x1 ≢ x2 → x1 ∶ τ1 ≢ x2 ∶ τ2
  lem-assingment-neq .x2 x2 .τ2 τ2 neq refl = neq refl


  -- the substitution lemma

  lem-subst : ∀ (Γ : Context)(x : Name)(α τ : Type)(t t2 : Term) → 
              Γ , x ∶ α ⊢ t ∶ τ   → Γ ⊢ t2 ∶ α   → Γ ⊢ t [ x ↦ t2 ] ∶ τ
  lem-subst = {!!}


  -- beta reduction and typing

  lem-subsitution-iter : ∀ (n : ℕ) (Γ : Context)(t t2 : Term) (τ₁ τ₂ : Type) → valid-iter (ƛ t) n → valid-iter t2 n → value t2 
    → Γ ⊢ ƛ t ∶ τ₁ ⇒ τ₂    → Γ ⊢ t2 ∶ τ₁     →  Γ ⊢ instantiate-iter t t2 n ∶ τ₂
  lem-subsitution-iter = {!!}
  
  lem-subsitution : ∀ (t t2 : Term) (τ₁ τ₂ : Type) → valid (ƛ t) → valid t2 → value t2 → ∅ ⊢ ƛ t ∶ τ₁ ⇒ τ₂ → ∅ ⊢ t2 ∶ τ₁
                    → ∅ ⊢ instantiate t t2 ∶ τ₂
  lem-subsitution = lem-subsitution-iter zero ∅


  -- type preservation under reduction

  lem-type-presservation : ∀ (t t' : Term) (τ : Type) → valid t → ∅ ⊢ t ∶ τ → (t ⟶β t') → ∅ ⊢ t' ∶ τ
  lem-type-presservation = {!!}


  -- the slogan theorem

  lem-well-typed-cant-go-bad : ∀ (t : Term) (τ : Type) → valid t → ∅ ⊢ t ∶ τ → ∃ (λ val → value val × (t ≡ val ⊎ t ⟶β val))
  lem-well-typed-cant-go-bad = {!!}

