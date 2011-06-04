module Contexts where

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

{- BASE IMPORT Terms -}

module TypeTechnicalities where

  infixl 40 _,_
  infix  50 _∶_
  infixr 60 _⇒_

  -- simple types

  data Type : Set where
    γ : Type
    _⇒_ : (τ1 τ2 : Type) → Type  


  -- variable type declaration/assignment

  data Assignment : Set where
    _∶_ : (x : Name) → (τ : Type) → Assignment


  -- for contexts we will use a sugared notation for lists instead
  -- of a seperate datatype to minimalize the number of needed lemmas

  Context : Set
  Context = List Assignment

  ∅ : Context
  ∅ = []

  -- a single assingment with the rest of the context
  _,_ : (Γ : Context) → (j : Assignment) → Context      
  Γ , j = j ∷ Γ
  

  -- domain of a context

  dom : (Γ : Context) → List Name
  dom [] = []
  dom (x ∶ τ ∷ xs) = x ∷ dom xs

  -- well formed contexts
  -- that is those whose domains form a set

  data ok : Context → Set where
    ok-nil  : ok ∅
    ok-cons : (x : Name) (Γ : Context) (τ : Type) → x ∉ dom Γ → ok Γ → ok (Γ , x ∶ τ)


  -------------------------------------
  --      properties of dom & ok     --
  -------------------------------------
 
  lem-dom-extend-l : ∀ (x : Name) (xs ys : Context) → x ∈ dom xs → x ∈ dom (xs ++ ys)
  lem-dom-extend-l x [] ys ()
  lem-dom-extend-l .x' (x' ∶ τ ∷ xs) ys (in-keep .x' .(dom xs)) = in-keep x' (dom (xs ++ ys))
  lem-dom-extend-l x (x' ∶ τ ∷ xs) ys (in-drop .x' y) = in-drop x' (lem-dom-extend-l x xs ys y)

  lem-dom-extend-r : ∀ (x : Name) (xs ys : Context) → x ∈ dom xs → x ∈ dom (ys ++ xs)
  lem-dom-extend-r x xs [] inn = inn
  lem-dom-extend-r x xs (x' ∶ τ ∷ xs') inn with x == x'
  lem-dom-extend-r x xs (x' ∶ τ ∷ xs') inn | yes p rewrite p = in-keep x' (dom (xs' ++ xs))
  lem-dom-extend-r x xs (x' ∶ τ ∷ xs') inn | no ¬p = in-drop x' (lem-dom-extend-r x xs xs' inn)


  lem-dom-app-inv-l : ∀ (x : Name) (xs ys : Context) → x ∉ dom (xs ++ ys) → x ∉ dom xs
  lem-dom-app-inv-l x xs ys x∉dom-app x∈dom-xs = x∉dom-app (lem-dom-extend-l x xs ys x∈dom-xs)

  lem-dom-app-inv-r : ∀ (x : Name) (xs ys : Context) → x ∉ dom (xs ++ ys) → x ∉ dom ys
  lem-dom-app-inv-r x xs ys x∉dom-app x∈dom-ys = x∉dom-app (lem-dom-extend-r x ys xs x∈dom-ys)

  lem-dom-app-inv : ∀ (x : Name) (xs ys : Context) → x ∈ dom (xs ++ ys) → x ∈ dom xs ⊎ x ∈ dom ys
  lem-dom-app-inv x [] ys in-app' = inj₂ in-app'
  lem-dom-app-inv .x' (x' ∶ τ ∷ xs) ys (in-keep .x' .(dom (xs ++ ys))) = inj₁ (in-keep x' (dom xs))
  lem-dom-app-inv x (x' ∶ τ ∷ xs) ys (in-drop .x' y) with lem-dom-app-inv x xs ys y
  ... | inj₁ l = inj₁ (in-drop x' l)
  ... | inj₂ r' = inj₂ r'

  lem-dom-not-head : ∀ (x x' : Name)(xs : Context) → x ∈ x' ∷ dom xs → x ≢ x' → x ∈ dom xs
  lem-dom-not-head .x' x' xs (in-keep .x' .(dom xs)) neq = ⊥-elim (neq refl)
  lem-dom-not-head x x' xs (in-drop .x' y) neq = y

  {- BASE dom lem-dom-app-inv-l lem-dom-app-inv-r lem-dom-app-inv lem-dom-not-head -}

   
  lem-ok-app-inv-l : ∀ (xs ys : Context) → ok (xs ++ ys) → ok xs
  lem-ok-app-inv-l [] ts okk = ok-nil
  lem-ok-app-inv-l (.(x ∶ τ) ∷ xs) ts (ok-cons x .(xs ++ ts) τ y y') = ok-cons x xs τ (lem-dom-app-inv-l x xs ts y) (lem-ok-app-inv-l xs ts y')

  lem-ok-app-inv-r : ∀ (xs ys : Context) → ok (xs ++ ys) → ok ys
  lem-ok-app-inv-r [] ys okk = okk
  lem-ok-app-inv-r (.(x ∶ τ) ∷ xs) ys (ok-cons x .(xs ++ ys) τ y y') = lem-ok-app-inv-r xs ys y'

  {- BASE dom lem-ok-app-inv-l lem-ok-app-inv-r -}

  lem-ok-app-middle : ∀ (x : Name) (τ : Type) (xs ys : Context) → ok (xs ++ ys) → x ∉ dom (xs ++ ys) → ok (xs ++ (x ∶ τ) ∷ ys)
  lem-ok-app-middle x τ [] ys ok-app x∉dom-app = ok-cons x ys τ x∉dom-app ok-app
  lem-ok-app-middle x τ (x' ∶ τ' ∷ xs) ys ok-app x∉dom-app with x == x'
  lem-ok-app-middle x τ (x' ∶ τ' ∷ xs) ys ok-app x∉dom-app | yes p rewrite (sym p) = ⊥-elim (x∉dom-app (in-keep x (dom (xs ++ ys))))
  lem-ok-app-middle x τ (x' ∶ τ' ∷ xs) ys (ok-cons .x' .(xs ++ ys) .τ' y y') x∉dom-app | no ¬p = ok-cons x' (xs ++ x ∶ τ ∷ ys) τ' 
    lem (lem-ok-app-middle x τ xs ys y' (λ x0 → x∉dom-app (in-drop x' x0))) where
      lem : x' ∈ dom (xs ++ x ∶ τ ∷ ys) → ⊥
      lem x0 with lem-dom-app-inv x' xs (x ∶ τ ∷ ys) x0
      lem x0 | inj₁ x1 = lem-dom-app-inv-l x' xs ys y x1
      lem x0 | inj₂ y0 with lem-dom-not-head x' x ys y0 (λ x1 → ¬p (sym x1))
      ... | cond0 = lem-dom-app-inv-r x' xs ys y cond0

  {- BASE dom lem-ok-app-middle -}
  
  --------------------------------------------------
  -- decidable comparisons on types and assignments
  --------------------------------------------------

  lem-type-dec : (τ1 τ2 τ3 τ4 : Type) → (τ1 ⇒ τ3 ≡ τ2 ⇒ τ4) → τ1 ≡ τ2 × τ3 ≡ τ4
  lem-type-dec .τ2 τ2 .τ4 τ4 refl = refl ,, refl  
  
  {- BASE type lem-type-dec -}

  type-dec : (τ₁ τ₂ : Type) → Dec (τ₁ ≡ τ₂)
  type-dec γ γ = yes refl
  type-dec γ (τ1 ⇒ τ2) = no (λ ())
  type-dec (τ1 ⇒ τ2) γ = no (λ ())
  type-dec (τ1 ⇒ τ2) (τ3 ⇒ τ4) with type-dec τ1 τ3
  type-dec (τ1 ⇒ τ2) (τ3 ⇒ τ4) | yes p with type-dec τ2 τ4
  type-dec (τ1 ⇒ τ2) (τ3 ⇒ τ4) | yes p | yes p2 rewrite p | p2 = yes refl
  type-dec (τ1 ⇒ τ2) (τ3 ⇒ τ4) | yes p | no ¬p rewrite p = no (λ x → ¬p (proj₂ (lem-type-dec τ3 τ3 τ2 τ4 x)))
  type-dec (τ1 ⇒ τ2) (τ3 ⇒ τ4) | no ¬p = no (λ x → ¬p (proj₁ (lem-type-dec τ1 τ3 τ2 τ4 x)))

  lem-ass-dec : (x1 x2 : Name)(τ1 τ2 : Type) → (x1 ∶ τ1 ≡ x2 ∶ τ2) → x1 ≡ x2 × τ1 ≡ τ2
  lem-ass-dec .x2 x2 .τ2 τ2 refl = refl ,, refl  

  {- BASE ass lem-ass-dec -}    

  ass-dec : (a1 a2 : Assignment) → Dec (a1 ≡ a2)
  ass-dec (x ∶ τ) (x' ∶ τ') with x == x'
  ass-dec (x ∶ τ) (x' ∶ τ') | yes p with type-dec τ τ'
  ass-dec (x ∶ τ) (x' ∶ τ') | yes p' | yes p rewrite p' | p = yes refl
  ass-dec (x ∶ τ) (x' ∶ τ') | yes p  | no ¬p = no (λ x0 → ¬p (proj₂ (lem-ass-dec x x' τ τ' x0)))
  ass-dec (x ∶ τ) (x' ∶ τ') | no ¬p = no (λ x0 → ¬p (proj₁ (lem-ass-dec x x' τ τ' x0)))

  {- BASE perm ass-dec -}

  ------------------------------
  -- properties of permutations
  ------------------------------

  dom-inv : ∀ (Γ : Context)(z : Name) → z ∈ dom Γ → ∃ (λ τ → z ∶ τ ∈ Γ)
  dom-inv [] z ()
  dom-inv (x ∶ τ ∷ xs) .x (in-keep .x .(dom xs)) = τ ,, in-keep (x ∶ τ) xs
  dom-inv (x ∶ τ ∷ xs) z (in-drop .x y) = proj₁ (dom-inv xs z y) ,, in-drop (x ∶ τ) (proj₂ (dom-inv xs z y))

  dom-in : ∀ (Γ : Context)(z : Name)(τ : Type) → z ∶ τ ∈ Γ → z ∈ dom Γ
  dom-in [] z τ ()
  dom-in (x ∶ τ ∷ xs) .x .τ (in-keep .(x ∶ τ) .xs) = in-keep x (dom xs)
  dom-in (x ∶ τ ∷ xs) z τ' (in-drop .(x ∶ τ) inn) = in-drop x (dom-in xs z τ' inn)

  {- BASE dom dom-inv dom-in -}

  dom-perm : ∀ (Γ Γ' : Context)(z : Name) → Permutation Γ Γ' → z ∉ dom Γ → z ∉ dom Γ'
  dom-perm Γ Γ' z perm z∉dom z∈dom' with dom-inv Γ' z z∈dom'
  dom-perm Γ Γ' z perm z∉dom z∈dom' | τ ,, inn = z∉dom (dom-in Γ z τ (perm-in-rev (z ∶ τ) Γ Γ' ass-dec perm inn))
     
  dom-perm-rev : ∀ (Γ Γ' : Context)(z : Name) → Permutation Γ Γ' → z ∉ dom Γ' → z ∉ dom Γ
  dom-perm-rev Γ Γ' z perm z∉dom' z∈dom with dom-inv Γ z z∈dom
  dom-perm-rev Γ Γ' z perm z∉dom' z∈dom | τ ,, inn = z∉dom' (dom-in Γ' z τ (perm-in (z ∶ τ) Γ Γ' ass-dec perm inn))

  {- BASE dom dom-perm dom-perm-rev -}
  {- BASE perm dom-perm dom-perm-rev -}


  -- permutations and ok
  dom-ok : ∀ (Γ Γ' : Context) → Permutation Γ Γ' → ok Γ → ok Γ'
  dom-ok .[] Γ' (p-trans .[] l2 .Γ' y y') ok-nil rewrite perm-nil l2 y | perm-nil Γ' y' = ok-nil
  dom-ok .(x ∶ τ ∷ Γ) Γ' (p-trans .(x ∶ τ ∷ Γ) l2 .Γ' y y') (ok-cons x Γ τ y0 y1) = dom-ok l2 Γ' y' l2-ok where
    l2-ok : ok l2
    l2-ok = dom-ok (x ∶ τ ∷ Γ) l2 y (ok-cons x Γ τ y0 y1)
  dom-ok .[] .[] p-nil okΓ = okΓ
  dom-ok .(x ∶ τ ∷ xs) .(x ∶ τ ∷ xs') (p-cons .(x ∶ τ) xs xs' y) (ok-cons x .xs τ y' y0) 
    = ok-cons x xs' τ (dom-perm xs xs' x y y') (dom-ok xs xs' y y0)
  dom-ok .(x ∶ τ ∷ x' ∶ τ' ∷ l) .(x' ∶ τ' ∷ x ∶ τ ∷ l) (p-swap .(x ∶ τ) .(x' ∶ τ') l) (ok-cons x .(x' ∶ τ' ∷ l) τ y' 
        (ok-cons x' .l τ' y y0)) = ok-cons x' (x ∶ τ ∷ l) τ' (lem-∉-neq-tail x' x ((dom l)) (λ x0 → x≢x' (sym x0)) y) 
        (ok-cons x l τ x∉l y0) where
   x≢x' : x ≢ x'
   x≢x' x0 = y' (lem-∈-eq x x' (dom l) x0)
   x∉l : x ∉ dom l
   x∉l = λ x0 → y' (in-drop x' x0)  

  {- BASE dom dom-ok -}
  {- BASE perm dom-ok -}