module Typing where

open import Data.Empty
open import Data.Fin
open import Data.Fin.Props renaming (_≟_ to _≟Fin_)
open import Data.Vec
open import Data.Nat renaming (_≤_ to _≤ℕ_)
open import Data.Product
open import Data.Sum

open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality

open import FinUtils
open import Terms

-- simple types

infix 7 _⇒_
infix 6 _,_∶_
infix 5 _⊢_∶_
infix 4 _∶_∈'_

data Type : Set where
  γ    : Type
  _⇒_ : (α β : Type) → Type

-- contexts

data Ctx : Set where
  ∅     : Ctx
  _,_∶_ : (Γ : Ctx) → (x : Name) → (σ : Type) → Ctx

-- context concatenation

_,,_ : Ctx → Ctx → Ctx
Γ ,, ∅ = Γ
Γ ,, (Γ' , x ∶ σ) = (Γ ,, Γ') , x ∶ σ

-- context membership

data _∶_∈'_ : Name → Type → Ctx → Set where
  here  : (x : Name)(α : Type)(Γ : Ctx) 
        → x ∶ α ∈' (Γ , x ∶ α)

  there : {x : Name}{α : Type}{Γ : Ctx}
        → (z : Name)(σ : Type) 
        → x ∶ α ∈' Γ 
        → x ∶ α ∈' Γ , z ∶ σ

-- size of the context

len : Ctx → ℕ
len ∅           = 0
len (Γ , x ∶ σ) = suc (len Γ)

-- domain of a context

Dom : (Γ : Ctx) → Vec Name (len Γ)
Dom ∅           = []
Dom (Γ , x ∶ σ) = x ∷ Dom Γ

-- a useful name

_∉_ : {A : Set}{n : ℕ} → A → Vec A n → Set
x ∉ xs = ¬ (x ∈ xs)

-- ok contexts

data ok : Ctx → Set where
  nil  : ok ∅
  cons : {Γ : Ctx} {x : Name} {σ : Type}
       → (rec  : ok Γ)
       → (x-ok : x ∉ Dom Γ)
       → ok (Γ , x ∶ σ)

-- some properties to be used later

postulate
  ok-uniqueness : ∀ {Γ Γ' x x' σ τ} → ok ((Γ , x' ∶ σ) ,, Γ') 
                → x ∶ τ ∈' (Γ , x' ∶ σ) ,, Γ'  →  x ≡ x'  →  τ ≡ σ
  ok-inverse : ∀ {Γ x σ} → ok (Γ , x ∶ σ) → ok Γ

-- typing judgments

data _⊢_∶_ : Ctx → Term 0 → Type → Set where

  ass : (Γ : Ctx) (x : Name) (σ : Type) 
      → ok Γ
      → x ∶ σ ∈' Γ
      → Γ ⊢ fvar x ∶ σ

  app : {Γ : Ctx} {t s : Term 0} {τ : Type} (σ : Type) -- only σ is not implicit
      → (fn : Γ ⊢ t ∶ σ ⇒ τ)
      → (ag : Γ ⊢ s ∶ σ)
      → Γ ⊢ t ∙ s ∶ τ

  abs : {Γ : Ctx} {t : Term 1} {τ : Type} (σ : Type)              
      → (L : set) 
      → ((x : Name) 
           → x ∉ carrier L
           → Γ , x ∶ σ ⊢ substOuter t (fvar x) ∶ τ)       -- here we need to close the outermost binder in t with x
      → Γ ⊢ (ƛ t) ∶ σ ⇒ τ

-- lemmas about ok and derivations -- 

postulate
  app-inv-l : ∀ {Γ τ τ' t s} → Γ ⊢ (t ∙ s) ∶ τ' → Γ ⊢ t ∶ τ ⇒ τ'
  app-inv-r : ∀ {Γ τ τ' t s} → Γ ⊢ (t ∙ s) ∶ τ' → Γ ⊢ s ∶ τ

-- every typing happens in an ok context

typing-ok-ctx : (Γ : Ctx)(t : Term 0)(σ : Type)
              → Γ ⊢ t ∶ σ → ok Γ
typing-ok-ctx Γ .(fvar x) σ (ass .Γ x .σ y y') 
  = y
typing-ok-ctx Γ .(t ∙ s) σ (app {.Γ} {t} {s} σ' fn ag) 
  = typing-ok-ctx Γ s _ ag
typing-ok-ctx Γ .(ƛ t) .(σ ⇒ τ) (abs {.Γ} {t} {τ} σ L y) with fresh L 
typing-ok-ctx Γ .(ƛ t) .(σ ⇒ τ) (abs {.Γ} {t} {τ} σ L y) | x , px 
  = ok-inverse (typing-ok-ctx _ _ _ (y x px))

-- example typings --

typ-ex : (σ : Type) → ∅ ⊢ (ƛ (bvar zero)) ∶ σ ⇒ σ
typ-ex σ = abs σ (0 , []) (λ x' x0 → ass (∅ , x' ∶ σ) x' σ (cons nil x0) (here x' σ ∅))

typ-ex2 : (t : Term 0)(σ : Type) → ∅ ⊢ t ∶ σ → ∅ ⊢ ƛ (bvar zero) ∙ t ∶ σ
typ-ex2 t σ der = app σ (typ-ex σ) der

-- progress

progress : ∀ (t : Term 0)(σ : Type) → ∅ ⊢ t ∶ σ → value t ⊎ (Σ[ t' ∶ Term 0 ]( t ⟶β t'))
progress .(fvar x) σ (ass .∅ x .σ y ())
progress .(ƛ t) .(σ ⇒ τ) (abs {.∅} {t} {τ} σ L y) 
  = inj₁ (abs t)
progress .(t ∙ s) σ (app {.∅} {t} {s} σ' fn ag) with progress t _ fn | progress s _ ag
progress .((ƛ t0) ∙ s) σ (app {.∅} {.(ƛ t0)} {s} σ' fn ag) | inj₁ (abs t0) | inj₁ val2
  = inj₂ (substOuterIter zero zero t0 s , beta t0 val2)
progress .(t ∙ s) σ (app {.∅} {t} {s} σ' fn ag) | inj₁ val | inj₂ (s' , s⟶s')
  = inj₂ (t ∙ s' , arg val s⟶s')
progress .(t ∙ s) σ (app {.∅} {t} {s} σ' fn ag) | inj₂ (t' , t⟶t') | _ 
  = inj₂ (t' ∙ s , fun s t⟶t')

-- substituion lemma

{-

Goal: ∅ ⊢ substOuterIter zero zero t s ∶ σ
————————————————————————————————————————————————————————————
xsag : ∅ ⊢ s ∶ α
y1 : ∅ , x ∶ α ⊢ substOuterIter zero zero t (fvar x) ∶ σ
y0 : x ∈ proj₂ L → ⊥
x  : Name
L  : Σ ℕ (Vec Name)
y  : ok ∅
α  : Type
v  : value s
s  : Term 0
t  : Term 1
σ  : Type
-}

postulate
  ok-shorten : ∀ {Γ Γ' x α} → ok ((Γ , x ∶ α) ,, Γ') → ok (Γ ,, Γ')

{-
substitution-iter : ∀ {n : ℕ}
                      (Γ Γ' : Ctx)
                      (i : Fin  (suc n)) (max : maximal i)
                      (t : Term (suc n))
                      (s : Term 0)
                      (σ α : Type)
                      (L : set) (x : Name) (x-ok : x ∉ (carrier L))
                  → Γ           ,, Γ' ⊢ s ∶ α
                  → (Γ , x ∶ α) ,, Γ' ⊢ substOuterIter i max t (fvar x) ∶ σ
                  → Γ           ,, Γ' ⊢ substOuterIter i max t s ∶ σ
substitution-iter Γ Γ' i max (fvar x) s σ α L x' x-ok der-s der-t 
  = {!!} -- co jest x' == x?

substitution-iter Γ Γ' i max (bvar m) s σ α L x x-ok der-s der-t with m ≟Fin i | der-t
... | yes p | d = {!!} -- rename is identity lemma is needed
substitution-iter Γ Γ' i max (bvar m) s σ α L x x-ok der-s der-t | no ¬p | ()
substitution-iter Γ Γ' i max (s ∙ t) s' σ α L x x-ok der-s (app σ' y fn ag) 
  = app σ' (ok-shorten {Γ} {Γ'} y) 
  (substitution-iter Γ Γ' i max s s' (σ' ⇒ σ) α L x x-ok der-s fn) 
  (substitution-iter Γ Γ' i max t s' _ _ _ _ x-ok der-s ag)
substitution-iter {n} Γ Γ' i max (ƛ t) s .(σ ⇒ τ) α L x x-ok der-s (abs {.((Γ , x ∶ α) ,, Γ')} 
  {.(substOuterIter (suc i) (suc max) t (fvar x))} {τ} σ y L' x' y' y0) 
  = abs σ (ok-shorten y) L' x' y' 
    {!!}
-}
{-
      substOuterIter (proj₁ (getMaximal n)) (proj₂ (getMaximal n)) t'
      (fvar x0)
      ∶ σ' →
      Γ ,, Γ' , x ∶ α ⊢
      substOuterIter (proj₁ (getMaximal n)) (proj₂ (getMaximal n)) t' s'
      ∶ σ'
————————————————————————————————————————————————————————————
y0    : (Γ , x ∶ α) ,, Γ' , x' ∶ σ ⊢
        substOuterIter (proj₁ (getMaximal n)) (proj₂ (getMaximal n))
        (substOuterIter (suc i) (suc max) t (fvar x)) (fvar x')
        ∶ τ
-}

postulate 
  in-shorten : ∀ {A : Set}{n : ℕ}{x y : A}{s : Vec A n} → x ∉ (y ∷ s) → x ∉ s


substitutionIter : ∀ (Γ Γ' : Ctx) 
             → (t : Term 1) (s : Term 0)
             → (σ α : Type)
             → (L : set) 
             → ((x : Name) 
               → (x ∉ carrier L)
               → (Γ , x ∶ α) ,, Γ' ⊢ substOuter t (fvar x) ∶ σ)
             → Γ ,, Γ' ⊢ s ∶ α
             → Γ ,, Γ' ⊢ substOuter t s ∶ σ

substitutionIter Γ Γ' (fvar x) s σ α L der-t der-s = {!!}

substitutionIter Γ Γ' (bvar (suc ())) s σ α L der-t der-s
substitutionIter Γ Γ' (bvar zero) s σ α L der-t der-s with fresh L 
substitutionIter Γ Γ' (bvar zero) s σ α L der-t der-s | xf , fresh-xf with der-t xf fresh-xf
substitutionIter Γ Γ' (bvar zero) s σ α L der-t der-s | xf , fresh-xf | ass .((Γ , xf ∶ α) ,, Γ') .xf .σ y y'
 rewrite lem-rename0 s | ok-uniqueness {Γ} {Γ'} {σ = α} y y' refl = der-s  


substitutionIter Γ Γ' (s ∙ t) s' σ α L der-t der-s with fresh L  
substitutionIter Γ Γ' (s ∙ t) s' σ α L der-t der-s | xf , fresh-xf with der-t xf fresh-xf
substitutionIter Γ Γ' (s ∙ t) s' σ α L der-t der-s | xf , fresh-xf | app σ' fn ag 
  = app σ' (substitutionIter Γ Γ' s s' _ _ L der-s2 der-s) 
           (substitutionIter Γ Γ' t s' _ _ L der-t2 der-s) where
    der-s2 : (x' : Name) →
            (x' ∈ proj₂ L → ⊥) →
            (Γ , x' ∶ α) ,, Γ' ⊢
            substOuterIter zero zero s (fvar x') ∶ σ' ⇒ σ
    der-s2 x x-ok = app-inv-l {τ = σ'} (der-t x x-ok)

    der-t2 : (x' : Name) →
            (x' ∈ proj₂ L → ⊥) →
            (Γ , x' ∶ α) ,, Γ' ⊢
            substOuterIter zero zero t (fvar x') ∶ σ'
    der-t2 x x-ok = app-inv-r {τ = σ'} (der-t x x-ok)

substitutionIter Γ Γ' (ƛ t) s σ α L der-t der-s with fresh L  
substitutionIter Γ Γ' (ƛ t) s σ α L der-t der-s | xf , fresh-xf with der-t xf fresh-xf
substitutionIter Γ Γ' (ƛ t) s .(σ ⇒ τ) α L der-t der-s 
  | xf , fresh-xf | abs {.((Γ , xf ∶ α) ,, Γ')} {.(substOuterIter (suc zero) (suc zero) t (fvar xf))} {τ} σ L' y 
  = {!substOuterIter Γ (Γ !}

{-
substitutionIter Γ Γ' t s σ α L der-t der-s with fresh L 
substitutionIter Γ Γ' t s σ α L der-t der-s | x , fx with der-t x fx
substitutionIter Γ Γ' (fvar x') s σ α L der-t der-s | x , fx | ass .((Γ , x ∶ α) ,, Γ') .x' .σ y y' 
  with fresh (suc (size L), x' ∷ (carrier L))
substitutionIter Γ Γ' (fvar x') s σ α L der-t der-s | x , fx | ass .((Γ , x ∶ α) ,, Γ') .x' .σ y y' 
 | x2 , fx2 with der-t x2 (in-shorten {x = x2} {y = x'} {s = proj₂ L} fx2)
substitutionIter Γ Γ' (fvar x') s σ α L der-t der-s | x , fx | ass .((Γ , x ∶ α) ,, Γ') .x' .σ y y' | x2 , fx2 | dt = {!dt!}

{-
substitutionIter Γ Γ' (fvar x') s σ α L der-t der-s | x , fx | ass .((Γ , x ∶ α) ,, Γ') .x' .σ y y' with x ≟Name x'
substitutionIter Γ Γ' (fvar x') s σ α L der-t der-s | x , fx | ass .((Γ , x ∶ α) ,, Γ') .x' .σ y y' | yes p 
  rewrite p {- | ok-uniqueness {Γ} {Γ'} {σ = α} y y' refl -} = {!!}
substitutionIter Γ Γ' (fvar x') s σ α L der-t der-s | x , fx | ass .((Γ , x ∶ α) ,, Γ') .x' .σ y y' | no ¬p = {!!}
-}
substitutionIter Γ Γ' (bvar zero) s σ α L der-t der-s | x , fx | ass .((Γ , x ∶ α) ,, Γ') .x .σ y y' 
  rewrite lem-rename0 s | ok-uniqueness {Γ} {Γ'} {σ = α} y y' refl = der-s
substitutionIter Γ Γ' (bvar (suc ())) s σ α L der-t der-s | x , fx | rec

substitutionIter Γ Γ' (s ∙ t) s' σ α L der-t der-s | x , fx | rec = {!!}
substitutionIter Γ Γ' (ƛ t) s σ α L der-t der-s | x , fx | rec = {!!}
-}



substitution : ∀ (t : Term 1) (s : Term 0)
             → (σ α : Type)
             → (L : set) 
             → ((x : Name) 
               → (x ∉ carrier L)
               → ∅ , x ∶ α ⊢ substOuter t (fvar x) ∶ σ)
             → ∅ ⊢ s ∶ α
             → ∅ ⊢ substOuter t s ∶ σ
substitution = substitutionIter ∅ ∅ 

-- preservation

preservation : ∀ (t t' : Term 0) (σ : Type) 
             → t ⟶β t' 
             → ∅ ⊢ t  ∶ σ
             → ∅ ⊢ t' ∶ σ
preservation .((ƛ t) ∙ s) .(substOuterIter zero zero t s) σ (beta t {s} v) (app σ' (abs .σ' L y) ag) 
  = substitution t _ _ _ _ y ag
preservation .(t ∙ s) .(t' ∙ s) σ (fun {t} {t'} s ind) (app τ fn ag) 
  = app τ (preservation t _ _ ind fn) ag
preservation .(t ∙ s) .(t ∙ s') σ (arg {s} {s'} {t} v ind) (app τ fn ag) 
  = app τ fn (preservation s _ _ ind ag)

