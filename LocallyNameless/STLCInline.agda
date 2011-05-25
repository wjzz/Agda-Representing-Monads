{- A formalization of some notions from the Simply Typed lambda calculus. -}

module STLCInline where

open import Data.Empty
open import Data.List
open import Data.List.Utils
open import Data.Nat
open import Data.Nat.Utils
open import Data.Sum
open import Data.Product renaming (_,_ to _,,_)

open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary


--open import UntypedLC

-- the main module is parametrized by the name type, a notion of equality and a comparison that decided the equality


module SimplyTyped (Name : Set) (_≈_ : Name → Name → Set)(_==_ : (n1 n2 : Name) → Dec (n1 ≡ n2)) where

  
  --open Untyped Name _≈_ _==_ 

    -- the type of terms
  infixl 5 _$_

  data Term : Set where
    B   : (i : ℕ)    → Term                   
    F   : (z : Name) → Term
    _$_ : (t1 t2 : Term) → Term
    ƛ   : (t : Term) → Term
  
  
  -- now we want to define the main two functions from the McBride & McKinna paper:
  -- * abstract

  abstraction-iter : (z : Name) → (t : Term) → ℕ → Term
  abstraction-iter z (B i) l = B i
  abstraction-iter z (F x) l with z == x
  abstraction-iter z (F x) l | yes p = B l
  abstraction-iter z (F x) l | no ¬p = F x
  abstraction-iter z (t1 $ t2) l = abstraction-iter z t1 l $ abstraction-iter z t2 l
  abstraction-iter z (ƛ t) l     = ƛ (abstraction-iter z t (suc l))


  -- abstract takes a name and binds it at the top-most level
  -- i.e. abstract x (λ. 0 x) ==> (λ 0 1) 
  --                         ! it does not wrap it with a ƛ!
  abstraction : (z : Name) → (t : Term) → Term
  abstraction z t = abstraction-iter z t 0

  -- and
  -- * instantiate
    
  instantiate-iter : (t : Term) → (s : Term) → ℕ → Term
  instantiate-iter (B i) s l with i ≟ l
  instantiate-iter (B i) s l | yes p = s
  instantiate-iter (B i) s l | no ¬p = B i
  instantiate-iter (F z) s l = F z
  instantiate-iter (t1 $ t2) s l = instantiate-iter t1 s l $ instantiate-iter t2 s l
  instantiate-iter (ƛ t) s l     = ƛ (instantiate-iter t s (suc l))


  -- instantiate takes a term t that came from ƛ t and replaces all occurences of the
  -- bound variable quantified at the top-most level by the given term s
  instantiate : (t s : Term) → Term
  instantiate t s = instantiate-iter t s 0

  
  -- we can also define a special case for the instantiate function
  -- when we open a bound variable for a given name (instead of just any term)
  -- in order for this function to be correct, z should be fresh in t
  -- (this precondition will be stated in the theorems and lemmas
  var-open-iter : (t : Term) → (z : Name) → (n : ℕ)  → Term
  var-open-iter (B i) z n with i ≟ n
  var-open-iter (B i) z n | yes p = F z
  var-open-iter (B i) z n | no ¬p = B i
  var-open-iter (F x) z n = F x
  var-open-iter (t1 $ t2) z n = var-open-iter t1 z n $ var-open-iter t2 z n
  var-open-iter (ƛ t) z n = ƛ (var-open-iter t z (suc n))

  var-open : (t : Term) → (z : Name) → Term
  var-open t z = var-open-iter t z 0


  -- having defined instantiate and abstraction we can now define subst as
  -- subst t x s ≡ t [ x ↦ s ] = instantiate (abstraction x t) s
  --
  -- however we will implement it directly, by essentially fusing the two functions

  _[_↦_] : (t : Term) → (x : Name) → (s : Term) → Term
  B i       [ x ↦ s ] = B i
  F z       [ x ↦ s ] with x == z
  F z       [ x ↦ s ] | yes p = s
  F z       [ x ↦ s ] | no ¬p = F z
  (t1 $ t2) [ x ↦ s ] = t1 [ x ↦ s ] $ t2 [ x ↦ s ]
  ƛ t       [ x ↦ s ] = ƛ (t [ x ↦ s ])

  -- free variables

  fv : (t : Term) → List Name
  fv (B i)     = []
  fv (F z)     = z ∷ []
  fv (t1 $ t2) = fv t1 ++ fv t2
  fv (ƛ t)     = fv t

  -- fresh variables

  _#_ : (n : Name) (t : Term) → Set
  x # t = x ∉ fv t

  
  -- encodings of valid lambda terms
  -- basically, we want to guarantee, that every bound
  -- variable has a coresponding lambda somewhere up in the term

  data valid-iter : (t : Term) (n : ℕ) → Set where
    free  : (n : ℕ) (z :     Name) → valid-iter (F z) n
    app   : {n : ℕ} (t1 t2 : Term) → (v1 : valid-iter t1 n) → (v2 : valid-iter t2 n)  → valid-iter (t1 $ t2) n
    abs   : {n : ℕ} (t :     Term) → valid-iter t (suc n)   → valid-iter (ƛ t) n
    bound : (n k : ℕ) → k < n      → valid-iter (B k) n

  valid : (t : Term) → Set
  valid t = valid-iter t 0

  -- the βη equality

  infix 4 _≡βη_

  data _≡βη_ : (t s : Term) → Set where
  
    -- equivalence relation rules
    refl : {t     : Term} → t ≡βη t
    symm : {t s   : Term} → t ≡βη s → s ≡βη t
    tran : {t s u : Term} → t ≡βη s → s ≡βη u → t ≡βη u

    -- congruence rules
    app : {t1 s1 t2 s2 : Term} → t1 ≡βη s1 → t2 ≡βη s2 → t1 $ t2 ≡βη s1 $ s2
    abs : {t s         : Term} → t  ≡βη s → ƛ t ≡βη ƛ s

    -- computational rules
    η : {t : Term} → ƛ (t $ B 0) ≡βη t
    β : (t s : Term) → (ƛ t) $ s ≡βη instantiate t s



{-
-----------------------------------------------------
   Some theorems about the notions defined so far
-----------------------------------------------------
-}

  -- id t ≡βη t
  -- derived automatically

  lem-apply-id : ∀ (t : Term) → (ƛ (B 0)) $ t ≡βη t
  lem-apply-id t = β (B zero) t

  -- a function that decided equality must be "reflexive"
  ==-refl : ∀ (x : Name) → x == x ≡ yes refl
  ==-refl x with x == x
  ==-refl x | yes refl = refl
  ==-refl x | no ¬p = ⊥-elim (¬p refl)
  

  {- the duality between variable opening and closing in two parts -}

  lem-open-then-close-iter : ∀ (n : ℕ) (t : Term) → (x : Name) → x # t → t ≡ abstraction-iter x (var-open-iter t x n) n
  lem-open-then-close-iter b (B i) x x#t with i ≟ b
  lem-open-then-close-iter b (B i) x x#t | yes p rewrite ==-refl x | p = refl
  lem-open-then-close-iter b (B i) x x#t | no ¬p = refl
  lem-open-then-close-iter b (F z) x x#t with x == z
  lem-open-then-close-iter b (F z) .z x#t | yes refl = ⊥-elim (x#t (in-keep z []))
  lem-open-then-close-iter b (F z) x x#t | no ¬p = refl
  lem-open-then-close-iter b (t1 $ t2) x x#t = cong₂ _$_
                                                 (lem-open-then-close-iter b t1 x
                                                  (lem-∈-app-l x (fv t1) (fv t2) x#t))
                                                 (lem-open-then-close-iter b t2 x
                                                  (lem-∈-app-r x (fv t1) (fv t2) x#t))
  lem-open-then-close-iter b (ƛ t) x x#t = cong ƛ (lem-open-then-close-iter (suc b) t x x#t)

  lem-close-then-open-iter : ∀ (n : ℕ) (t : Term) → (x : Name) → valid-iter t n → t ≡ var-open-iter (abstraction-iter x t n) x n
  lem-close-then-open-iter n (B i) x v with i ≟ n
  lem-close-then-open-iter n (B i) x (bound .n .i y) | yes p = ⊥-elim (lem-less-means-no i n y p)
  lem-close-then-open-iter n (B i) x v | no ¬p = refl
  lem-close-then-open-iter n (F z) x v with x == z
  lem-close-then-open-iter n (F z) x v | yes p rewrite lem-≟-refl n | p = refl
  lem-close-then-open-iter n (F z) x v | no ¬p = refl
  lem-close-then-open-iter n (t1 $ t2) x (app .t1 .t2 v1 v2) = cong₂ _$_ (lem-close-then-open-iter n t1 x v1) (lem-close-then-open-iter n t2 x v2)
  lem-close-then-open-iter n (ƛ t) x (abs .t v) = cong ƛ (lem-close-then-open-iter (suc n) t x v)



  -- having proven the generalizations, we get the main theorems for free
  lem-open-then-close : ∀ (t : Term) → (x : Name) → x # t → t ≡ abstraction x (var-open t x)
  lem-open-then-close = lem-open-then-close-iter 0

  lem-close-then-open : ∀ (t : Term) → (x : Name) → valid t → t ≡ var-open (abstraction x t) x
  lem-close-then-open = lem-close-then-open-iter 0


  -- substitution on a fresh variable doesn't change the term

  lem-subst-fresh : ∀ (t s : Term)(x : Name) → x # t → t [ x ↦ s ] ≡ t
  lem-subst-fresh (B i) s x nin = refl
  lem-subst-fresh (F z) s x nin with x == z
  lem-subst-fresh (F z) s x nin | yes p rewrite p = ⊥-elim (nin (in-keep z []))
  lem-subst-fresh (F z) s x nin | no ¬p = refl
  lem-subst-fresh (t1 $ t2) s x nin = cong₂ _$_ (lem-subst-fresh t1 s x (lem-∈-app-l x (fv t1) (fv t2) nin)) 
                                                (lem-subst-fresh t2 s x (lem-∈-app-r x (fv t1) (fv t2) nin))
  lem-subst-fresh (ƛ t) s x nin = cong ƛ (lem-subst-fresh t s x nin)


  -- abstraction on a fresh variable is an identity

  lem-abstraction-fresh-iter : ∀ (n : ℕ) (t : Term) (x : Name) → x # t → abstraction-iter x t n ≡ t
  lem-abstraction-fresh-iter n (B i) x nin = refl
  lem-abstraction-fresh-iter n (F z) x nin with x == z
  lem-abstraction-fresh-iter n (F z) x nin | yes p rewrite p = ⊥-elim (nin (in-keep z []))
  lem-abstraction-fresh-iter n (F z) x nin | no ¬p = refl
  lem-abstraction-fresh-iter n (t1 $ t2) x nin = cong₂ _$_
      (lem-abstraction-fresh-iter n t1 x (lem-∈-app-l x (fv t1) (fv t2) nin))
      (lem-abstraction-fresh-iter n t2 x (lem-∈-app-r x (fv t1) (fv t2) nin))
  lem-abstraction-fresh-iter n (ƛ t) x nin = cong ƛ (lem-abstraction-fresh-iter (suc n) t x nin)
 

  lem-abstraction-fresh : ∀ (t : Term) (x : Name) → x # t → abstraction x t ≡ t
  lem-abstraction-fresh t x nin = lem-abstraction-fresh-iter 0 t x nin


  -- If we guarantee that t is valid, then subst can be expressed using instantiate and abstraction
  
  -- We need a stronger result first, essentialy it's only used in the ƛ case

  lem-subst-alternate-iter : ∀ (n : ℕ) (t s : Term) (x : Name) → (v : valid-iter t n) → 
                t [ x ↦ s ] ≡ instantiate-iter (abstraction-iter x t n) s n
  lem-subst-alternate-iter n (B i) s x (bound .n .i y) with i ≟ n
  ... | yes p = ⊥-elim (lem-less-means-no i n y p)
  ... | no ¬p = refl
  lem-subst-alternate-iter n (F z) s x v with x == z
  lem-subst-alternate-iter n (F z) s x v | yes p rewrite lem-≟-refl n = refl
  lem-subst-alternate-iter n (F z) s x v | no ¬p = refl
  lem-subst-alternate-iter n (t1 $ t2) s x (app .t1 .t2 v v') = cong₂ _$_ (lem-subst-alternate-iter n t1 s x v) (lem-subst-alternate-iter n t2 s x v')
  lem-subst-alternate-iter n (ƛ t) s x (abs .t v) = cong ƛ (lem-subst-alternate-iter (suc n) t s x v)


  lem-subst-alternate : ∀ (t s : Term) (x : Name) → (v : valid t) → t [ x ↦ s ] ≡ instantiate (abstraction x t) s
  lem-subst-alternate t s x v = lem-subst-alternate-iter zero t s x v



  {-  hints for auto
  -t 10 -c ⊥-elim cong ƛ cong₂ _$_ lem-∈-app-l lem-∈-app-r 
  -}

  -- end of copy pasting


  
  -- simple types

  data Type : Set where
    γ : Type
    _⇒_ : (τ1 τ2 : Type) → Type

  
  -- for contexts we will use a sugared notation for lists instead
  -- of a seperate datatype to minimalize the number of needed lemmas

  infix  3 _⟶β_
  infixl 40 _,_
  infix  50 _∶_
  infixr 60 _⇒_
   
  data Assingment : Set where
    _∶_ : (x : Name) → (τ : Type) → Assingment               -- variable type declaration/assignment

  Context : Set
  Context = List Assingment

  ∅ : Context
  ∅ = []

  _,_ : (Γ : Context) → (j : Assingment) → Context      -- a single assingment with the rest of the context
  Γ , j = j ∷ Γ
  

  -- for starters, we do not force the context to be a set wrt to the names

  data _⊢_∶_ : (Γ : Context) → (t : Term) → (τ : Type) → Set where
    ass : {z : Name}{τ : Type} {Γ : Context} → (z ∶ τ) ∈ Γ → Γ ⊢ F z ∶ τ

    app : {Γ : Context} {t s : Term} (τ₁ τ₂ : Type) →
          (d1 : Γ ⊢ t ∶ τ₁ ⇒ τ₂)   →   (d2 : Γ ⊢ s ∶ τ₁)   →    Γ ⊢ t $ s ∶ τ₂

    abs : {Γ : Context}{z : Name}{t : Term} (α τ : Type) →
          (d : Γ , z ∶ α ⊢ t ∶ τ)   →    Γ ⊢ ƛ (abstraction z t) ∶ α ⇒ τ

    -- other possibility
    -- this one is actually used in the document
    -- the approaches seem to be equivalent
  {-
    abs2 : {Γ : Context}{z : Name}{t : Term} (α τ : Type) →
           Γ , z ∶ α ⊢ instantiate (F z) t ∶ τ   →    Γ ⊢ ƛ t ∶ α ⇒ τ
  -}

  
  data value : (t : Term) → Set where
    abs : (t : Term) → value (ƛ t)

  value? : (t : Term) → Dec (value t)
  value? (B i)       = no (λ ())
  value? (F z)       = no (λ ())
  value? (_$_ t1 t2) = no (λ ())
  value? (ƛ t)       = yes (abs t)

  
  -- small-step reduction relation
  data _⟶β_ : (t t' : Term) → Set where
    β     : {t s : Term} → value s → (ƛ t) $ s ⟶β instantiate t s
    app-f : {t t' s : Term} → t ⟶β t'  → t $ s ⟶β t' $ s
    app-a : {t s s' : Term} → value t → s ⟶β s'  → t $ s ⟶β t $ s'


  {- some examples -}
  lem-id : (t : Term) → value t → (ƛ (B 0)) $ t ⟶β t
  lem-id t v = β v

  ω : Term
  ω = ƛ (B 0 $ B 0)

  Ω : Term
  Ω = ω $ ω

  lem-omega : Ω ⟶β Ω
  lem-omega = β (abs (B zero $ B zero))

  

  -- the progress theorem
  lem-progress : ∀ (t : Term) (τ : Type) → valid t → ∅ ⊢ t ∶ τ → value t ⊎ ∃ (λ t' → t ⟶β t')
  lem-progress (B i) τ (bound .0 .i ()) der
  lem-progress (F z) τ v (ass ())
  lem-progress (t1 $ t2) τ (app .t1 .t2 v1 v2) (app τ₁ .τ d1 d2) with lem-progress t1 (τ₁ ⇒ τ) v1 d1
  lem-progress (.(ƛ t) $ t2) τ (app .t1 .t2 v1 v2) (app τ₁ .τ d1 d2) | inj₁ (abs t) with lem-progress t2 τ₁ v2 d2
  ... | inj₁ t2-val  = inj₂ (instantiate-iter t t2 zero ,, β t2-val)
  ... | inj₂ t2-prog = inj₂ (ƛ t $ proj₁ t2-prog ,, app-a (abs t) (proj₂ t2-prog))
  lem-progress (t1 $ t2) τ (app .t1 .t2 v1 v2) (app τ₁ .τ d1 d2) | inj₂ t1-prog = inj₂ (proj₁ t1-prog $ t2 ,, app-f (proj₂ t1-prog))
  lem-progress (ƛ t) τ v der = inj₁ (abs t)

  -- substitution lemma
  
  lem-subsitution-iter : ∀ (n : ℕ) (t t2 : Term) (τ₁ τ₂ : Type) → valid-iter (ƛ t) n → valid-iter t2 n → value t2 → ∅ ⊢ ƛ t ∶ τ₁ ⇒ τ₂ → ∅ ⊢ t2 ∶ τ₁ → 
    ∅ ⊢ instantiate-iter t t2 n ∶ τ₂
  lem-subsitution-iter n (B i) t2 τ₁ τ₂ (abs .(B i) (bound .(suc n) .i (s≤s m≤n))) v2 val2 d1 d2 with i ≟ n
  ... | yes p = {!!}
  ... | no ¬p = {!!}
  lem-subsitution-iter n (F z) t2 τ₁ τ₂ v1 v2 val2 d1 d2 = {!!}
  lem-subsitution-iter n (t1 $ t2) t3 τ₁ τ₂ v1 v2 val2 d1 d2 = {!!}
  lem-subsitution-iter n (ƛ t) t2 τ₁ τ₂ v1 v2 val2 d1 d2 = {!!}

  lem-subsitution : ∀ (t t2 : Term) (τ₁ τ₂ : Type) → valid (ƛ t) → valid t2 → value t2 → ∅ ⊢ ƛ t ∶ τ₁ ⇒ τ₂ → ∅ ⊢ t2 ∶ τ₁
                    → ∅ ⊢ instantiate t t2 ∶ τ₂
  lem-subsitution = lem-subsitution-iter zero

  -- type preservation theorem
  lem-type-presservation : ∀ (t t' : Term) (τ : Type) → valid t → ∅ ⊢ t ∶ τ → (t ⟶β t') → ∅ ⊢ t' ∶ τ
  lem-type-presservation (B i) t' τ (bound .0 .i ()) der red
  lem-type-presservation (F z) t' τ v (ass ()) red

  lem-type-presservation (.(ƛ t) $ t2) .(instantiate-iter t t2 0) τ (app .(ƛ t) .t2 v1 v2) (app τ₁ .τ d1 d2) (β {t} y) 
     = lem-subsitution t t2 τ₁ τ v1 v2 y d1 d2 
  
  lem-type-presservation (t1 $ t2) .(t' $ t2) τ (app .t1 .t2 v1 v2) (app τ₁ .τ d1 d2) (app-f {.t1} {t'} y) = 
    app τ₁ τ (lem-type-presservation t1 t' (τ₁ ⇒ τ) v1 d1 y) d2
  lem-type-presservation (t1 $ t2) .(t1 $ s') τ (app .t1 .t2 v1 v2) (app τ₁ .τ d1 d2) (app-a {.t1} {.t2} {s'} y y') =
    app τ₁ τ d1 (lem-type-presservation t2 s' τ₁ v2 d2 y')

  lem-type-presservation (ƛ .(abstraction-iter z t 0)) t' .(α ⇒ τ) v (abs {.[]} {z} {t} α τ d) ()


  -- the slogan theorem
  lem-well-typed-cant-go-bad : ∀ (t : Term) (τ : Type) → valid t → ∅ ⊢ t ∶ τ → ∃ (λ val → value val × (t ≡ val ⊎ t ⟶β val))
  lem-well-typed-cant-go-bad (B i) τ (bound .0 .i ()) der
  lem-well-typed-cant-go-bad (F z) τ v (ass ())
  lem-well-typed-cant-go-bad (t1 $ t2) τ (app .t1 .t2 v1 v2) (app τ₁ .τ d1 d2) with lem-well-typed-cant-go-bad t1 ((τ₁ ⇒ τ)) v1 d1
  ... | val ,, vval ,, inj₁ t1=val = {!!}
  ... | val ,, vval ,, inj₂ t1>val = {!!}
  lem-well-typed-cant-go-bad (ƛ t) τ v der = ƛ t ,, abs t ,, inj₁ refl

-- it seems that I should change the computation rules so that the simple case is in the bottom

