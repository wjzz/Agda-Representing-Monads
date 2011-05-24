{- A formalization of some notions from the untyped lambda calculus.

  The main goal is to check how will the locally nameless approach (de Bruijn indices for
  bound variables and names for free variables) work in practice for me.
  
  If it proves to be useful then this work will get extended to formalize the Simply Typed Lambda Calcules.
-}

module UntypedLC where

open import Data.Empty
open import Data.List
open import Data.List.Utils
open import Data.Nat
open import Data.Nat.Utils

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary


-- the main module is parametrized by the name type, a notion of equality and a comparison that decided the equality

module Untyped (Name : Set) (_≈_ : Name → Name → Set)(_==_ : (n1 n2 : Name) → Dec (n1 ≡ n2)) where
  
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
    app   : {n : ℕ} (t1 t2 : Term) → valid-iter t1 n      → valid-iter t2 n    → valid-iter (t1 $ t2) n
    abs   : {n : ℕ} (t :     Term) → valid-iter t (suc n) → valid-iter (ƛ t) n
    bound : (n k : ℕ) → k < n      → valid-iter (B k) n

  valid : (t : Term) → Set
  valid t = valid-iter t 0

{-
-----------------------------------------------------
   Some theorems about the notions defined so far
-----------------------------------------------------
-}

  -- id t ≡βη t
  -- derived automatically

  lem-apply-id : ∀ (t : Term) → (ƛ (B 0)) $ t ≡βη t
  lem-apply-id t = β (B zero) t


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
