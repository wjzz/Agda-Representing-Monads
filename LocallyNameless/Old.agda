module Old where

{-  perm .[] .[] τ .(F z) p-nil (ass {z} _ ())
  perm .(x ∷ xs ++ ys) .(xs' ++ x ∷ ys') τ .(F z) (p-cons x xs xs' ys ys' y y') (ass {z} y0) with lem-∈-app (z ∶ τ) (x ∷ xs) ys ass-dec y0
  perm .(x ∷ xs ++ ys) .(xs' ++ x ∷ ys') τ .(F z) (p-cons x xs xs' ys ys' y y') (ass {z} y0) | inj₁ l with ass-dec (z ∶ τ) x
  perm .(x ∷ xs ++ ys) .(xs' ++ x ∷ ys') τ .(F z) (p-cons x xs xs' ys ys' y y') (ass {z} y0) | inj₁ l | yes p rewrite (sym p) 
    = ass (lem-∈-inside (z ∶ τ) xs' ys')
  perm .(x ∷ xs ++ ys) .(xs' ++ x ∷ ys') τ .(F z) (p-cons x xs xs' ys ys' y y') (ass {z} y0) | inj₁ l | no ¬p 
    = ass (lem-∈-extend-r (z ∶ τ) xs' (x ∷ ys') (perm-in (z ∶ τ) xs xs' ass-dec y (lem-∈-neq (z ∶ τ) x xs ¬p l)))
  perm .(x ∷ xs ++ ys) .(xs' ++ x ∷ ys') τ .(F z) (p-cons x xs xs' ys ys' y y') (ass {z} y0) | inj₂ r 
    = ass (lem-∈-extend-l ((z ∶ τ)) (x ∷ ys') xs' (in-drop x (perm-in (z ∶ τ) ys ys' ass-dec y' r)))
  perm Γ Γ' τ .(t $ s) permu (app {.Γ} {t} {s} τ₁ .τ v1 v2 d1 d2) = app τ₁ τ v1 v2 (perm Γ Γ' (τ₁ ⇒ τ) t permu d1) (perm Γ Γ' τ₁ s permu d2)
  perm Γ Γ' .(α ⇒ τ) .(ƛ t) permu (abs {.Γ} {t} α τ f) = abs α τ (λ z z∉t z∉Γ' → perm (Γ , z ∶ α  ) (z ∶ α ∷ Γ') τ 
     (instantiate-iter t (F z) zero) (p-cons (z ∶ α) [] [] Γ Γ' p-nil permu) (f z z∉t (dom-perm-rev Γ Γ' z permu z∉Γ')))
-}
  {- BASE perm perm perm-id -}

{-
  -- weakening lemma
  weak : ∀ (Γ : Context)(τ α : Type)(t : Term)(x : Name) →
         Γ ⊢ t ∶ α   →    Γ , x ∶ τ ⊢ t ∶ α
  weak Γ τ α .(F z) x (ass {z} y) = ass (in-drop (x ∶ τ) y)
  weak Γ τ α .(t $ s) x (app {.Γ} {t} {s} τ₁ .α v1 v2 d1 d2) = app τ₁ α v1 v2 (weak Γ τ (τ₁ ⇒ α) t x d1) (weak Γ τ τ₁ s x d2)
  weak Γ τ .(α ⇒ τ') .(ƛ t) x (abs {.Γ} {t} α τ' y) = abs α τ' (λ z z∉t z∉Γ → perm (x ∶ τ ∷ z ∶ α ∷ Γ) (z ∶ α ∷ x ∶ τ ∷ Γ) 
    τ' (instantiate-iter t (F z) zero) (p-cons (x ∶ τ) (z ∶ α ∷ []) (z ∶ α ∷ []) Γ Γ (p-cons (z ∶ α) [] [] [] [] p-nil p-nil) (perm-id Γ)) 
    (weak (z ∶ α ∷ Γ) τ τ' (instantiate-iter t (F z) zero) x (y z z∉t (λ x' → z∉Γ (in-drop x x')))))

  {- BASE context perm weak perm-id -}  

  -- the progress theorem
  lem-progress : ∀ (t : Term) (τ : Type) → valid t → ∅ ⊢ t ∶ τ → value t ⊎ ∃ (λ t' → t ⟶β t')
  lem-progress .(F z) τ val (ass {z} ())
  lem-progress .(t $ s) τ val (app {.[]} {t} {s} τ₁ .τ v1 v2 d1 d2) with lem-progress t (τ₁ ⇒ τ) v1 d1
  lem-progress .((ƛ t) $ s) τ val (app {.[]} {.(ƛ t)} {s} τ₁ .τ v1 v2 d1 d2) | inj₁ (abs t) with lem-progress s τ₁ v2 d2
  ... | inj₁ val-s  = inj₂ (instantiate-iter t s zero ,, β val-s)
  ... | inj₂ comp-s = inj₂ (ƛ t $ proj₁ comp-s ,, app-a (abs t) (proj₂ comp-s))
  lem-progress .(t $ s) τ val (app {.[]} {t} {s} τ₁ .τ v1 v2 d1 d2) | inj₂ comp-t = inj₂ (proj₁ comp-t $ s ,, app-f (proj₂ comp-t))
  lem-progress .(ƛ t) .(α ⇒ τ) val (abs {.[]} {t} α τ y) = inj₁ (abs t)

  -- substitution lemma
    
  lem-assingment-neq : ∀ (x1 x2 : Name)(τ1 τ2 : Type) → x1 ≢ x2 → x1 ∶ τ1 ≢ x2 ∶ τ2
  lem-assingment-neq .x2 x2 .τ2 τ2 neq refl = neq refl


  lem-subst : ∀ (Γ : Context)(x : Name)(α τ : Type)(t t2 : Term) → 
              Γ , x ∶ α ⊢ t ∶ τ   → Γ ⊢ t2 ∶ α   → Γ ⊢ t [ x ↦ t2 ] ∶ τ
  lem-subst Γ x α τ .(F z) t2 (ass {z} y) der2 with x == z
  ... | yes p rewrite p = {!!} -- needs a statement that Γ is a set
  ... | no ¬p = ass (lem-∈-neq (z ∶ τ) (x ∶ α) Γ (lem-assingment-neq z x τ α (λ x' → ¬p (sym x'))) y)
  lem-subst Γ x α τ .(t $ s) t2 (app {.(x ∶ α ∷ Γ)} {t} {s} τ₁ .τ v1 v2 d1 d2) der2 = app τ₁ τ {!!} {!!} {!!} {!!}
  lem-subst Γ x α .(α' ⇒ τ) .(ƛ t) t2 (abs {.(x ∶ α ∷ Γ)} {t} α' τ y) der2 = {!!}


  lem-subsitution-iter : ∀ (n : ℕ) (Γ : Context)(t t2 : Term) (τ₁ τ₂ : Type) → valid-iter (ƛ t) n → valid-iter t2 n → value t2 
    → Γ ⊢ ƛ t ∶ τ₁ ⇒ τ₂    → Γ ⊢ t2 ∶ τ₁     →  Γ ⊢ instantiate-iter t t2 n ∶ τ₂
  lem-subsitution-iter n Γ t1 .(ƛ t) .(α ⇒ τ) τ2 (abs .t1 y) valid-t2 (abs t) (abs .(α ⇒ τ) .τ2 y') (abs α τ y0) = {!!}
--  lem-subsitution-iter n Γ t1 .(ƛ t) .(α ⇒ τ) τ2 (abs .t1 y) valid-t2 (abs t) (abs .(α ⇒ τ) .τ2 y') (abs α τ y0) = ?

  lem-subsitution : ∀ (t t2 : Term) (τ₁ τ₂ : Type) → valid (ƛ t) → valid t2 → value t2 → ∅ ⊢ ƛ t ∶ τ₁ ⇒ τ₂ → ∅ ⊢ t2 ∶ τ₁
                    → ∅ ⊢ instantiate t t2 ∶ τ₂
  lem-subsitution = lem-subsitution-iter zero ∅

  -- type preservation theorem
  lem-type-presservation : ∀ (t t' : Term) (τ : Type) → valid t → ∅ ⊢ t ∶ τ → (t ⟶β t') → ∅ ⊢ t' ∶ τ
  lem-type-presservation (B i) t' τ valid-t der ()
  lem-type-presservation (F z) t' τ valid-t der ()
  lem-type-presservation (ƛ t) t' τ valid-t der ()
  lem-type-presservation (.(ƛ t) $ t2) .(instantiate-iter t t2 0) τ (app .(ƛ t) .t2 (abs .t y) v2) (app τ₁ .τ v1 v3 d1 d2) (β {t} y') 
    = lem-subsitution t t2 τ₁ τ v1 v3 y' d1 d2
  lem-type-presservation (t1 $ t2) .(t' $ t2) τ (app .t1 .t2 v1 v2) (app τ₁ .τ v3 v4 d1 d2) (app-f {.t1} {t'} y) 
    = app τ₁ τ (valid-red t1 t' y v3) v4
        (lem-type-presservation t1 t' (τ₁ ⇒ τ) v3 d1 y) d2
  lem-type-presservation (t1 $ t2) .(t1 $ s') τ (app .t1 .t2 v1 v2) (app τ₁ .τ v3 v4 d1 d2) (app-a {.t1} {.t2} {s'} y y') 
    = app τ₁ τ v3 (valid-red t2 s' y' v4) d1
        (lem-type-presservation t2 s' τ₁ v4 d2 y')
  
-}
{-
  -- the slogan theorem
  lem-well-typed-cant-go-bad : ∀ (t : Term) (τ : Type) → valid t → ∅ ⊢ t ∶ τ → ∃ (λ val → value val × (t ≡ val ⊎ t ⟶β val))
  lem-well-typed-cant-go-bad (B i) τ (bound .0 .i ()) der
  lem-well-typed-cant-go-bad (F z) τ v (ass ())
  lem-well-typed-cant-go-bad (t1 $ t2) τ (app .t1 .t2 v1 v2) (app τ₁ .τ d1 d2) with lem-well-typed-cant-go-bad t1 ((τ₁ ⇒ τ)) v1 d1
  ... | val ,, vval ,, inj₁ t1=val = {!!}
  ... | val ,, vval ,, inj₂ t1>val = {!!}
  lem-well-typed-cant-go-bad (ƛ t) τ v der = ƛ t ,, abs t ,, inj₁ refl

-- it seems that I should change the computation rules so that the simple case is in the bottom

-}
