module Data.List.Utils where

open import Data.List

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

infix 3 _∈_

data _∈_ {A : Set} : (a : A) → (l : List A) → Set where
  in-keep : (a : A)(xs : List A) → a ∈ a ∷ xs
  in-drop : {a : A}{xs : List A} (x : A) → a ∈ xs → a ∈ x ∷ xs

_∉_ : {A : Set} (a : A)(l : List A) → Set
a ∉ l = ¬ (a ∈ l)


-- extension lemmas

lem-∈-extend-l : ∀ {A : Set} (a : A)(xs ys : List A) → a ∈ xs → a ∈ ys ++ xs
lem-∈-extend-l a xs [] inn = inn
lem-∈-extend-l a xs (x ∷ xs') inn = in-drop x (lem-∈-extend-l a xs xs' inn)

lem-∈-extend-r : ∀ {A : Set} (a : A)(xs ys : List A) → a ∈ xs → a ∈ xs ++ ys
lem-∈-extend-r a .(a ∷ xs) ys (in-keep .a xs) = in-keep a (xs ++ ys)
lem-∈-extend-r a .(x ∷ xs) ys (in-drop {.a} {xs} x y) = in-drop x (lem-∈-extend-r a xs ys y)

-- ∉ and ++

lem-∈-app-l : ∀ {A : Set} (a : A)(xs ys : List A) → a ∉ (xs ++ ys) → a ∉ xs
lem-∈-app-l a [] ys p ()
lem-∈-app-l a (x ∷ xs) ys nin axs = nin (lem-∈-extend-r a (x ∷ xs) ys axs) 

lem-∈-app-r : ∀ {A : Set} (a : A)(xs ys : List A) → a ∉ (xs ++ ys) → a ∉ ys
lem-∈-app-r a xs ys nin ays = nin (lem-∈-extend-l a ys xs ays)
