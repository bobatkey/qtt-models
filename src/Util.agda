{-# OPTIONS --safe #-}

module Util where

open import Data.Product using (_×_; _,_)

κ : ∀ {Γ A : Set} → A → Γ → Γ × A
κ a γ = (γ , a)

κ-map : ∀ {Γ : Set}{A B : Set} → (A → B) → Γ × A → Γ × B
κ-map f (γ , a) = (γ , f a)

K : ∀ {A B : Set} → A → B → A
K a _ = a
