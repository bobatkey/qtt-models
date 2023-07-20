{-# OPTIONS --safe #-}

open import Algebra.ResourceMonoid

module AmortisedModel.GradedExponential (ℳ : ResourceMonoid) (ℳ₀ : SubResourceMonoid ℳ) where

open import Data.Empty using (⊥)
open import Data.Fin using (suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_; _*_; _≤_)
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product using (Σ-syntax; _×_; Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (refl)

open import AmortisedModel.Machine

open ResourceMonoid ℳ renaming (Carrier to |ℳ|)
open SubResourceMonoid ℳ₀ renaming (member to mor-potential)

open import AmortisedModel.Preorder ℳ ℳ₀
open import AmortisedModel.SMC ℳ ℳ₀

------------------------------------------------------------------------
-- Part VII : ℕ-graded repetition exponential

![_] : ∀ {Γ} → ℕ → Γ -Obj → Γ -Obj
![ n ] X γ .realises α v =
  Σ[ β ∈ |ℳ| ] (0 ≤D⟨ α , repeat n β ⟩ × X γ .realises β v)

!-monoidal : ∀ {Γ X Y n} → Γ ⊢ (![ n ] X) ⊗ (![ n ] Y) ⇒ ![ n ] (X ⊗ Y)
!-monoidal .realiser .expr _ = ` zero
!-monoidal .realiser .potential = acct 1
!-monoidal .realiser .potential-ok = `acct
!-monoidal {n = n} .realises γ η α (v₁ , v₂) (α₁ , α₂ , α-α₁α₂ , (β₁ , α₁-nβ₁ , β₁v₁) , (β₂ , α₂-nβ₂ , β₂v₂)) = is-realisable
  where
  is-realisable : Eval _ _ _ _
  is-realisable .result = v₁ , v₂
  is-realisable .steps = 1
  is-realisable .result-potential = α
  is-realisable .evaluation = access zero
  is-realisable .result-realises =
    β₁ ⊕ β₂ ,
    (α-α₁α₂ ； pair α₁-nβ₁ ； pair' α₂-nβ₂ ； repeat-monoidal n) ,
    β₁ , β₂ , identity , β₁v₁ , β₂v₂
  is-realisable .accounted = acct⊕-

!-wk : ∀ {Γ X m n} → m ≤ n → Γ ⊢ ![ n ] X ⇒ ![ m ] X
!-wk m≤n .realiser .expr _ = ` zero
!-wk m≤n .realiser .potential = acct 1
!-wk m≤n .realiser .potential-ok = `acct
!-wk m≤n .realises γ η α v (β , α-nβ , βv) = is-realisable
  where
  is-realisable : Eval _ _ _ _
  is-realisable .result = v
  is-realisable .steps = 1
  is-realisable .result-potential = α
  is-realisable .evaluation = access zero
  is-realisable .result-realises = β , (α-nβ ； repeat-wk m≤n) , βv
  is-realisable .accounted = acct⊕-

derelict : ∀ {Γ X} → Γ ⊢ ![ 1 ] X ⇒ X
derelict .realiser .expr _ = ` zero
derelict .realiser .potential = acct 1
derelict .realiser .potential-ok = `acct
derelict .realises γ η α v (β , α-β , β-v) .result = v
derelict .realises γ η α v (β , α-β , β-v) .steps = 1
derelict .realises γ η α v (β , α-β , β-v) .result-potential = β
derelict .realises γ η α v (β , α-β , β-v) .evaluation = access zero
derelict .realises γ η α v (β , α-β , β-v) .result-realises = β-v
derelict .realises γ η α v (β , α-β , β-v) .accounted =
  pair account ； unit' ； α-β ； unit

comult : ∀ {Γ X m n} → Γ ⊢ ![ m ] (![ n ] X) ⇒ ![ m * n ] X
comult .realiser .expr _ = ` zero
comult .realiser .potential = acct 1
comult .realiser .potential-ok = `acct
comult {m = m}{n = n} .realises γ η α v (β , α-m-β , (β' , β-n-β' , β'-v)) = is-realisable
  where
  is-realisable : Eval _ _ _ _
  is-realisable .result = v
  is-realisable .steps = 1
  is-realisable .result-potential = α
  is-realisable .evaluation = access zero
  is-realisable .result-realises =
    β' ,
    (α-m-β ； repeat-f m β-n-β' ； repeat-mul m n) ,
    β'-v
  is-realisable .accounted = acct⊕-

duplicate : ∀ {Γ X m n} → Γ ⊢ ![ m + n ] X ⇒ ![ m ] X ⊗ ![ n ] X
duplicate .realiser .expr _ = zero , zero
duplicate .realiser .potential = acct 1
duplicate .realiser .potential-ok = `acct
duplicate {m = m}{n = n} .realises γ η α v (β , α-m+n-β , β-v) = is-realisable
  where
  is-realisable : Eval _ _ _ _
  is-realisable .result = v , v
  is-realisable .steps = 1
  is-realisable .result-potential = α
  is-realisable .evaluation = mkpair zero zero
  is-realisable .result-realises =
    repeat m β , repeat n β ,
    α-m+n-β ； repeat-add-inv m n ,
    (β , identity , β-v) ,
    (β , identity , β-v)
  is-realisable .accounted = acct⊕-

discard : ∀ {Γ X} → Γ ⊢ ![ 0 ] X ⇒ I
discard .realiser .expr _ = ⋆
discard .realiser .potential = acct 1
discard .realiser .potential-ok = `acct
discard .realises γ η α v (β , α-∅ , _) = is-realisable
  where
   is-realisable : Eval _ _ _ _
   is-realisable .result = ⋆
   is-realisable .steps = 1
   is-realisable .result-potential = α
   is-realisable .evaluation = mkunit
   is-realisable .result-realises = α-∅
   is-realisable .accounted = acct⊕-
