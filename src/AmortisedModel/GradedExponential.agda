{-# OPTIONS --safe #-}

open import Algebra.ResourceMonoid

module AmortisedModel.GradedExponential (ℳ : ResourceMonoid) (ℳ₀ : SubResourceMonoid ℳ) where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_; _*_; _≤_)
open import Data.Nat.Properties using (≤-reflexive; *-zeroʳ; +-identityʳ; m≤m+n)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product using (Σ-syntax; _×_; Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (refl; cong; sym)

open import AmortisedModel.Machine

open ResourceMonoid ℳ renaming (Carrier to |ℳ|)
open SubResourceMonoid ℳ₀ renaming (member to mor-potential)

open import AmortisedModel.Preorder ℳ ℳ₀
open import AmortisedModel.SMC ℳ ℳ₀

------------------------------------------------------------------------
-- Part VII : ℕ-graded repetition exponential

![_] : ∀ {Γ} → ℕ → Γ -Obj → Γ -Obj
![ 0 ] X γ .realises α ⋆ = ⊤
![ 0 ] X γ .realises α (v , v₁) = ⊥
![ 0 ] X γ .realises α true = ⊥
![ 0 ] X γ .realises α false = ⊥
![ 0 ] X γ .realises α (clo x x₁) = ⊥
![ suc n ] X γ .realises α v =
  Σ[ β ∈ |ℳ| ] (0 ≤D⟨ α , repeat (suc n) β ⟩ × X γ .realises β v)


![_]-map : ∀ {Γ} n {X Y} → Γ ⊢ X ⇒ Y → Γ ⊢ ![ n ] X ⇒ ![ n ] Y
![ 0 ]-map f = identity-realised g
  where g : ∀ γ α v → ![ 0 ] _ γ .realises α v → ![ 0 ] _ γ .realises α v
        g γ α ⋆ x = x
![ suc n ]-map f .realiser .expr = f .realiser .expr
![ suc n ]-map f .realiser .potential = repeat (suc n) (f .realiser .potential)
![ suc n ]-map f .realiser .potential-ok =
  `repeat (suc n) (f .realiser .potential) (f .realiser .potential-ok)
![ suc n ]-map f .realises γ η α v (β , α≤nβ , X-γ-β-v) = is-realisable
  where
  is-realisable : Eval _ _ _ _
  is-realisable .result = f .realises γ η β v X-γ-β-v .result
  is-realisable .steps = f .realises γ η β v X-γ-β-v .steps
  is-realisable .result-potential = repeat (suc n) (f .realises γ η β v X-γ-β-v .result-potential)
  is-realisable .evaluation = f .realises γ η β v X-γ-β-v .evaluation
  is-realisable .result-realises =
    f .realises γ η β v X-γ-β-v .result-potential ,
    identity ,
    f .realises γ η β v X-γ-β-v .result-realises
  is-realisable .accounted =
    weaken
      (pair' α≤nβ ；
       repeat-monoidal (suc n) ；
       repeat-f' (suc n) (f .realises γ η β v X-γ-β-v .accounted))
      (m≤m+n _ _)

!-subst : ∀ {Γ₁ Γ₂ n X} (f : Γ₁ → Γ₂) → Γ₁ ⊢ (⟨ f ⟩ (![ n ] X)) ≅ (![ n ] (⟨ f ⟩ X))
!-subst {n = zero} {X = X} f = realised-iso g h
  where g : ∀ γ α v → (⟨ f ⟩ (![ zero ] X)) γ .realises α v → (![ zero ] (⟨ f ⟩ X)) γ .realises α v
        g γ α ⋆ x = x
        h : ∀ γ α v → (![ zero ] (⟨ f ⟩ X)) γ .realises α v → (⟨ f ⟩ (![ zero ] X)) γ .realises α v
        h γ α ⋆ x = x
!-subst {n = suc n} {X = X} f = realised-iso g h
  where g : ∀ γ α v → (⟨ f ⟩ (![ suc n ] X)) γ .realises α v → (![ suc n ] (⟨ f ⟩ X)) γ .realises α v
        g γ α v x = x
        h : ∀ γ α v → (![ suc n ] (⟨ f ⟩ X)) γ .realises α v → (⟨ f ⟩ (![ suc n ] X)) γ .realises α v
        h γ α v x = x

!-monoidal : ∀ {Γ X Y n} → Γ ⊢ (![ n ] X) ⊗ (![ n ] Y) ⇒ ![ n ] (X ⊗ Y)
!-monoidal {n = zero} .realiser .expr _ = ⋆
!-monoidal {n = zero} .realiser .potential = acct 1
!-monoidal {n = zero} .realiser .potential-ok = `acct
!-monoidal {n = zero} .realises γ η α _ _ .result = ⋆
!-monoidal {n = zero} .realises γ η α _ _ .steps = 1
!-monoidal {n = zero} .realises γ η α _ _ .result-potential = α
!-monoidal {n = zero} .realises γ η α _ _ .evaluation = mkunit
!-monoidal {n = zero} .realises γ η α _ _ .result-realises = tt
!-monoidal {n = zero} .realises γ η α _ _ .accounted = acct⊕-
!-monoidal {n = suc n} .realiser .expr _ = ` zero
!-monoidal {n = suc n} .realiser .potential = acct 1
!-monoidal {n = suc n} .realiser .potential-ok = `acct
!-monoidal {n = suc n} .realises γ η α (v₁ , v₂) (α₁ , α₂ , α-α₁α₂ , (β₁ , α₁-nβ₁ , β₁v₁) , (β₂ , α₂-nβ₂ , β₂v₂)) = is-realisable
  where
  is-realisable : Eval _ _ _ _
  is-realisable .result = v₁ , v₂
  is-realisable .steps = 1
  is-realisable .result-potential = α
  is-realisable .evaluation = access zero
  is-realisable .result-realises =
    β₁ ⊕ β₂ ,
    (α-α₁α₂ ； pair α₁-nβ₁ ； pair' α₂-nβ₂ ； repeat-monoidal (suc n)) ,
    β₁ , β₂ , identity , β₁v₁ , β₂v₂
  is-realisable .accounted = acct⊕-

to-zero : ∀ {Γ X Y} → Γ ⊢ X ⇒ ![ 0 ] Y
to-zero .realiser .expr _ = ⋆
to-zero .realiser .potential = acct 1
to-zero .realiser .potential-ok = `acct
to-zero .realises γ η α _ _ .result = ⋆
to-zero .realises γ η α _ _ .steps = 1
to-zero .realises γ η α _ _ .result-potential = α
to-zero .realises γ η α _ _ .evaluation = mkunit
to-zero .realises γ η α _ _ .result-realises = tt
to-zero .realises γ η α _ _ .accounted = acct⊕-

!-wk : ∀ {Γ X m n} → m ≤ n → Γ ⊢ ![ n ] X ⇒ ![ m ] X
!-wk {m = zero} _ = to-zero
!-wk {m = suc m} {n = zero} ()
!-wk {m = suc m} {n = suc n} m≤n .realiser .expr _ = ` zero
!-wk {m = suc m} {n = suc n} m≤n .realiser .potential = acct 1
!-wk {m = suc m} {n = suc n} m≤n .realiser .potential-ok = `acct
!-wk {m = suc m} {n = suc n} m≤n .realises γ η α v (β , α-nβ , βv) = is-realisable
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
comult {m = zero}{n = zero} = to-zero
comult {m = zero}{n = suc n} = to-zero
comult {m = suc m}{n = zero} = (!-wk (≤-reflexive (*-zeroʳ m))) ∘ to-zero
comult {m = suc m}{n = suc n} .realiser .expr _ = ` zero
comult {m = suc m}{n = suc n} .realiser .potential = acct 1
comult {m = suc m}{n = suc n} .realiser .potential-ok = `acct
comult {m = suc m}{n = suc n} .realises γ η α v (β , α-m-β , (β' , β-n-β' , β'-v)) = is-realisable
  where
  is-realisable : Eval _ _ _ _
  is-realisable .result = v
  is-realisable .steps = 1
  is-realisable .result-potential = α
  is-realisable .evaluation = access zero
  is-realisable .result-realises =
    β' ,
    (α-m-β ； repeat-f (suc m) β-n-β' ； repeat-mul (suc m) (suc n)) ,
    β'-v
  is-realisable .accounted = acct⊕-

duplicate : ∀ {Γ X m n} → Γ ⊢ ![ m + n ] X ⇒ ![ m ] X ⊗ ![ n ] X
duplicate {m = zero}{n = zero} = (to-zero ⊗m to-zero) ∘ unit-inv-m
duplicate {m = suc m}{n = zero} =
  (!-wk (≤-reflexive (sym (cong suc (+-identityʳ m)))) ⊗m to-zero) ∘ unit-inv-m
duplicate {m = zero}{n = suc n} =
  (to-zero ⊗m id) ∘ (swap ∘ unit-inv-m)
duplicate {m = suc m}{n = suc n} .realiser .expr _ = zero , zero
duplicate {m = suc m}{n = suc n} .realiser .potential = acct 1
duplicate {m = suc m}{n = suc n} .realiser .potential-ok = `acct
duplicate {m = suc m}{n = suc n} .realises γ η α v (β , α-m+n-β , β-v) = is-realisable
  where
  is-realisable : Eval _ _ _ _
  is-realisable .result = v , v
  is-realisable .steps = 1
  is-realisable .result-potential = α
  is-realisable .evaluation = mkpair zero zero
  is-realisable .result-realises =
    repeat (suc m) β , repeat (suc n) β ,
    α-m+n-β ； repeat-add-inv (suc m) (suc n) ,
    (β , identity , β-v) ,
    (β , identity , β-v)
  is-realisable .accounted = acct⊕-

discard : ∀ {Γ X} → Γ ⊢ ![ 0 ] X ≅ I
discard = terminal , to-zero
