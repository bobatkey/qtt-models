{-# OPTIONS --safe #-}

open import Algebra.ResourceMonoid

module AmortisedModel.SMC (ℳ : ResourceMonoid) (ℳ₀ : SubResourceMonoid ℳ) where

open import Data.Empty using (⊥)
open import Data.Fin using (suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_; _*_; _≤_)
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product using (Σ-syntax; _×_; Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (refl)

open import AmortisedModel.Machine

open ResourceMonoid ℳ renaming (Carrier to |ℳ|; assoc to ℳ-assoc)
open SubResourceMonoid ℳ₀ renaming (member to mor-potential)

open import AmortisedModel.Preorder ℳ ℳ₀

------------------------------------------------------------------------
-- Part II : has a terminal object

I : ∀ {Γ : Set} → Γ -Obj
I γ .realises α ⋆         = 0 ≤D⟨ α , ∅ ⟩
I γ .realises α (_ , _)   = ⊥
I γ .realises α true      = ⊥
I γ .realises α false     = ⊥
I γ .realises α (clo _ _) = ⊥

I-subst : ∀ {Γ₁ Γ₂} (f : Γ₁ → Γ₂) → Γ₁ ⊢ ⟨ f ⟩ I ≅ I
I-subst f = realised-iso ⟨f⟩I⊆I I⊆⟨f⟩I
  where
    ⟨f⟩I⊆I : ∀ γ α v → (⟨ f ⟩ I) γ .realises α v → I γ .realises α v
    ⟨f⟩I⊆I γ α ⋆ x = x
    I⊆⟨f⟩I : ∀ γ α v → I γ .realises α v → (⟨ f ⟩ I) γ .realises α v
    I⊆⟨f⟩I γ α ⋆ x = x

terminal : ∀ {Γ X} → Γ ⊢ X ⇒ I
terminal .realiser .expr _ = ⋆
terminal .realiser .potential = acct 1
terminal .realiser .potential-ok = `acct
terminal .realises γ η α _ _ .result = ⋆
terminal .realises γ η α _ _ .steps = 1
terminal .realises γ η α _ _ .result-potential = α
terminal .realises γ η α _ _ .evaluation = mkunit
terminal .realises γ η α _ _ .result-realises = term
terminal .realises γ η α _ _ .accounted = acct⊕-

------------------------------------------------------------------------
-- Part III : has an ordered commutative monoid

_⊗_ : ∀ {Γ} → Γ -Obj → Γ -Obj → Γ -Obj
(X ⊗ Y) γ .realises α (v₁ , v₂) =
   Σ[ α₁ ∈ |ℳ| ]
   Σ[ α₂ ∈ |ℳ| ]
   (0 ≤D⟨ α , α₁ ⊕ α₂ ⟩ × X γ .realises α₁ v₁ × Y γ .realises α₂ v₂)
(X ⊗ Y) γ .realises α ⋆ = ⊥
(X ⊗ Y) γ .realises α (clo _ _) = ⊥
(X ⊗ Y) γ .realises α true = ⊥
(X ⊗ Y) γ .realises α false = ⊥

infixl 20 _⊗_

⊗-subst : ∀ {Γ Δ X Y} (f : Γ → Δ) → Γ ⊢ ⟨ f ⟩ (X ⊗ Y) ≅ (⟨ f ⟩ X) ⊗ (⟨ f ⟩ Y)
⊗-subst {Γ}{Δ}{X}{Y} f = realised-iso fwd bwd
  where fwd : ∀ γ α v → (⟨ f ⟩ (X ⊗ Y)) γ .realises α v → (⟨ f ⟩ X ⊗ ⟨ f ⟩ Y) γ .realises α v
        fwd γ α (v₁ , v₂) x = x

        bwd : ∀ γ α v →  (⟨ f ⟩ X ⊗ ⟨ f ⟩ Y) γ .realises α v → (⟨ f ⟩ (X ⊗ Y)) γ .realises α v
        bwd γ α (v₁ , v₂) x = x


swap : ∀ {Γ X Y} → Γ ⊢ (X ⊗ Y) ⇒ (Y ⊗ X)
swap .realiser .expr _ = letpair zero then (zero , suc zero)
swap .realiser .potential = acct 2
swap .realiser .potential-ok = `acct
swap .realises γ η α (v₁ , v₂) (α₁ , α₂ , d , X-α₁-v₁ , Y-α₂-v₂) = is-realisable
  where
    is-realisable : Eval _ _ _ _
    is-realisable .result = v₂ , v₁
    is-realisable .steps = 2
    is-realisable .result-potential = α
    is-realisable .evaluation = letpair zero (mkpair zero (suc zero))
    is-realisable .result-realises = α₂ , α₁ , d ； symmetry , Y-α₂-v₂ , X-α₁-v₁
    is-realisable .accounted = acct⊕-

assoc-m : ∀ {Γ X Y Z} → Γ ⊢ X ⊗ (Y ⊗ Z) ⇒ (X ⊗ Y) ⊗ Z
assoc-m .realiser .expr _ =
  letpair zero then
  letpair zero then
  seq (suc (suc (suc zero)) , suc zero) then
  (zero , suc zero)
assoc-m .realiser .potential = acct 5
assoc-m .realiser .potential-ok = `acct
assoc-m .realises γ η α (vx , (vy , vz)) (α₁ , α₂ , d , vx-r , α₃ , α₄ , d' , vy-r , vz-r) =
  is-realisable
  where
   is-realisable : Eval _ _ _ _
   is-realisable .result = (vx , vy) , vz
   is-realisable .steps = 5
   is-realisable .result-potential = α
   is-realisable .evaluation =
     letpair zero
       (letpair zero
          (seq (mkpair (suc (suc (suc zero))) (suc zero))
            (mkpair zero (suc zero))))
   is-realisable .result-realises =
      α₁ ⊕ α₃ , α₄ , (d ； pair' d' ； ℳ-assoc) ,
      (α₁ , α₃ , identity , vx-r , vy-r) , vz-r
   is-realisable .accounted = acct⊕-

assoc-inv-m : ∀ {Γ X Y Z} → Γ ⊢ (X ⊗ Y) ⊗ Z ⇒ X ⊗ (Y ⊗ Z)
assoc-inv-m .realiser .expr _ =
  letpair zero then
  letpair suc zero then
  seq (zero , suc (suc zero)) then
  (suc (suc zero) , zero)
assoc-inv-m .realiser .potential = acct 5
assoc-inv-m .realiser .potential-ok = `acct
assoc-inv-m .realises γ η α ((vx , vy) , vz) (α₁ , α₂ , d , (α₃ , α₄ , d' , vx-r , vy-r) , vz-r) =
  is-realisable
  where
   is-realisable : Eval _ _ _ _
   is-realisable .result = vx , (vy , vz)
   is-realisable .steps = 5
   is-realisable .result-potential = α
   is-realisable .evaluation = letpair zero (letpair (suc zero) (seq (mkpair zero (suc (suc zero))) (mkpair (suc (suc zero)) zero)))
   is-realisable .result-realises = α₃ , α₄ ⊕ α₂ , (d ； pair d' ； assoc-inv) , vx-r , α₄ , α₂ , identity , vy-r , vz-r
   is-realisable .accounted = acct⊕-

assoc : ∀ {Γ X Y Z} → Γ ⊢ (X ⊗ (Y ⊗ Z)) ≅ ((X ⊗ Y) ⊗ Z)
assoc = assoc-m , assoc-inv-m

unit-m : ∀ {Γ X} → Γ ⊢ (X ⊗ I) ⇒ X
unit-m .realiser .expr _ = letpair zero then ` (suc zero)
unit-m .realiser .potential = acct 2
unit-m .realiser .potential-ok = `acct
unit-m .realises γ η α (vx , ⋆) (α₁ , α₂ , d , vx-r , ⋆-r) = is-realisable
  where
    is-realisable : Eval _ _ _ _
    is-realisable .result = vx
    is-realisable .steps = 2
    is-realisable .result-potential = α₁
    is-realisable .evaluation = letpair zero (access (suc zero))
    is-realisable .result-realises = vx-r
    is-realisable .accounted = acct⊕- ； d ； pair' ⋆-r ； unit

unit-inv-m : ∀ {Γ X} → Γ ⊢ X ⇒ (X ⊗ I)
unit-inv-m .realiser .expr _ = seq ⋆ then (suc zero , zero)
unit-inv-m .realiser .potential = acct 3
unit-inv-m .realiser .potential-ok = `acct
unit-inv-m .realises γ η α vx vx-r = is-realisable
  where
    is-realisable : Eval _ _ _ _
    is-realisable .result = (vx , ⋆)
    is-realisable .steps = 3
    is-realisable .result-potential = α
    is-realisable .evaluation = seq mkunit (mkpair (suc zero) zero)
    is-realisable .result-realises = α , ∅ , unit-inv , vx-r , identity
    is-realisable .accounted = acct⊕-

_⊗m_ : ∀ {Γ X₁ X₂ Y₁ Y₂} →
       Γ ⊢ X₁ ⇒ Y₁ →
       Γ ⊢ X₂ ⇒ Y₂ →
       Γ ⊢ X₁ ⊗ X₂ ⇒ Y₁ ⊗ Y₂
(f ⊗m g) .realiser .expr n =
  letpair zero then
  seq g .realiser .expr (2 + n) then
  seq ` (suc (suc zero)) then
  seq f .realiser .expr (4 + n) then
  (zero , suc (suc zero))
(f ⊗m g) .realiser .potential =
   acct 6 ⊕ (f .realiser .potential ⊕ g .realiser .potential)
(f ⊗m g) .realiser .potential-ok =
   `acct `⊕ (f .realiser .potential-ok `⊕ g .realiser .potential-ok)
(f ⊗m g) .realises γ η α (v₁ , v₂) (α₁ , α₂ , d , X₁-α₁-v₁ , X₂-α₂-v₂) =
  is-realisable
  where
    r₁ = f .realises γ (η ,- _ ,- _ ,- _ ,- _) α₁ v₁ X₁-α₁-v₁
    r₂ = g .realises γ (η ,- _ ,- _) α₂ v₂ X₂-α₂-v₂

    is-realisable : Eval _ _ _ _
    is-realisable .result = r₁ .result , r₂ .result
    is-realisable .steps = 1 + (r₂ .steps + 1) + (2 + r₁ .steps + 1 + 1)
    is-realisable .result-potential = r₁ .result-potential ⊕ r₂ .result-potential
    is-realisable .evaluation = letpair zero (seq (r₂ .evaluation) (seq (access (suc (suc zero))) (seq (r₁ .evaluation) (mkpair zero (suc (suc zero))))))
    is-realisable .result-realises =
      r₁ .result-potential , r₂ .result-potential , identity , r₁ .result-realises , r₂ .result-realises
    is-realisable .accounted =
      weaken (assoc-inv ；
              acct⊕- ；
              pair' (d ； symmetry) ；
              assoc-inv ；
              pair' (ℳ-assoc ； symmetry) ；
              ℳ-assoc ；
              pair' (r₂ .accounted) ；
              pair (r₁ .accounted))
             (≤-reflexive (begin
                             1 + (r₂ .steps + 1) + (2 + r₁ .steps + 1 + 1)
                           ≡⟨ +-*-Solver.solve 2
                                 (λ x y →
                                       con 1 :+ (x :+ con 1) :+ (con 2 :+ y :+ con 1 :+ con 1)
                                       := con 6 :+ x :+ y) refl (r₂ .steps) (r₁ .steps) ⟩
                             6 + r₂ .steps + r₁ .steps
                           ∎))
      where open Eq.≡-Reasoning
            open +-*-Solver using (solve; con; _:+_; _:=_)

------------------------------------------------------------------------
-- Part IV : Linear functions
_⊸_ : ∀ {Γ} → Γ -Obj → Γ -Obj → Γ -Obj
(X ⊸ Y) γ .realises α (clo E η) =
   ∀ (α' : |ℳ|) (v w : val) → X γ .realises α' v → Eval (Y γ) E (α ⊕ α') (η ,- w ,- v)
(X ⊸ Y) γ .realises α ⋆ = ⊥
(X ⊸ Y) γ .realises α (_ , _) = ⊥
(X ⊸ Y) γ .realises α true = ⊥
(X ⊸ Y) γ .realises α false = ⊥

⊸-subst : ∀ {Γ₁ Γ₂ X Y} (f : Γ₁ → Γ₂) →
            Γ₁ ⊢ ⟨ f ⟩ (X ⊸ Y) ≅ ((⟨ f ⟩ X) ⊸ (⟨ f ⟩ Y))
⊸-subst {X = X}{Y = Y} f = realised-iso fwd bwd
  where
  fwd : ∀ γ α v → (⟨ f ⟩ (X ⊸ Y)) γ .realises α v → ((⟨ f ⟩ X) ⊸ (⟨ f ⟩ Y)) γ .realises α v
  fwd γ α (clo _ _) x = x
  bwd : ∀ γ α v → ((⟨ f ⟩ X) ⊸ (⟨ f ⟩ Y)) γ .realises α v → (⟨ f ⟩ (X ⊸ Y)) γ .realises α v
  bwd γ α (clo _ _) x = x

Λ : ∀ {Γ X Y Z} → Γ ⊢ X ⊗ Y ⇒ Z → Γ ⊢ X ⇒ Y ⊸ Z
Λ f .realiser .expr n = ƛ (seq (suc (suc zero) , zero) then f .realiser .expr (3 + n))
Λ f .realiser .potential = acct 1 ⊕ (acct 2 ⊕ f .realiser .potential)
Λ f .realiser .potential-ok = `acct `⊕ (`acct `⊕ f .realiser .potential-ok)
Λ f .realises γ {n₀} η α vx vx-r = is-realisable
  where
    is-realisable : Eval _ _ _ _
    is-realisable .result =
       clo (seq (suc (suc zero) , zero) then f .realiser .expr (3 + n₀)) (η ,- vx)
    is-realisable .steps = 1
    is-realisable .result-potential = (acct 2 ⊕ f .realiser .potential) ⊕ α
    is-realisable .evaluation = lam
    is-realisable .result-realises α' vy vw vy-r = is-realisable'
      where
        r = f .realises γ (η ,- vx ,- vw ,- vy) (α ⊕ α') (vx , vy) (α , α' , identity , vx-r , vy-r)

        is-realisable' : Eval _ _ _ _
        is-realisable' .result = r .result
        is-realisable' .steps = 2 + r .steps
        is-realisable' .result-potential = r .result-potential
        is-realisable' .evaluation = seq (mkpair (suc (suc zero)) zero) (r .evaluation)
        is-realisable' .result-realises = r .result-realises
        is-realisable' .accounted = assoc-inv ； assoc-inv ； acct⊕- ； r .accounted
    is-realisable .accounted = assoc-inv ； acct⊕-

apply : ∀ {Γ X Y} → Γ ⊢ (X ⊸ Y) ⊗ X ⇒ Y
apply .realiser .expr _ = letpair zero then (suc zero · zero)
apply .realiser .potential = acct 2
apply .realiser .potential-ok = `acct
apply .realises γ η₀ α (clo E η , vx) (α₁ , α₂ , d , vf-r , vx-r) = is-realisable
  where
    y-r = vf-r α₂ vx (clo E η) vx-r

    is-realisable : Eval _ _ _ _
    is-realisable .result = y-r .result
    is-realisable .steps = 2 + y-r .steps
    is-realisable .result-potential = y-r .result-potential
    is-realisable .evaluation = letpair zero (app (suc zero) zero (y-r .evaluation))
    is-realisable .result-realises = y-r .result-realises
    is-realisable .accounted = acct⊕- ； d ； y-r .accounted
