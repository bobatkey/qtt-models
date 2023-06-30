{-# OPTIONS --safe #-}

open import Algebra.ResourceMonoid

module AmortisedRealisabilityModel (ℳ : ResourceMonoid) (ℳ₀ : SubResourceMonoid ℳ) where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; zero; _+_; _*_; _≤_)
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Fin using (suc; zero)
open import Data.Product using (Σ-syntax; _×_; Σ; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality as Eq

open import MachineModel

open ResourceMonoid ℳ renaming (Carrier to |ℳ|)
open SubResourceMonoid ℳ₀ renaming (member to mor-potential)

record Elem : Set₁ where
  field
    realises : |ℳ| → val → Set
open Elem public

_-Obj : Set → Set₁
Γ -Obj = Γ → Elem

record Eval {n} (Y : Elem) (e : exp n) (α : |ℳ|) (η : env n) : Set where
  field
    result           : val
    steps            : ℕ
    result-potential : |ℳ|
    evaluation       : e , η ⇓[ steps ] result
    result-realises  : Y .realises result-potential result
    accounted        : steps ≤D⟨ α , result-potential ⟩
open Eval public

record Realiser : Set where
  field
    expr         : ∀ n → exp (suc n)
    potential    : |ℳ|
    potential-ok : mor-potential potential
open Realiser public

record _⊢_⇒_ (Γ : Set) (X Y : Γ → Elem) : Set where
  field
    realiser : Realiser
    realises : ∀ γ → ∀ {n} (η : env n) (α : |ℳ|) v →
               X γ .realises α v →
               Eval (Y γ) (realiser .expr n) (realiser .potential ⊕ α) (η ,- v)
open _⊢_⇒_ public

_⊢_≅_ : (Γ : Set) → Γ -Obj → Γ -Obj → Set
Γ ⊢ X ≅ Y = (Γ ⊢ X ⇒ Y) × (Γ ⊢ Y ⇒ X)

infix 21 ⟨_⟩_
infix 19 _⊢_⇒_

------------------------------------------------------------------------------
identity-realiser : Realiser
identity-realiser .expr _ = ` zero
identity-realiser .potential = acct 1
identity-realiser .potential-ok = `acct

identity-realises : ∀ {Γ} {X Y : Γ -Obj} →
  (∀ {γ α v} → X γ .realises α v → Y γ .realises α v) →
  ∀ γ {n} (η : env n) (α : |ℳ|) v →
  X γ .realises α v → Eval (Y γ) (` zero) (acct 1 ⊕ α) (η ,- v)
identity-realises X⊆Y γ η α v X-v .result = v
identity-realises X⊆Y γ η α v X-v .steps = 1
identity-realises X⊆Y γ η α v X-v .result-potential = α
identity-realises X⊆Y γ η α v X-v .evaluation = access zero
identity-realises X⊆Y γ η α v X-v .result-realises = X⊆Y X-v
identity-realises X⊆Y γ η α v X-v .accounted = acct⊕-

------------------------------------------------------------------------
-- Part 0: Reindexing

⟨_⟩_ : ∀ {Γ Δ} → (Γ → Δ) → Δ -Obj → Γ -Obj
⟨ f ⟩ X = λ γ → X (f γ)

⟨_⟩-map : ∀ {Γ Δ X Y} (f : Γ → Δ) → Δ ⊢ X ⇒ Y → Γ ⊢ (⟨ f ⟩ X) ⇒ (⟨ f ⟩ Y)
⟨ f ⟩-map g .realiser = g .realiser
⟨ f ⟩-map g .realises γ η α v x = g .realises (f γ) η α v x

⟨id⟩ : ∀ {Γ X} → Γ ⊢ X ≅ (⟨ (λ x → x) ⟩ X)
⟨id⟩ .proj₁ .realiser = identity-realiser
⟨id⟩ .proj₁ .realises = identity-realises (λ x → x)
⟨id⟩ .proj₂ .realiser = identity-realiser
⟨id⟩ .proj₂ .realises = identity-realises (λ x → x)

------------------------------------------------------------------------
-- Part I : Identity and composition in each fibre

id : ∀ {Γ X} → Γ ⊢ X ⇒ X
id .realiser = identity-realiser
id .realises = identity-realises (λ x → x)

_∘_ : ∀ {Γ X Y Z} → Γ ⊢ Y ⇒ Z → Γ ⊢ X ⇒ Y → Γ ⊢ X ⇒ Z
(f ∘ g) .realiser .expr n = seq (g .realiser .expr n) then f .realiser .expr (suc n)
(f ∘ g) .realiser .potential = acct 1 ⊕ f .realiser .potential ⊕ g .realiser .potential
(f ∘ g) .realiser .potential-ok =
   (`acct `⊕ f .realiser .potential-ok) `⊕ g .realiser .potential-ok
(f ∘ g) .realises γ η α v X-α-v = is-realisable
  where
    gr = g .realises γ η α v X-α-v
    fr = f .realises γ (η ,- v) (gr .result-potential) (gr .result) (gr .result-realises)

    is-realisable : Eval _ _ _ _
    is-realisable .result = fr .result
    is-realisable .steps = gr .steps + 1 + fr .steps
    is-realisable .result-potential = fr .result-potential
    is-realisable .evaluation = seq (gr .evaluation) (fr .evaluation)
    is-realisable .result-realises = fr .result-realises
    is-realisable .accounted =
       assoc-inv ； assoc-inv ； pair' (pair' (gr .accounted)) ； acct⊕- ； fr .accounted

------------------------------------------------------------------------
-- Part II : has a terminal object

I : ∀ {Γ : Set} → Γ -Obj
I γ .realises α ⋆         = 0 ≤D⟨ α , ∅ ⟩
I γ .realises α (_ , _)   = ⊥
I γ .realises α true      = ⊥
I γ .realises α false     = ⊥
I γ .realises α (clo _ _) = ⊥

-- FIXME: I-subst

terminal : ∀ {Γ X} → Γ ⊢ X ⇒ I
terminal .realiser .expr _ = ⋆
terminal .realiser .potential = acct 1
terminal .realiser .potential-ok = `acct
terminal .realises γ η α _ _ = is-realisable
  where
    is-realisable : Eval _ _ _ _
    is-realisable .result = ⋆
    is-realisable .steps = 1
    is-realisable .result-potential = α
    is-realisable .evaluation = mkunit
    is-realisable .result-realises = term
    is-realisable .accounted = acct⊕-

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

-- FIXME: _⊗_ commutes with reindexing

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
      α₁ ⊕ α₃ , α₄ , (d ； pair' d' ； assoc) ,
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
      weaken (assoc-inv ； acct⊕- ； pair' (d ； symmetry) ； assoc-inv ； pair' (assoc ； symmetry) ； assoc ； pair' (r₂ .accounted) ； pair (r₁ .accounted))
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

⊸-reindex-1 : ∀ {Γ₁ Γ₂ X Y} (f : Γ₁ → Γ₂) →
            Γ₁ ⊢ ⟨ f ⟩ (X ⊸ Y) ⇒ (⟨ f ⟩ X) ⊸ (⟨ f ⟩ Y)
⊸-reindex-1 f .realiser = identity-realiser
⊸-reindex-1 f .realises γ η α v x .result = v
⊸-reindex-1 f .realises γ η α v x .steps = 1
⊸-reindex-1 f .realises γ η α v x .result-potential = α
⊸-reindex-1 f .realises γ η α v x .evaluation = access zero
⊸-reindex-1 f .realises γ η α (clo E η') x .result-realises = x
⊸-reindex-1 f .realises γ η α v x .accounted = acct⊕-

⊸-reindex-2 : ∀ {Γ₁ Γ₂ X Y} (f : Γ₁ → Γ₂) →
            Γ₁ ⊢ (⟨ f ⟩ X) ⊸ (⟨ f ⟩ Y) ⇒ ⟨ f ⟩ (X ⊸ Y)
⊸-reindex-2 f .realiser = identity-realiser
⊸-reindex-2 f .realises γ η α v x .result = v
⊸-reindex-2 f .realises γ η α v x .steps = 1
⊸-reindex-2 f .realises γ η α v x .result-potential = α
⊸-reindex-2 f .realises γ η α v x .evaluation = access zero
⊸-reindex-2 f .realises γ η α (clo E η') x .result-realises = x
⊸-reindex-2 f .realises γ η α v x .accounted = acct⊕-

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

------------------------------------------------------------------------
-- Part V : Products

`∀ : ∀ {Γ} A → (Σ Γ A) -Obj → Γ -Obj
`∀ A X γ .realises α ⋆ = ⊥
`∀ A X γ .realises α (_ , _) = ⊥
`∀ A X γ .realises α true = ⊥
`∀ A X γ .realises α false = ⊥
`∀ A X γ .realises α (clo E η) = ∀ a v → Eval (X (γ , a)) E α (η ,- v ,- ⋆)

⟪_⟫ : ∀ {Γ₁ Γ₂ : Set} → (Γ₁ → Γ₂) → (Γ₂ → Set) → (Γ₁ → Set)
⟪ f ⟫ A γ = A (f γ)

`∀-subst-1 : ∀ {Γ₁ Γ₂ A X} (f : Γ₁ → Γ₂) →
             Γ₁ ⊢ ⟨ f ⟩ (`∀ A X) ⇒ `∀ (⟪ f ⟫ A) (⟨ (λ x → (f (x .proj₁)) , x .proj₂) ⟩ X)
`∀-subst-1 f .realiser .expr _ = ` zero
`∀-subst-1 f .realiser .potential = acct 1
`∀-subst-1 f .realiser .potential-ok = `acct
`∀-subst-1 f .realises γ η α v x .result = v
`∀-subst-1 f .realises γ η α v x .steps = 1
`∀-subst-1 f .realises γ η α v x .result-potential = α
`∀-subst-1 f .realises γ η α v x .evaluation = access zero
`∀-subst-1 f .realises γ η α (clo E η') x .result-realises = x
`∀-subst-1 f .realises γ η α v x .accounted = acct⊕-

`∀-subst-2 : ∀ {Γ₁ Γ₂ A X} (f : Γ₁ → Γ₂) →
             Γ₁ ⊢ `∀ (⟪ f ⟫ A) (⟨ (λ x → (f (x .proj₁)) , x .proj₂) ⟩ X) ⇒ ⟨ f ⟩ (`∀ A X)
`∀-subst-2 f .realiser .expr _ = ` zero
`∀-subst-2 f .realiser .potential = acct 1
`∀-subst-2 f .realiser .potential-ok = `acct
`∀-subst-2 f .realises γ η α v x .result = v
`∀-subst-2 f .realises γ η α v x .steps = 1
`∀-subst-2 f .realises γ η α v x .result-potential = α
`∀-subst-2 f .realises γ η α v x .evaluation = access zero
`∀-subst-2 f .realises γ η α (clo E η') x .result-realises = x
`∀-subst-2 f .realises γ η α v x .accounted = acct⊕-

`∀-intro : ∀ {Γ A X Y} →
           (Σ Γ A) ⊢ (⟨ proj₁ ⟩ X) ⇒ Y →
           Γ ⊢ X ⇒ (`∀ A Y)
`∀-intro f .realiser .expr n = ƛ (seq (` (suc (suc zero))) then (f .realiser .expr _))
`∀-intro f .realiser .potential = acct 1 ⊕ (acct 2 ⊕ f .realiser .potential)
`∀-intro f .realiser .potential-ok = `acct `⊕ (`acct `⊕ f .realiser .potential-ok)
`∀-intro f .realises γ η α v X-α-v .result =
   clo (seq (` (suc (suc zero))) then (f .realiser .expr _)) (η ,- v)
`∀-intro f .realises γ η α v X-α-v .steps = 1
`∀-intro f .realises γ η α v X-α-v .result-potential = acct 2 ⊕ f .realiser .potential ⊕ α
`∀-intro f .realises γ η α v X-α-v .evaluation = lam
`∀-intro f .realises γ η α v X-α-v .result-realises a v' = is-realisable
   where
     f-r = f .realises (γ , a) (η ,- v ,- v' ,- ⋆) α v X-α-v

     is-realisable : Eval _ _ _ _
     is-realisable .result = f-r .result
     is-realisable .steps = 2 + f-r .steps
     is-realisable .result-potential = f-r .result-potential
     is-realisable .evaluation = seq (access (suc (suc zero))) (f-r .evaluation)
     is-realisable .result-realises = f-r .result-realises
     is-realisable .accounted = assoc-inv ； acct⊕- ； f-r .accounted
`∀-intro f .realises γ η α v X-α-v .accounted = assoc-inv ； acct⊕-

`∀-proj : ∀ {Γ A X} →
          (Σ Γ A) ⊢ (⟨ proj₁ ⟩ `∀ A X) ⇒ X
`∀-proj .realiser .expr _ = seq ⋆ then (suc zero · zero)
`∀-proj .realiser .potential = acct 3
`∀-proj .realiser .potential-ok = `acct
`∀-proj .realises (γ , a) η α (clo E η') E-x = is-realisable
  where
    v-r = E-x a (clo E η')

    is-realisable : Eval _ _ _ _
    is-realisable .result = v-r .result
    is-realisable .steps = 3 + v-r .steps
    is-realisable .result-potential = v-r .result-potential
    is-realisable .evaluation =
      seq mkunit (app (suc zero) zero (v-r .evaluation))
    is-realisable .result-realises = v-r .result-realises
    is-realisable .accounted = acct⊕- ； v-r .accounted

------------------------------------------------------------------------
-- Co-products

`∃ : ∀ {Γ} A → (Σ Γ A) -Obj → Γ -Obj
`∃ A X γ .realises α v = Σ[ a ∈ A γ ] X (γ , a) .realises α v

`∃-elim : ∀ {Γ A X Y} →
           (Σ Γ A) ⊢ X ⇒ (⟨ proj₁ ⟩ Y) →
           Γ ⊢ `∃ A X ⇒ Y
`∃-elim f .realiser = f .realiser
`∃-elim f .realises γ η α v (a , X-α-v) = f .realises (γ , a) η α v X-α-v

`∃-intro : ∀ {Γ A X Y} →
           Γ ⊢ `∃ A X ⇒ Y →
           (Σ Γ A) ⊢ X ⇒ (⟨ proj₁ ⟩ Y)
`∃-intro f .realiser = f .realiser
`∃-intro f .realises (γ , a) η α v X-α-v = f .realises γ η α v (a , X-α-v)

------------------------------------------------------------------------
-- Part VI : Booleans
`Bool : Bool -Obj
`Bool false .realises α false = 0 ≤D⟨ α , ∅ ⟩
`Bool false .realises α ⋆ = ⊥
`Bool false .realises α (_ , _) = ⊥
`Bool false .realises α true = ⊥
`Bool false .realises α (clo _ _) = ⊥
`Bool true .realises α ⋆ = ⊥
`Bool true .realises α (_ , _) = ⊥
`Bool true .realises α true = 0 ≤D⟨ α , ∅ ⟩
`Bool true .realises α false = ⊥
`Bool true .realises α (clo _ _) = ⊥

K : ∀ {A B : Set} → A → B → A
K a _ = a

`true : ∀ {Γ} → Γ ⊢ I ⇒ (⟨ K true ⟩ `Bool)
`true .realiser .expr _ = true
`true .realiser .potential = acct 1
`true .realiser .potential-ok = `acct
`true .realises γ η α ⋆ r .result = true
`true .realises γ η α ⋆ r .steps = 1
`true .realises γ η α ⋆ r .result-potential = ∅
`true .realises γ η α ⋆ r .evaluation = true
`true .realises γ η α ⋆ r .result-realises = identity
`true .realises γ η α ⋆ r .accounted = acct⊕- ； r

`false : ∀ {Γ} → Γ ⊢ I ⇒ (⟨ K false ⟩ `Bool)
`false .realiser .expr _ = false
`false .realiser .potential = acct 1
`false .realiser .potential-ok = `acct
`false .realises γ η α ⋆ r .result = false
`false .realises γ η α ⋆ r .steps = 1
`false .realises γ η α ⋆ r .result-potential = ∅
`false .realises γ η α ⋆ r .evaluation = false
`false .realises γ η α ⋆ r .result-realises = identity
`false .realises γ η α ⋆ r .accounted = acct⊕- ； r

κ : ∀ {Γ A : Set} → A → Γ → Γ × A
κ a γ = (γ , a)

κ-map : ∀ {Γ : Set}{A B : Set} → (A → B) → Γ × A → Γ × B
κ-map f (γ , a) = (γ , f a)

`cond : ∀ {Γ : Set}{X : Γ -Obj}{Y : (Γ × Bool) -Obj} →
        Γ ⊢ X ⇒ ⟨ κ true ⟩ Y →
        Γ ⊢ X ⇒ ⟨ κ false ⟩ Y →
        (Γ × Bool) ⊢ ⟨ proj₁ ⟩ X ⊗ ⟨ proj₂ ⟩ `Bool ⇒ Y
`cond on-true on-false .realiser .expr n =
  letpair zero then
  cond zero then (seq ` suc zero then on-true .realiser .expr (3 + n))
            else (seq ` suc zero then on-false .realiser .expr (3 + n))
`cond on-true on-false .realiser .potential =
  acct 4 ⊕ on-true .realiser .potential ⊕ on-false .realiser .potential
`cond on-true on-false .realiser .potential-ok =
  (`acct `⊕ on-true .realiser .potential-ok) `⊕ on-false .realiser .potential-ok
`cond on-true on-false .realises (γ , false) η α (vx , false) (α₁ , α₂ , d , vx-r , b-r) =
  is-realisable
  where
    r = on-false .realises γ (η ,- _ ,- _ ,- _) α₁ vx vx-r

    is-realisable : Eval _ _ _ _
    is-realisable .result = r .result
    is-realisable .steps = 4 + r .steps
    is-realisable .result-potential = r .result-potential
    is-realisable .evaluation =
      letpair zero (cond-false zero (seq (access (suc zero)) (r .evaluation)))
    is-realisable .result-realises = r .result-realises
    is-realisable .accounted =
      assoc-inv ； pair (acct⊕- ； term) ； unit' ； pair' d' ； r .accounted
      where
        d' : 0 ≤D⟨ α , α₁ ⟩
        d' = d ； pair' b-r ； unit
`cond on-true on-false .realises (γ , true) η α (vx , true) (α₁ , α₂ , d , vx-r , b-r) =
  is-realisable
  where
    r = on-true .realises γ (η ,- _ ,- _ ,- _) α₁ vx vx-r

    is-realisable : Eval _ _ _ _
    is-realisable .result = r .result
    is-realisable .steps = 4 + r .steps
    is-realisable .result-potential = r .result-potential
    is-realisable .evaluation =
      letpair zero (cond-true zero (seq (access (suc zero)) (r .evaluation)))
    is-realisable .result-realises = r .result-realises
    is-realisable .accounted =
      assoc-inv ； assoc-inv ； acct⊕- ； pair' (pair term ； unit') ； pair' d' ； r .accounted
      where
        d' : 0 ≤D⟨ α , α₁ ⟩
        d' = d ； pair' b-r ； unit

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

------------------------------------------------------------------------
-- Part VIII : Finitary (indexed?) datatypes, with matching but no
-- recursion

data Code : Set where
  _`+_   : Code → Code → Code
  `⊤     : Code
  `Rec×_ : Code → Code
