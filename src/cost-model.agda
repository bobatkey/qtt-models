module cost-model where

open import Data.Nat hiding (_∸_)
open import Data.Nat.Properties
open import Data.Fin hiding (_+_; _≤_; raise)
open import Data.Product hiding (swap)
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Bool hiding (_≤_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; subst; sym)
open Eq.≡-Reasoning -- using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; con; _:+_; _:=_)

open import MachineModel
open import ResourceMonoid

-- Conjecture: if we don't have fancy exponentials, then all the terms
-- used in the realisers are linear. Then we only need to make sure
-- that the iterators we use properly count the number of recursive
-- steps they take. The total number of steps will then be some
-- globally fixed multiple of the number of recursive steps.
--
-- except that this needs to be uniform in the size of the actual
-- input!!!

-- need linear λ-calculus + natural numbers + other data

--  M ::= x | λ M | M·N | (M,N) | letp M N | let M N | * | n | nrec M N

-- theorem: for a term of type ◇(n) → I(n) → O, it evaluates to a
-- closed value in time proportional to 'n' steps. Is this the right
-- theorem? no

-- Idea
-- 1. Measure the size of linear terms, counting first order data as '1'
-- 2. Normal β-reduction makes them smaller, by removing an elimination term, except for nat-recursion

-- 3. Given any reduction with a fixed number of unfolding steps, the
-- total number is bounded by the number of eliminators in the term,
-- multiplied by the unfolding steps.
--
-- 4. This is proved by induction on the number of unfolding steps,
-- where the total size of the term goes down each time.
--
-- 5. Relies on the realising term being linear, or at least counting
-- the number of uses of each variable accurately.


------------------------------------------------------------------------------
-- this is essentially a ℕ∪{-∞}-enriched category that is also
-- symmetric monoidal.
--
-- the idea is that k ≤D⟨ α , β ⟩ if going from α to β yields k amount
-- of resource for computation.
--
-- could we have any quantitative model of computation with an indexed
-- evaluation relation: _=[_]=>_ : 𝒜 → ℚ → 𝒜 → Set (could be probability?)
--
-- this would connect with the ideas of "Quantitative Foundations for
-- Resource Theories" by Dan Marsden and Maaike Zwart
-- (https://doi.org/10.4230/LIPIcs.CSL.2018.32)
--
-- and elements B, C, I such that:
-- - (B · x · y · z) =[ 1 ]=> x · (y · z)
-- - (I · x)         =[ 1 ]=> x
-- - (C · x · y · z) =[ 1 ]=> x · z · y
--
-- for some "unit cost" 1.
--
-- then we could presumably build a symmetric monoidal category? as
-- long as we have an “acct” morphism in the resource category.
--
-- for the probability version we could have a constant F (for Flip),
-- with:
--
--   F · x · y =[ 0.5 ]=> x
--   F · x · y =[ 0.5 ]=> y
--
-- Presumably this would realise some finite distribution monad? So
-- what? the equational theory of programs would still be the same as
-- the original one.
--
-- what if we used M-indexed PERs? Then we wouldn't have to state up
-- front what the set theoretic functions were?
--
-- I suppose the abstract behaviour here is that the computational
-- model is also a ℚ-enriched category, yielding a sort of melding
-- operation?
--
-- Given a pair of ℚ-enriched categories, one of which is symmetric
-- monoidal, and the other is an ordered BCI algebra, then the
-- category of PERs yields a symmetric monoidal category? If we have
-- booleans, then we also have the additives.
--
-- instances? probability? distances? this is a kind of abstract
-- amortised resource analysis. What do we need to abstractly do
-- iteration?
--
-- It : 𝒜 × 𝒜 → 𝒜
-- Z, S : 𝒜
-- It(z, s) · Z       =[ 1 ]=> z
-- It(z, s) · (S · x) =[ 1 ]=> s · (It(z, s) · x)   -- why not a paramorphism?
--
-- What structure on the resulting category do we get?


-- module sub-monoids where

--   open sub-monoid

--   entire : ∀ M → sub-monoid M
--   entire M .member α = ⊤
--   entire M ._`⊕_ tt tt = tt
--   entire M .`∅ = tt
--   entire M .`acct = tt

-- natural numbers form a resource monoid that essentially yields a
-- direct connection between sizes and number of steps.
module nat-rm where

  open rmonoid

  ℕ-rm : rmonoid
  ∣ ℕ-rm ∣ = ℕ
  ℕ-rm .∅ = 0
  ℕ-rm ._⊕_ = _+_
  ℕ-rm ._≤D⟨_,_⟩ k m n = k + n ≤ m
  ℕ-rm .acct k = k
  ℕ-rm .identity = ≤-refl
  ℕ-rm ._⟫_ {k₁} k₁+n≤m k₂+l≤n = ≤-trans (≤-trans (≤-reflexive (+-assoc k₁ _ _)) (+-monoʳ-≤ k₁ k₂+l≤n)) k₁+n≤m
  ℕ-rm .weaken k₁+n≤m k₂≤k₁ = ≤-trans (+-monoˡ-≤ _ k₂≤k₁) k₁+n≤m
  ℕ-rm .pair {k}{m}{n}{l} k+n≤m = ≤-trans (≤-reflexive (sym (+-assoc k n l))) (+-monoˡ-≤ _ k+n≤m)
  ℕ-rm .symmetry {m}{n} = ≤-reflexive (+-comm n m)
  ℕ-rm .unit = ≤-reflexive (sym (+-identityʳ _))
  ℕ-rm .unit-inv = ≤-reflexive (+-identityʳ _)
  ℕ-rm .assoc {m}{n}{l}= ≤-reflexive (+-assoc m n l)
  ℕ-rm .assoc-inv {m}{n}{l} = ≤-reflexive (sym (+-assoc m n l))
  ℕ-rm .term = z≤n
  ℕ-rm .account = ≤-reflexive (+-identityʳ _)

------------------------------------------------------------------------------

module resource-category (M : rmonoid) (M₀ : sub-monoid M) where

  open rmonoid using (∣_∣)
  open rmonoid M hiding (∣_∣)
  open sub-monoid M₀ renaming (member to mor-potential)

  record obj : Set₁ where
    field
      ∥_∥ : Set
      realises : ∣ M ∣ → val → ∥_∥  → Set
  open obj public

  record Eval {n} (Y : obj) (e : exp n) (α : ∣ M ∣) (η : env n) (y : ∥ Y ∥) : Set where
    field
      result           : val
      steps            : ℕ
      result-potential : ∣ M ∣
      evaluation       : e , η ⇓[ steps ] result
      result-realises  : Y .realises result-potential result y
      accounted        : steps ≤D⟨ α , result-potential ⟩
  open Eval public

  record _==>_ (X Y : obj) : Set where
    field
      mor : ∥ X ∥ → ∥ Y ∥
      expr : ∀ n → exp (suc n)
      potential : ∣ M ∣
      potential-ok : mor-potential potential
      realisable : ∀ {n} (η : env n) (α : ∣ M ∣) v x → X .realises α v x → Eval Y (expr n) (potential ⊕ α) (η ,- v) (mor x)
  open _==>_ public

  -- FIXME: two morphisms are equal if they have (extensionally) equal
  -- underlying functions.

  id : ∀{X} → X ==> X
  id .mor x = x
  id .expr _ = ` zero
  id .potential = acct 1
  id .potential-ok = `acct
  id .realisable η α v x X-α-v-x .result = v
  id .realisable η α v x X-α-v-x .steps = 1
  id .realisable η α v x X-α-v-x .result-potential = α
  id .realisable η α v x X-α-v-x .evaluation = access zero
  id .realisable η α v x X-α-v-x .result-realises = X-α-v-x
  id .realisable η α v x X-α-v-x .accounted = acct⊕-

  _∘_ : ∀{X Y Z} → (Y ==> Z) → (X ==> Y) → (X ==> Z)
  (f ∘ g) .mor x     = f .mor (g .mor x)
  (f ∘ g) .expr    n = seq (g .expr n) then f .expr (suc n)
  (f ∘ g) .potential = acct 1 ⊕ f .potential ⊕ g .potential
  (f ∘ g) .potential-ok = (`acct `⊕ f .potential-ok) `⊕ g .potential-ok
  (f ∘ g) .realisable η α v x X-α-v-x = is-realisable
    where
      gr = g .realisable η α v x X-α-v-x
      fr = f .realisable (η ,- v) (gr .result-potential) (gr .result) (g .mor x) (gr .result-realises)

      is-realisable : Eval _ _ _ _ (f .mor (g .mor x))
      is-realisable .result = fr .result
      is-realisable .steps = gr .steps + 1 + fr .steps
      is-realisable .result-potential = fr .result-potential
      is-realisable .evaluation = seq (gr .evaluation) (fr .evaluation)
      is-realisable .result-realises = fr .result-realises
      is-realisable .accounted =
         assoc-inv ⟫ assoc-inv ⟫ pair' (pair' (gr .accounted)) ⟫ acct⊕- ⟫ fr .accounted

  ------------------------------------------------------------------------------
  -- Terminal object

  I : obj
  ∥ I ∥ = ⊤
  I .realises α ⋆         tt = 0 ≤D⟨ α , ∅ ⟩
  I .realises α (_ , _)   tt = ⊥
  I .realises α (clo _ _) tt = ⊥
  I .realises α true      tt = ⊥
  I .realises α false     tt = ⊥

  -- only terminal if we always have 0 ≤D⟨ α , ∅ ⟩
  terminal : ∀ X → X ==> I
  terminal X .mor _ = tt
  terminal X .expr _ = ⋆
  terminal X .potential = acct 1
  terminal X .potential-ok = `acct
  terminal X .realisable η α _ _ _ = is-realisable
    where
      is-realisable : Eval _ _ _ _ _
      is-realisable .result = ⋆
      is-realisable .steps = 1
      is-realisable .result-potential = α
      is-realisable .evaluation = mkunit
      is-realisable .result-realises = term
      is-realisable .accounted = acct⊕-

  ------------------------------------------------------------------------------
  -- Symmetric monoidal closed

  _⊗_ : obj → obj → obj
  ∥ X ⊗ Y ∥ = ∥ X ∥ × ∥ Y ∥
  (X ⊗ Y) .realises α (v₁ , v₂) (x , y) =
     Σ[ α₁ ∈ ∣ M ∣ ]
     Σ[ α₂ ∈ ∣ M ∣ ]
     (0 ≤D⟨ α , α₁ ⊕ α₂ ⟩ × X .realises α₁ v₁ x × Y .realises α₂ v₂ y)
  (X ⊗ Y) .realises α ⋆ _ = ⊥
  (X ⊗ Y) .realises α (clo _ _) _ = ⊥
  (X ⊗ Y) .realises α true _ = ⊥
  (X ⊗ Y) .realises α false _ = ⊥

  _⊸_ : obj → obj → obj
  ∥ X ⊸ Y ∥ = ∥ X ∥ → ∥ Y ∥
  (X ⊸ Y) .realises α (clo E η) f = (x : ∥ X ∥) → (α' : ∣ M ∣) → (v w : val) → X .realises α' v x → Eval Y E (α ⊕ α') (η ,- w ,- v) (f x)
  (X ⊸ Y) .realises α ⋆ _ = ⊥
  (X ⊸ Y) .realises α (_ , _) _ = ⊥
  (X ⊸ Y) .realises α true _ = ⊥
  (X ⊸ Y) .realises α false _ = ⊥

  swap : ∀ {X Y} → (X ⊗ Y) ==> (Y ⊗ X)
  swap .mor (x , y) = (y , x)
  swap .expr _ = letpair zero then (zero , suc zero)
  swap .potential = acct 2
  swap .potential-ok = `acct
  swap .realisable η α (v₁ , v₂) (x , y) (α₁ , α₂ , d , X-α₁-v₁-x , Y-α₂-v₂-y) = is-realisable
    where
      is-realisable : Eval _ _ _ _ _
      is-realisable .result = v₂ , v₁
      is-realisable .steps = 2
      is-realisable .result-potential = α
      is-realisable .evaluation = letpair zero (mkpair zero (suc zero))
      is-realisable .result-realises = α₂ , α₁ , d ⟫ symmetry , Y-α₂-v₂-y , X-α₁-v₁-x
      is-realisable .accounted = acct⊕-

  assoc-m : ∀ {X Y Z} → (X ⊗ (Y ⊗ Z)) ==> ((X ⊗ Y) ⊗ Z)
  assoc-m .mor (x , (y , z)) = ((x , y) , z)
  assoc-m .expr _ = letpair zero then
                    letpair zero then
                    seq (suc (suc (suc zero)) , suc zero) then
                    (zero , suc zero)
  assoc-m .potential = acct 5
  assoc-m .potential-ok = `acct
  assoc-m .realisable η α (vx , (vy , vz)) (x , (y , z)) (α₁ , α₂ , d , vx-r , α₃ , α₄ , d' , vy-r , vz-r) = is-realisable
    where
     is-realisable : Eval _ _ _ _ _
     is-realisable .result = (vx , vy) , vz
     is-realisable .steps = 5
     is-realisable .result-potential = α
     is-realisable .evaluation = letpair zero (letpair zero (seq (mkpair (suc (suc (suc zero))) (suc zero)) (mkpair zero (suc zero))))
     is-realisable .result-realises = α₁ ⊕ α₃ , α₄ , (d ⟫ pair' d' ⟫ assoc) , (α₁ , α₃ , identity , vx-r , vy-r) , vz-r
     is-realisable .accounted = acct⊕-

  assoc-inv-m : ∀ {X Y Z} → ((X ⊗ Y) ⊗ Z) ==> (X ⊗ (Y ⊗ Z))
  assoc-inv-m .mor ((x , y) , z) = (x , (y , z))
  assoc-inv-m .expr _ = letpair zero then
                        letpair suc zero then
                        seq (zero , suc (suc zero)) then
                        (suc (suc zero) , zero)
  assoc-inv-m .potential = acct 5
  assoc-inv-m .potential-ok = `acct
  assoc-inv-m .realisable η α ((vx , vy) , vz) ((x , y) , z) (α₁ , α₂ , d , (α₃ , α₄ , d' , vx-r , vy-r) , vz-r) = is-realisable
    where
     is-realisable : Eval _ _ _ _ _
     is-realisable .result = vx , (vy , vz)
     is-realisable .steps = 5
     is-realisable .result-potential = α
     is-realisable .evaluation = letpair zero (letpair (suc zero) (seq (mkpair zero (suc (suc zero))) (mkpair (suc (suc zero)) zero)))
     is-realisable .result-realises = α₃ , α₄ ⊕ α₂ , (d ⟫ pair d' ⟫ assoc-inv) , vx-r , α₄ , α₂ , identity , vy-r , vz-r
     is-realisable .accounted = acct⊕-

  unit-m : ∀ {X} → (X ⊗ I) ==> X
  unit-m .mor (x , tt) = x
  unit-m .expr _ = letpair zero then ` (suc zero)
  unit-m .potential = acct 2
  unit-m .potential-ok = `acct
  unit-m .realisable η α (vx , ⋆) (x , tt) (α₁ , α₂ , d , vx-r , ⋆-r) = is-realisable
    where
      is-realisable : Eval _ _ _ _ _
      is-realisable .result = vx
      is-realisable .steps = 2
      is-realisable .result-potential = α₁
      is-realisable .evaluation = letpair zero (access (suc zero))
      is-realisable .result-realises = vx-r
      is-realisable .accounted = acct⊕- ⟫ d ⟫ pair' ⋆-r ⟫ unit

  unit-inv-m : ∀ {X} → X ==> (X ⊗ I)
  unit-inv-m .mor x = (x , tt)
  unit-inv-m .expr _ = seq ⋆ then (suc zero , zero)
  unit-inv-m .potential = acct 3
  unit-inv-m .potential-ok = `acct
  unit-inv-m .realisable η α vx x vx-r = is-realisable
    where
      is-realisable : Eval _ _ _ _ _
      is-realisable .result = (vx , ⋆)
      is-realisable .steps = 3
      is-realisable .result-potential = α
      is-realisable .evaluation = seq mkunit (mkpair (suc zero) zero)
      is-realisable .result-realises = α , ∅ , unit-inv , vx-r , identity
      is-realisable .accounted = acct⊕-

  _⊗m_ : ∀ {X₁ X₂ Y₁ Y₂} →
         (f : X₁ ==> Y₁)
         (g : X₂ ==> Y₂) →
         (X₁ ⊗ X₂) ==> (Y₁ ⊗ Y₂)
  (f ⊗m g) .mor (x₁ , x₂) = f .mor x₁ , g .mor x₂
  (f ⊗m g) .expr n = letpair zero then
                     seq g .expr (2 + n) then
                     seq ` (suc (suc zero)) then
                     seq f .expr (4 + n) then
                     (zero , suc (suc zero))
  (f ⊗m g) .potential = acct 6 ⊕ (f .potential ⊕ g .potential)
  (f ⊗m g) .potential-ok = `acct `⊕ (f .potential-ok `⊕ g .potential-ok)
  (f ⊗m g) .realisable η α (v₁ , v₂) (x₁ , x₂) (α₁ , α₂ , d , X₁-α₁-v₁-x₁ , X₂-α₂-v₂-x₂) = is-realisable
    where
      r₁ = f .realisable (η ,- _ ,- _ ,- _ ,- _) α₁ v₁ x₁ X₁-α₁-v₁-x₁
      r₂ = g .realisable (η ,- _ ,- _) α₂ v₂ x₂ X₂-α₂-v₂-x₂

      is-realisable : Eval _ _ _ _ _
      is-realisable .result = r₁ .result , r₂ .result
      is-realisable .steps = 1 + (r₂ .steps + 1) + (2 + r₁ .steps + 1 + 1)
      is-realisable .result-potential = r₁ .result-potential ⊕ r₂ .result-potential
      is-realisable .evaluation = letpair zero (seq (r₂ .evaluation) (seq (access (suc (suc zero))) (seq (r₁ .evaluation) (mkpair zero (suc (suc zero))))))
      is-realisable .result-realises =
        r₁ .result-potential , r₂ .result-potential , identity , r₁ .result-realises , r₂ .result-realises
      is-realisable .accounted =
        weaken (assoc-inv ⟫ acct⊕- ⟫ pair' (d ⟫ symmetry) ⟫ assoc-inv ⟫ pair' (assoc ⟫ symmetry) ⟫ assoc ⟫ pair' (r₂ .accounted) ⟫ pair (r₁ .accounted))
               (≤-reflexive (begin
                               1 + (r₂ .steps + 1) + (2 + r₁ .steps + 1 + 1)
                             ≡⟨ +-*-Solver.solve 2
                                   (λ x y →
                                         con 1 :+ (x :+ con 1) :+ (con 2 :+ y :+ con 1 :+ con 1)
                                         := con 6 :+ x :+ y) refl (r₂ .steps) (r₁ .steps) ⟩
                               6 + r₂ .steps + r₁ .steps
                             ∎))

  Λ : ∀ {X Y Z} → (X ⊗ Y) ==> Z → X ==> (Y ⊸ Z)
  Λ f .mor x = λ y → f .mor (x , y)
  Λ f .expr n = ƛ (seq (suc (suc zero) , zero) then f .expr (3 + n))
  Λ f .potential = acct 1 ⊕ (acct 2 ⊕ f .potential)
  Λ f .potential-ok = `acct `⊕ (`acct `⊕ f .potential-ok)
  Λ f .realisable {n₀} η α vx x vx-r = is-realisable
    where
      is-realisable : Eval _ _ _ _ _
      is-realisable .result = clo (seq (suc (suc zero) , zero) then f .expr (3 + n₀)) (η ,- vx)
      is-realisable .steps = 1
      is-realisable .result-potential = (acct 2 ⊕ f .potential) ⊕ α
      is-realisable .evaluation = lam
      is-realisable .result-realises y α' vy vw vy-r = is-realisable'
        where
          r = f .realisable (η ,- vx ,- vw ,- vy) (α ⊕ α') (vx , vy) (x , y) (α , α' , identity , vx-r , vy-r)

          is-realisable' : Eval _ _ _ _ _
          is-realisable' .result = r .result
          is-realisable' .steps = 2 + r .steps
          is-realisable' .result-potential = r .result-potential
          is-realisable' .evaluation = seq (mkpair (suc (suc zero)) zero) (r .evaluation)
          is-realisable' .result-realises = r .result-realises
          is-realisable' .accounted = assoc-inv ⟫ assoc-inv ⟫ acct⊕- ⟫ r .accounted
      is-realisable .accounted = assoc-inv ⟫ acct⊕-

  apply : ∀ {X Y} → ((X ⊸ Y) ⊗ X) ==> Y
  apply .mor (f , x) = f x
  apply .expr _ = letpair zero then (suc zero · zero)
  apply .potential = acct 2
  apply .potential-ok = `acct
  apply .realisable η₀ α (clo E η , vx) (f , x) (α₁ , α₂ , d , vf-r , vx-r) = is-realisable
    where
      y-r = vf-r x α₂ vx (clo E η) vx-r

      is-realisable : Eval _ _ _ _ _
      is-realisable .result = y-r .result
      is-realisable .steps = 2 + y-r .steps
      is-realisable .result-potential = y-r .result-potential
      is-realisable .evaluation = letpair zero (app (suc zero) zero (y-r .evaluation))
      is-realisable .result-realises = y-r .result-realises
      is-realisable .accounted = acct⊕- ⟫ d ⟫ y-r .accounted

  ------------------------------------------------------------------------------
  _&_ : obj → obj → obj
  ∥ X & Y ∥ = ∥ X ∥ × ∥ Y ∥
  (X & Y) .realises α ⋆ _ = ⊥
  (X & Y) .realises α (_ , _) _ = ⊥
  (X & Y) .realises α true _ = ⊥
  (X & Y) .realises α false _ = ⊥
  (X & Y) .realises α (clo E η) (x , y) = ∀ v →
      Eval X E α (η ,- v ,- false) x × Eval Y E α (η ,- v ,- true) y

  &-proj₁ : ∀ {X Y} → (X & Y) ==> X
  &-proj₁ .mor x = x .proj₁
  &-proj₁ .expr _ = seq false then (suc zero · zero)
  &-proj₁ .potential = acct 3
  &-proj₁ .potential-ok = `acct
  &-proj₁ .realisable η α (clo E η') (x , y) E-xy = is-realisable
    where
      v-x = E-xy (clo E η') .proj₁

      is-realisable : Eval _ _ _ _ _
      is-realisable .result = v-x .result
      is-realisable .steps = 3 + v-x .steps
      is-realisable .result-potential = v-x .result-potential
      is-realisable .evaluation = seq false (app (suc zero) zero (v-x .evaluation))
      is-realisable .result-realises = v-x .result-realises
      is-realisable .accounted = acct⊕- ⟫ v-x .accounted

  &-proj₂ : ∀ {X Y} → (X & Y) ==> Y
  &-proj₂ .mor x = x .proj₂
  &-proj₂ .expr _ = seq true then (suc zero · zero)
  &-proj₂ .potential = acct 3
  &-proj₂ .potential-ok = `acct
  &-proj₂ .realisable η α (clo E η') (x , y) E-xy = is-realisable
    where
      v-y = E-xy (clo E η') .proj₂

      is-realisable : Eval _ _ _ _ _
      is-realisable .result = v-y .result
      is-realisable .steps = 3 + v-y .steps
      is-realisable .result-potential = v-y .result-potential
      is-realisable .evaluation = seq true (app (suc zero) zero (v-y .evaluation))
      is-realisable .result-realises = v-y .result-realises
      is-realisable .accounted = acct⊕- ⟫ v-y .accounted

  pair-expr : (∀ n → exp (suc n)) → (∀ n → exp (suc n)) → ∀ n → exp (3 + n)
  pair-expr f g n =
    cond zero then (seq ` (suc (suc zero)) then g _)
              else (seq ` (suc (suc zero)) then f _)

  &-pair : ∀ {X Y Z} → (X ==> Y) → (X ==> Z) → (X ==> (Y & Z))
  &-pair f g .mor x = f .mor x , g .mor x
  &-pair f g .expr n = ƛ (pair-expr (f .expr) (g .expr) n)
  &-pair f g .potential = acct 1 ⊕ (acct 3 ⊕ (f .potential ⊕ g .potential))
  &-pair f g .potential-ok = `acct `⊕ (`acct `⊕ (f .potential-ok `⊕ (g .potential-ok)))
  &-pair f g .realisable {n} η α v x v-x = is-realisable
    where
      f-r : (v' : val) → Eval _ _ _ _ _
      f-r v' = f .realisable (η ,- v ,- v' ,- false) α v x v-x

      g-r : (v' : val) → Eval _ _ _ _ _
      g-r v' = g .realisable (η ,- v ,- v' ,- true) α v x v-x

      is-realisable : Eval _ _ _ _ _
      is-realisable .result = clo (pair-expr (f .expr) (g .expr) n) (η ,- v)
      is-realisable .steps = 1
      is-realisable .result-potential = acct 3 ⊕ ((f .potential ⊕ g .potential) ⊕ α)
      is-realisable .evaluation = lam
      is-realisable .result-realises v' .proj₁ .result = f-r v' .result
      is-realisable .result-realises v' .proj₁ .steps = 3 + f-r v' .steps
      is-realisable .result-realises v' .proj₁ .result-potential = f-r v' .result-potential
      is-realisable .result-realises v' .proj₁ .evaluation = cond-false zero (seq (access (suc (suc zero))) (f-r v' .evaluation))
      is-realisable .result-realises v' .proj₁ .result-realises = f-r v' .result-realises
      is-realisable .result-realises v' .proj₁ .accounted = acct⊕- ⟫ pair fst ⟫ f-r v' .accounted
      is-realisable .result-realises v' .proj₂ .result = g-r v' .result
      is-realisable .result-realises v' .proj₂ .steps = 3 + g-r v' .steps
      is-realisable .result-realises v' .proj₂ .result-potential = g-r v' .result-potential
      is-realisable .result-realises v' .proj₂ .evaluation = cond-true zero (seq (access (suc (suc zero))) (g-r v' .evaluation))
      is-realisable .result-realises v' .proj₂ .result-realises = g-r v' .result-realises
      is-realisable .result-realises v' .proj₂ .accounted = acct⊕- ⟫ pair (snd _ _) ⟫ g-r v' .accounted
      is-realisable .accounted = assoc-inv ⟫ acct⊕- ⟫ assoc-inv

  ------------------------------------------------------------------------------
  -- FIXME: a ℕ-indexed exponential, that occupies n resources for a single thing
  ![_] : ℕ → obj → obj
  ∥ ![ n ] X ∥ = ∥ X ∥
  ![ n ] X .realises α v x = Σ[ β ∈ ∣ M ∣ ] (0 ≤D⟨ α , repeat n β ⟩ × X .realises β v x )

  -- should have:
  --    ![ 1 ] X          ==> X
  --    ![ m ] (![ n ] X) =~ ![ m * n ] X
  --    ![ m + n ] X      ==> (![ m ] X ⊗ ![ n ] X)
  --    ![ 0 ] X          ==> I -- always exists anyway
  --
  -- extensionaly realised by identity, identity, duplication, discarding

  derelict : ∀ {X} → ![ 1 ] X ==> X
  derelict .mor x = x
  derelict .expr _ = ` zero
  derelict .potential = acct 1
  derelict .potential-ok = `acct
  derelict .realisable η α v x (β , α-β , v-x) = is-realisable
    where
      is-realisable : Eval _ _ _ _ _
      is-realisable .result = v
      is-realisable .steps = 1
      is-realisable .result-potential = β
      is-realisable .evaluation = access zero
      is-realisable .result-realises = v-x
      is-realisable .accounted = pair account ⟫ unit' ⟫ α-β ⟫ unit



  -- two versions: one that implements by storing the realising value
  -- 'n' times, and one that stores it once. The costs are all bounded
  -- by the sizes of the types.

  ------------------------------------------------------------------------------
  -- Booleans, and non-iterable data structures

  -- FIXME: also do coproducts

  `bool : obj
  ∥ `bool ∥ = Bool
  `bool .realises α true  true  = 0 ≤D⟨ α , ∅ ⟩
  `bool .realises α false false = 0 ≤D⟨ α , ∅ ⟩
  `bool .realises α true  false = ⊥
  `bool .realises α false true  = ⊥
  `bool .realises α (_ , _)   _ = ⊥
  `bool .realises α ⋆         _ = ⊥
  `bool .realises α (clo _ _) _ = ⊥

  `true : I ==> `bool
  `true .mor tt = true
  `true .expr _ = true
  `true .potential = acct 1
  `true .potential-ok = `acct
  `true .realisable η α ⋆ tt v⋆-r = is-realisable
    where
      is-realisable : Eval _ _ _ _ _
      is-realisable .result = true
      is-realisable .steps = 1
      is-realisable .result-potential = ∅
      is-realisable .evaluation = true
      is-realisable .result-realises = identity
      is-realisable .accounted = acct⊕- ⟫ v⋆-r

  `false : I ==> `bool
  `false .mor tt = false
  `false .expr _ = false
  `false .potential = acct 1
  `false .potential-ok = `acct
  `false .realisable η α ⋆ tt v⋆-r = is-realisable
    where
      is-realisable : Eval _ _ _ _ _
      is-realisable .result = false
      is-realisable .steps = 1
      is-realisable .result-potential = ∅
      is-realisable .evaluation = false
      is-realisable .result-realises = identity
      is-realisable .accounted = acct⊕- ⟫ v⋆-r

  `cond : ∀ {X Y : obj} →
          (X ==> Y) →
          (X ==> Y) →
          (`bool ⊗ X) ==> Y
  `cond t f .mor (true  , y) = t .mor y
  `cond t f .mor (false , y) = f .mor y
  `cond t f .expr n = letpair zero then cond suc zero then t .expr (2 + n) else f .expr (2 + n)
  `cond t f .potential = acct 2 ⊕ t .potential ⊕ f .potential
  `cond t f .potential-ok = (`acct `⊕ t .potential-ok) `⊕ f .potential-ok
  `cond t f .realisable η α (true , vx)  (true , x)  (α₁ , α₂ , d , b-r , vx-r) = is-realisable
    where
      r = t .realisable (η ,- _ ,- _) α₂ vx x vx-r

      is-realisable : Eval _ _ _ _ _
      is-realisable .result = r .result
      is-realisable .steps = 2 + r .steps
      is-realisable .result-potential = r .result-potential
      is-realisable .evaluation = letpair zero (cond-true (suc zero) (r .evaluation))
      is-realisable .result-realises = r .result-realises
      is-realisable .accounted =
          assoc-inv ⟫ assoc-inv ⟫ acct⊕- ⟫ pair' (pair term ⟫ unit') ⟫ pair' d' ⟫ r .accounted
        where
          d' : 0 ≤D⟨ α , α₂ ⟩
          d' = d ⟫ pair b-r ⟫ unit'
  `cond t f .realisable η α (false , vx) (false , x) (α₁ , α₂ , d , b-r , vx-r) = is-realisable
    where
      r = f .realisable (η ,- _ ,- _) α₂ vx x vx-r

      is-realisable : Eval _ _ _ _ _
      is-realisable .result = r .result
      is-realisable .steps = 2 + r .steps
      is-realisable .result-potential = r .result-potential
      is-realisable .evaluation = letpair zero (cond-false (suc zero) (r .evaluation))
      is-realisable .result-realises = r .result-realises
      is-realisable .accounted =
          assoc-inv ⟫ pair (acct⊕- ⟫ term) ⟫ unit' ⟫ pair' d' ⟫ r .accounted
        where
          d' : 0 ≤D⟨ α , α₂ ⟩
          d' = d ⟫ pair b-r ⟫ unit'

{-where
      is-realisable : Eval _ _ _ _ _
      is-realisable .result = ?
      is-realisable .steps = ?
      is-realisable .result-potential = ?
      is-realisable .evaluation = ?
      is-realisable .result-realises = ?
      is-realisable .accounted = ?
-}
------------------------------------------------------------------------------
-- Natural numbers with a recursion combinator

-- Three variants (all with the same realiser)
--   1. LFPL one
--   2. 'SAL'one  (basically the same argument)
--   3. explicit one (slightly different type)

-- SAL:
-- [ ] resource monoid is pairs of numbers and ℕ-coeff polynomials
-- [ ] extend the core language with recursion
-- [ ] numbers are realised by α , v |= n ⇔ v = v(n) ∧ 0 ≤D⟨ α , (n , 0) ⟩
-- [ ]

-- LFPL: [ ] need to account for the lack of diamonds in realisers of
-- morphisms in the definition of category above. Need a predicate on
-- elements of the resource monoid that is closed under ⊕ and ∅ and
-- acct. For the polynomial resource monoids below, we need a
-- predicate that makes the chosen operation on sizes idempotent (so
-- that scaling works)

-- symmetric monoidal category...?
record size-algebra : Set where
  field
    _⊎_       : ℕ → ℕ → ℕ
    mono      : ∀ {x y} z → x ≤ y → (x ⊎ z) ≤ (y ⊎ z)
    assoc     : ∀ x y z → (x ⊎ y) ⊎ z ≡ x ⊎ (y ⊎ z)
    comm      : ∀ x y   → x ⊎ y ≡ y ⊎ x
    unit      : ∀ x     → x ⊎ 0 ≡ x
    bounded   : ∀ x y {z} → x ⊎ y ≤ z → x ≤ z

  interchange : ∀ a b c d → (a ⊎ b) ⊎ (c ⊎ d) ≡ (a ⊎ c) ⊎ (b ⊎ d)
  interchange a b c d =
    begin
      (a ⊎ b) ⊎ (c ⊎ d)
    ≡⟨ assoc a b (c ⊎ d) ⟩
      a ⊎ (b ⊎ (c ⊎ d))
    ≡⟨ cong (λ □ → a ⊎ □) (sym (assoc b c d)) ⟩
      a ⊎ ((b ⊎ c) ⊎ d)
    ≡⟨ cong (λ □ → a ⊎ (□ ⊎ d)) (comm b c) ⟩
      a ⊎ ((c ⊎ b) ⊎ d)
    ≡⟨ cong (λ □ → a ⊎ □) (assoc c b d) ⟩
      a ⊎ (c ⊎ (b ⊎ d))
    ≡⟨ sym (assoc a c (b ⊎ d)) ⟩
      (a ⊎ c) ⊎ (b ⊎ d)
    ∎

+-size-algebra : size-algebra
+-size-algebra .size-algebra._⊎_ = _+_
+-size-algebra .size-algebra.mono z x≤y = +-mono-≤ x≤y ≤-refl
+-size-algebra .size-algebra.assoc x y z = +-assoc x y z
+-size-algebra .size-algebra.comm x y = +-comm x y
+-size-algebra .size-algebra.unit x = +-identityʳ x
+-size-algebra .size-algebra.bounded x y x⊎y≤z = m+n≤o⇒m≤o x x⊎y≤z

⊔-size-algebra : size-algebra
⊔-size-algebra .size-algebra._⊎_ = _⊔_
⊔-size-algebra .size-algebra.mono z x≤y = ⊔-mono-≤ x≤y ≤-refl
⊔-size-algebra .size-algebra.assoc x y z = ⊔-assoc x y z
⊔-size-algebra .size-algebra.comm x y = ⊔-comm x y
⊔-size-algebra .size-algebra.unit x = ⊔-identityʳ x
⊔-size-algebra .size-algebra.bounded x y x⊎y≤z = m⊔n≤o⇒m≤o x y x⊎y≤z


module poly-monoid (S : size-algebra) where

  open import nat-poly hiding (unit; assoc; comm; scale)

  module monoid-defn where
    open rmonoid
    open size-algebra S

    -- this works for both _+_ and _⊔_: only needs the operation to be a pre-ordered commutative monoid s.t. m·n≤x → m≤x
    -- also, the class of functions only needs to be closed under constants, 0 and +
    -- and sizes needn't be natural numbers?? Could be trees?
    poly-monoid : rmonoid
    ∣ poly-monoid ∣ = ℕ × ℕ-poly
    poly-monoid .∅ = 0 , 0-poly
    poly-monoid ._⊕_ (m , p) (n , q) = m ⊎ n , p +-poly q
    poly-monoid ._≤D⟨_,_⟩ k (m , p) (n , q) =
       (n ≤ m) × ((x : ℕ) → m ≤ x → k + ⟪ q ⟫ x ≤ ⟪ p ⟫ x)
    poly-monoid .acct n = 0 , const-poly n
    poly-monoid .identity {n , p} =
       ≤-refl , λ x n≤x → ≤-refl
    poly-monoid ._⟫_ {k₁}{k₂}{m , p}{n , q}{l , r} (n≤m , ϕ₁) (l≤n , ϕ₂) =
       ≤-trans l≤n n≤m ,
       λ x m≤x → ≤-trans (≤-reflexive (+-assoc k₁ k₂ (⟪ r ⟫ x)))
                 (≤-trans (+-monoʳ-≤ k₁ (ϕ₂ x (≤-trans n≤m m≤x)))
                          (ϕ₁ x m≤x))
    poly-monoid .weaken {k₁}{k₂}{m , p}{n , q} (n≤m , ϕ) k₂≤k₁ =
       n≤m ,
       λ x m≤x → ≤-trans (+-monoˡ-≤ (⟪ q ⟫ x) k₂≤k₁) (ϕ x m≤x)
    poly-monoid .pair {k}{m , p}{n , q}{l , r} (n≤m , ϕ) =
       mono l n≤m ,
       λ x m⊔l≤x →  ≤-trans (≤-reflexive (cong (λ □ → k + □) (eval-+ q r x)))
                    (≤-trans (≤-reflexive (sym (+-assoc k (⟪ q ⟫ x) (⟪ r ⟫ x))))
                    (≤-trans (+-monoˡ-≤ (⟪ r ⟫ x) (ϕ x (bounded m l m⊔l≤x)))
                             (≤-reflexive (sym (eval-+ p r x)))))
    poly-monoid .symmetry {m , p}{n , q} =
       ≤-reflexive (comm n m) ,
       λ x _ → ≤-reflexive (nat-poly.comm q p x)
    poly-monoid .unit {m , p} =
      ≤-reflexive (sym (size-algebra.unit S m)) ,
      λ x _ → ≤-reflexive (nat-poly.unit p x)
    poly-monoid .unit-inv {m , p} =
      ≤-reflexive (size-algebra.unit S m) ,
      λ x _ → ≤-reflexive (sym (nat-poly.unit p x))
    poly-monoid .assoc {m , p}{n , q}{l , r} =
      ≤-reflexive (size-algebra.assoc S m n l) ,
      λ x _ → ≤-reflexive (nat-poly.assoc p q r x)
    poly-monoid .assoc-inv {m , p}{n , q}{l , r} =
      ≤-reflexive (sym (size-algebra.assoc S m n l)) ,
      λ x _ → ≤-reflexive (sym (nat-poly.assoc p q r x))
    poly-monoid .term {m , p} =
      z≤n ,
      λ x _ → z≤n
    poly-monoid .account {k} =
      ≤-refl ,
      λ x _ → +-monoʳ-≤ k (≤-reflexive (sym (*-zeroʳ x)))

    open sub-monoid

    -- the sub-monoid of idempotently sized things
    poly-monoid-idem : sub-monoid poly-monoid
    poly-monoid-idem .member (x , p) = x ⊎ x ≡ x
    poly-monoid-idem ._`⊕_ {x , _}{y , _} ϕ₁ ϕ₂ = trans (interchange x y x y) (Eq.cong₂ _⊎_ ϕ₁ ϕ₂)
    poly-monoid-idem .`∅ = S .unit 0
    poly-monoid-idem .`acct = S .unit 0

    poly-monoid₀ : sub-monoid poly-monoid
    poly-monoid₀ .member (x , p) = x ≡ 0
    poly-monoid₀ ._`⊕_ {x , _}{y , _} refl refl = S .unit 0
    poly-monoid₀ .`∅ = refl
    poly-monoid₀ .`acct = refl

  open monoid-defn using (poly-monoid; poly-monoid₀) public
  open rmonoid using (∣_∣)
  open rmonoid poly-monoid using (_≤D⟨_,_⟩; _⊕_; ∅)

  size : ℕ → ∣ poly-monoid ∣
  size n = n , 0-poly

  raise : ∣ poly-monoid ∣ → ∣ poly-monoid ∣
  raise (n , p) = (n , ↑ p)

  scale : ℕ → ∣ poly-monoid ∣ → ∣ poly-monoid ∣
  scale n (m , p) = (m , nat-poly.scale n p)

  -- For LFPL, this only works for α that are of 0 size; in general of duplicable size
  raise→scale : ∀ α n → 0 ≤D⟨ raise α ⊕ size n , scale n α ⊕ size n ⟩
  raise→scale (m , p) n =
    ≤-refl ,
    λ x m⊔n≤x → ≤-trans (≤-reflexive (sym (nat-poly.unit (nat-poly.scale n p) x)))
                         (↑-wins n p x (S .size-algebra.bounded n m (≤-trans (≤-reflexive (S .size-algebra.comm n m)) m⊔n≤x)))

  -- this is true because ∅ is the terminal object anyway
  scale-zero : ∀ α → 0 ≤D⟨ scale zero α , ∅ ⟩
  scale-zero (m , p) =
    z≤n ,
    λ x _ → z≤n

  scale-suc : ∀ n α → poly-monoid₀ .sub-monoid.member α → 0 ≤D⟨ scale (1 + n) α , α ⊕ scale n α ⟩
  scale-suc n (m , p) refl =
    ≤-reflexive (S .size-algebra.unit 0) ,
    λ x m≤x → ≤-reflexive (begin
                              ⟪ p +-poly nat-poly.scale n p ⟫ x
                            ≡⟨ eval-+ p (nat-poly.scale n p) x ⟩
                              ⟪ p ⟫ x + ⟪ nat-poly.scale n p ⟫ x
                            ≡⟨ cong (λ □ → ⟪ p ⟫ x + □) (eval-scale n p x) ⟩
                              ⟪ p ⟫ x + n * ⟪ p ⟫ x
                            ≡⟨ refl ⟩
                              (1 + n) * ⟪ p ⟫ x
                            ≡⟨ sym (eval-scale (1 + n) p x) ⟩
                              ⟪ nat-poly.scale (1 + n) p ⟫ x
                            ∎)


{-
module soft-exponential (M : rmonoid)
                        (M₀ : sub-monoid M)
                        (open rmonoid using (∣_∣))
                        (open rmonoid M hiding (∣_∣))
                        (size         : ℕ → ∣ M ∣)
                        (raise        : ∣ M ∣ → ∣ M ∣) -- raise must be order preserving
                        (scale        : ℕ → ∣ M ∣ → ∣ M ∣)
                        (raise→scale : ∀ α n → 0 ≤D⟨ raise α ⊕ size n , scale n α ⊕ size n ⟩)
                        (scale-zero   : ∀ α → 0 ≤D⟨ scale zero α , ∅ ⟩)
                        (scale-suc    : ∀ n α → M₀ .sub-monoid.member α → 0 ≤D⟨ scale (1 + n) α , α ⊕ scale n α ⟩)
     where

  -- See also: Patrick Baillot, Virgile Mogbil. Soft lambda-calculus:
  -- a language for polynomial time computation.. 2004, Springer,
  -- pp.27-41, 2004, volume 2987 de LNCS

  open resource-category M M₀
  open sub-monoid M₀

  -- represent a natural number by
  --   ∀ X. !(X ⊸ X) ⊸ X ⊸ X
  -- which means that we can replicate the successor multiple times.

  ! : obj → obj
  ∥ ! X ∥ = ∥ X ∥
  ! X .realises α v x = Σ[ β ∈ ∣ M ∣ ] (0 ≤D⟨ α , raise β ⟩ × X .realises β v x)

  -- "soft promotion"
  !f : ∀ {X Y} → (X ==> Y) → (! X ==> ! Y)
  !f f .mor = f .mor
  !f f .expr = f .expr
  !f f .potential = f .potential
  !f f .potential-ok = f .potential-ok
  !f f .realisable η α v x (β , raiseβ≤α , v-x) = is-realisable
    where
      is-realisable : Eval _ _ _ _ _
      is-realisable .result = f .realisable η β v x v-x .result
      is-realisable .steps = f .realisable η β v x v-x .steps
      is-realisable .result-potential = raise (f .realisable η β v x v-x .result-potential)
      is-realisable .evaluation = f .realisable η β v x v-x .evaluation
      is-realisable .result-realises =
         f .realisable η β v x v-x .result-potential , identity , f .realisable η β v x v-x .result-realises
      is-realisable .accounted = {!f .realisable η β v x v-x .accounted!}
          -- FIXME: need to work this out,, probably need some extra properties of raise

  -- FIXME: also need:
  -- dist : ∀ {X Y} → (! X ⊗ ! Y) ==> ! (X ⊗ Y)

  multiplex : ∀ {X} → ℕ → ! X ==> (X ⊗ X) -- FIXME: n-fold tensor
  multiplex n .mor x = x , x
  multiplex n .expr _ = zero , zero
  multiplex n .potential = acct 1 ⊕ size 2
  multiplex n .potential-ok = {!!} -- FIXME: this assumes that 'size' is in the submonoid. Probably best
  multiplex n .realisable η α v x (β , α≥raiseβ , v-x) = is-realisable
    where
      is-realisable : Eval _ _ _ _ _
      is-realisable .result = v , v
      is-realisable .steps = 1
      is-realisable .result-potential = α ⊕ size 2
      is-realisable .evaluation = mkpair zero zero
      is-realisable .result-realises = β , β , ((pair α≥raiseβ) ⟫ (raise→scale β 2 ⟫ (fst ⟫ {!!}))) , v-x , v-x
      is-realisable .accounted = assoc-inv ⟫ acct⊕- ⟫ symmetry

  -- another way of writing multiplex (in a dependently typed
  -- language) is to use the iterator.

  -- we would get an LFPL multiplex if could provide n-many ⋄s.
-}

{-
module soft-affine where

  open poly-monoid (⊔-size-algebra)

  open iter-category (poly-monoid)
                     (poly-monoid₀)
                     (size)
                     (raise)
                     (λ x → x)
                     (scale)
                     (raise→scale)
                     (scale-zero)
                     (scale-suc)

  -- so we have a symmetric monoidal category, where the monoidal unit
  -- is terminal, with natural numbers and an iterator for them.

  -- Also, there ought to be a "soft" exponential
  --
  -- (i) a functor !
  -- (ii) multiplex n : ! X → Xⁿ

  -- define as ∥ ! X ∥ = ∥ X ∥
  --           ! X .realises α v x = Σ[ β ∈ ∣ M ∣ ] (0 ≤D⟨ raise β , α ⟩ × X .realises β v x


  open rmonoid poly-monoid
  open import nat-poly

  dup-nat : `nat ==> (`nat ⊗ `nat)
  dup-nat .mor n = n , n
  dup-nat .expr _ = zero , zero
  dup-nat .potential = acct 1
  dup-nat .potential-ok = refl
  dup-nat .realisable η (n' , p) _ n (refl , n≤n' , _) = is-realisable
    where
      is-realisable : Eval _ _ _ _ _
      is-realisable .result = nat-val n , nat-val n
      is-realisable .steps = 1
      is-realisable .result-potential = (n' , p)
      is-realisable .evaluation = mkpair zero zero
      is-realisable .result-realises =
        size n' , size n' ,
        (≤-reflexive (⊔-idem n') , λ x _ → z≤n) ,
        (refl , n≤n' , λ x _ → ≤-refl) ,
        (refl , n≤n' , λ x _ → ≤-refl)
      is-realisable .accounted = acct⊕- {1} {n' , p}

  nat-expr : ℕ → ∀ n → exp (suc n)
  nat-expr zero    n = seq true then seq ⋆ then (suc zero , zero)
  nat-expr (suc k) n = seq false then seq (nat-expr k (suc n)) then (suc zero , zero)

  nat-steps : ℕ → ℕ
  nat-steps zero    = 5
  nat-steps (suc k) = 2 + nat-steps k + 1 + 1

  nat-expr-eval : (k : ℕ) → (n : ℕ)(η : env (suc n)) → nat-expr k n , η ⇓[ nat-steps k ] nat-val k
  nat-expr-eval zero    n η = seq true (seq mkunit (mkpair (suc zero) zero))
  nat-expr-eval (suc k) n η = seq false (seq (nat-expr-eval k (suc n) (η ,- false)) (mkpair (suc zero) zero))
{-
  `const : ℕ → I ==> `nat
  `const k .mor tt = k
  `const k .expr = nat-expr k
  `const k .potential = size k ⊕ acct (nat-steps k)
  `const k .potential-ok = ⊔-idem _
  `const k .realisable η (n , p) ⋆ tt (z≤n , ϕ) = is-realisable
    where
      is-realisable : Eval _ _ _ _ _
      is-realisable .result = nat-val k
      is-realisable .steps = nat-steps k
      is-realisable .result-potential = size k
      is-realisable .evaluation = nat-expr-eval k _ (η ,- _)
      is-realisable .result-realises = refl , (≤-refl , (λ x _ → ≤-refl))
      is-realisable .accounted =
        m≤n⇒m≤n⊔o n (m≤n⇒m≤n⊔o 0 ≤-refl) ,
        (λ x ψ → ≤-trans (+-mono-≤ ≤-refl z≤n)
                          (≤-reflexive (trans (cong (λ □ → □ + ⟪ p ⟫ x) (trans (sym (+-identityʳ (nat-steps k))) (cong (λ □ → nat-steps k + □) (sym (*-zeroʳ x))))) (sym (eval-+ (const-poly (nat-steps k)) p x)))))
-}

{-
  -- this shouldn't be realisable (cons-free programming)
  `suc : `nat ==> `nat
  `suc .mor = suc
  `suc .expr n = seq false then (zero , suc zero)
  `suc .potential = size 1 ⊕ acct 3
  `suc .potential-ok = refl
  `suc .realisable η (m , p) _ n (refl , d , _) = is-realisable
    where
      is-realisable : Eval _ _ _ _ _
      is-realisable .result = nat-val (suc n)
      is-realisable .steps = 3
      is-realisable .result-potential = (suc m) , 0-poly
      is-realisable .evaluation = seq false (mkpair zero (suc zero))
      is-realisable .result-realises = refl , (s≤s d , (λ x x₁ → z≤n))
      is-realisable .accounted = {!!} , {!!} -- stuck here: not true that 1+m ≤ 1 ⊔ m
-}

  -- FIXME: this is true no matter the size monoid used, as long as
  -- the size component for morphisms is always 0.
  poly-time : ∀ {X} → (f : `nat ==> X) →
              Σ[ p ∈ ℕ-poly ] ((n : ℕ) → Σ[ v ∈ val ] Σ[ k ∈ ℕ ] (f .expr 0 , (nil ,- nat-val n) ⇓[ k ] v × k ≤ ⟪ p ⟫ n))
  poly-time f .proj₁ = f .potential .proj₂
  poly-time f .proj₂ n = r .result , r .steps , r .evaluation , under-time
    where
      r = f .realisable nil (size n) (nat-val n) n (refl , ≤-refl , (λ x _ → ≤-refl))

      under-time : r .steps ≤ ⟪ f .potential .proj₂ ⟫ n
      under-time = ≤-trans (m≤m+n (r .steps) (⟪ r .result-potential .proj₂ ⟫ n))
                           (≤-trans (r .accounted .proj₂ n {!f .potential-ok!}) -- FIXME: doesn't quite work, because we need to know that we didn't make a huge number in the term and iterate on it; a more refined solution is needed for the full soft monoid
                           (≤-reflexive (trans (eval-+ (f .potential .proj₂) 0-poly n) (+-identityʳ _))))
-}
