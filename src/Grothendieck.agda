{-# OPTIONS --postfix-projections --without-K #-}

module Grothendieck where

open import Data.Nat using (ℕ; zero; _+_; _*_)
open import Data.Product using (_×_; proj₁; proj₂; Σ; _,_; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

-- Other instances:
-- 1. Heap manipulating model
-- 2. Weighted sets? Γ -Obj = Γ → W, Γ ⊢ α ⇒ β iff ∀ γ → α γ ≤ β γ
--    would get length spaces, and the capability thing of Vikraman and Neel
-- 3. BCI realisability / R-LCA realisability; might be easiest to do with ordered realisability
-- 4. PCA realisability, so would get erasability analysis
-- Realisability is a (sort of) refinement of the weighted sets model to include weights on the morphisms

-- 5. What if we weaken some of the requirements (such as ⊸), can we
-- get a two-level language for talking about very weak models?
-- E.g. log-space? circuits?

-- 6. Reversible computation? Maybe using Π (the reversible thing)?

-- 7. If we allow for non preorder version, then we could get quantum
-- things working? Need to check everything in the soundness proof of
-- the interpretation.

-- 8. What does realisable by processes mean? Would we get some kind
-- of session type thing? If we had a 'Sessions' monad in the indexing
-- category?

-- TODO:
-- 1. What relationship do we get with 'Set'? for the category of Contexts?
--    - Forget : Con → Set
--    - (-,I)  : Set → Con
--    - (X,R) ↦ (Σ X (λ x → ⊤ ⊢ I ⇒ X x)) : Con → Set   -- realisable elements (could be relativised to any A : ⊤ -Obj)
-- presumably the first two are a monoidal adjunction, which forms a LNL model?
--
-- 2. What about the category of Sets and binary predicates? Does this
-- model information flow? (if we interpret the relations as
-- indistinguishability?)

postulate
  fext : ∀ {A : Set}{B : A → Set} {f g : (a : A) → B a} →
         (∀ a → f a ≡ g a) → f ≡ g


⟪_⟫ : ∀ {Γ₁ Γ₂ : Set} → (Γ₁ → Γ₂) → (Γ₂ → Set) → (Γ₁ → Set)
⟪ f ⟫ A γ = A (f γ)

record IndexedPreorder : Set₂ where
  field
    -- Objects
    Obj   : Set → Set₁
    -- and Morphisms
    _⊢_⇒_ : (Γ : Set) → Obj Γ → Obj Γ → Set

  _⊢_≅_ : (Γ : Set) → Obj Γ → Obj Γ → Set
  Γ ⊢ X ≅ Y = (Γ ⊢ X ⇒ Y) × (Γ ⊢ Y ⇒ X)

  field
    ⟨_⟩_ : ∀ {Γ Δ} → (Γ → Δ) → Obj Δ → Obj Γ

    ⟨_⟩-map : ∀ {Γ Δ X Y} (f : Γ → Δ) → Δ ⊢ X ⇒ Y → Γ ⊢ (⟨ f ⟩ X) ⇒ (⟨ f ⟩ Y)

    ⟨id⟩  : ∀ {Γ X} → Γ ⊢ X ≅ (⟨ (λ x → x) ⟩ X)
    ⟨_∘_⟩ : ∀ {Γ₁ Γ₂ Γ₃ X} (f : Γ₂ → Γ₃) (g : Γ₁ → Γ₂) →
             Γ₁ ⊢ (⟨ g ⟩ (⟨ f ⟩ X)) ≅ (⟨ (λ x → f (g x)) ⟩ X)

    -- identities and composition
    id  : ∀ {Γ X} → Γ ⊢ X ⇒ X
    _∘_ : ∀ {Γ X Y Z} → Γ ⊢ Y ⇒ Z → Γ ⊢ X ⇒ Y → Γ ⊢ X ⇒ Z

  infixl 4 _∘_

  field
    -- Symmetric monoidal structure
    I    : ∀ {Γ} → Obj Γ
    _⊗_  : ∀ {Γ} → Obj Γ → Obj Γ → Obj Γ
    _⊗m_ : ∀ {Γ X Y X' Y'} → Γ ⊢ X ⇒ X' → Γ ⊢ Y ⇒ Y' → Γ ⊢ (X ⊗ Y) ⇒ (X' ⊗ Y')

    -- swapping, associativity and units
    swap  : ∀ {Γ X Y} → Γ ⊢ (X ⊗ Y) ⇒ (Y ⊗ X)
    assoc : ∀ {Γ X Y Z} → Γ ⊢ (X ⊗ (Y ⊗ Z)) ≅ ((X ⊗ Y) ⊗ Z)
    unit  : ∀ {Γ X} → Γ ⊢ (I ⊗ X) ≅ X

    -- reindexing is symmetric monoidal
    -- TODO: do these only need to be lax?
    I-subst : ∀ {Γ₁ Γ₂} (f : Γ₁ → Γ₂) → Γ₁ ⊢ ⟨ f ⟩ I ≅ I
    -- TODO: rename to ⊗-subst
    ⟨_⊗⟩ : ∀ {Γ Δ X Y} (f : Γ → Δ) → Γ ⊢ ⟨ f ⟩ (X ⊗ Y) ≅ ((⟨ f ⟩ X) ⊗ (⟨ f ⟩ Y))

    -- Closed
  field
    _⊸_   : ∀ {Γ} → Obj Γ → Obj Γ → Obj Γ
    ⊸-subst : ∀ {Γ₁ Γ₂ X Y} (f : Γ₁ → Γ₂) →
              Γ₁ ⊢ ⟨ f ⟩ (X ⊸ Y) ≅ ((⟨ f ⟩ X) ⊸ (⟨ f ⟩ Y))
    Λ     : ∀ {Γ X Y Z} → Γ ⊢ (X ⊗ Y) ⇒ Z → Γ ⊢ X ⇒ (Y ⊸ Z)
    apply : ∀ {Γ X Y} → Γ ⊢ ((X ⊸ Y) ⊗ X) ⇒ Y

  ⊸-map : ∀ {Γ X₁ X₂ Y₁ Y₂} →
          Γ ⊢ X₂ ⇒ X₁ →
          Γ ⊢ Y₁ ⇒ Y₂ →
          Γ ⊢ (X₁ ⊸ Y₁) ⇒ (X₂ ⊸ Y₂)
  ⊸-map f g = Λ (g ∘ (apply ∘ (id ⊗m f)))

  field
    -- Products
    `∀       : ∀ {Γ} A → Obj (Σ Γ A) → Obj Γ
    `∀-intro : ∀ {Γ A X Y} → (Σ Γ A) ⊢ (⟨ proj₁ ⟩ X) ⇒ Y → Γ ⊢ X ⇒ (`∀ A Y)
    `∀-proj  : ∀ {Γ A X} → (Σ Γ A) ⊢ (⟨ proj₁ ⟩ `∀ A X) ⇒ X
    `∀-subst : ∀ {Γ₁ Γ₂ A X} (f : Γ₁ → Γ₂) →
               Γ₁ ⊢ ⟨ f ⟩ (`∀ A X) ≅ `∀ (⟪ f ⟫ A) (⟨ (λ x → (f (x .proj₁)) , x .proj₂) ⟩ X)

  `∀-map : ∀ {Γ A X Y} → (Σ Γ A) ⊢ X ⇒ Y → Γ ⊢ (`∀ A X) ⇒ (`∀ A Y)
  `∀-map f = `∀-intro (f ∘ `∀-proj)

    -- FIXME: booleans, indexed in a certain way

    -- FIXME: graded exponentials
  field
    -- FIXME: generalise to any semiring
    ![_] : ∀ {Γ} → ℕ → Obj Γ → Obj Γ   -- FIXME: why not over Γ × ℕ ???
    ![_]-map : ∀ {Γ} n {X Y} → Γ ⊢ X ⇒ Y → Γ ⊢ ![ n ] X ⇒ ![ n ] Y
    !-subst : ∀ {Γ₁ Γ₂ n A} (f : Γ₁ → Γ₂) → Γ₁ ⊢ ⟨ f ⟩ ![ n ] A ≅ ![ n ] (⟨ f ⟩ A)
    discard : ∀ {Γ X} → Γ ⊢ ![ 0 ] X ≅ I --- FIXME: any way to do without this being an iso?
    derelict : ∀ {Γ X} → Γ ⊢ ![ 1 ] X ⇒ X

module Make (L : IndexedPreorder) where

  open IndexedPreorder L renaming ( Obj to _-Obj
                                  ; id  to id-L
                                  ; _∘_ to _∘-L_
                                  ; I   to I-L
                                  ; _⊗_ to _⊗L_
                                  ; _⊗m_ to _⊗mL_
                                  ; swap to swap-L
                                  ; unit to unit-L
                                  ; _⊸_  to _⊸L_
                                  ; Λ    to ΛL
                                  ; apply to applyL
                                  ; ![_]  to ![_]L
                                  ; ![_]-map to ![_]-mapL
                                  ; derelict to derelictL
                                  ; discard to discardL)

  record Obj : Set₂ where
    field
      Hi : Set
      Lo : Hi -Obj
  open Obj

  record _⇒_ (X Y : Obj) : Set where
    field
      mor   : X .Hi → Y .Hi
      morlo : X .Hi ⊢ X .Lo ⇒ (⟨ mor ⟩ Y .Lo)
  open _⇒_

  infix 4 _⇒_

  -- FIXME: equality of morphisms

  ------------------------------------------------------------------------
  -- Part I : Identities and Composition
  id : ∀ {X} → X ⇒ X
  id .mor x = x
  id .morlo = ⟨id⟩ .proj₁

  _∘_ : ∀ {X Y Z} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
  (f ∘ g) .mor   = λ x → f .mor (g .mor x)
  (f ∘ g) .morlo = ((⟨ f .mor ∘ g .mor ⟩) .proj₁ ∘-L (⟨ g .mor ⟩-map (f .morlo))) ∘-L (g .morlo)

  ------------------------------------------------------------------------
  -- Part II : Symmetric Monoidal

  I : Obj
  I .Hi = ⊤
  I .Lo = I-L

  _⊗_ : Obj → Obj → Obj
  (X ⊗ Y) .Hi = X .Hi × Y .Hi
  (X ⊗ Y) .Lo = (⟨ proj₁ ⟩ X .Lo) ⊗L (⟨ proj₂ ⟩ Y .Lo)

  swap₀ : ∀ {X Y : Set} → X × Y → Y × X
  swap₀ (x , y) = (y , x)

  swap : ∀ {X Y} → (X ⊗ Y) ⇒ (Y ⊗ X)
  swap .mor = swap₀
  swap .morlo =
    ⟨ swap₀ ⊗⟩ .proj₂ ∘-L
    (⟨ proj₁ ∘ swap₀ ⟩) .proj₂ ⊗mL (⟨ proj₂ ∘ swap₀ ⟩) .proj₂ ∘-L
    swap-L

  _⊗m_ : ∀ {X₁ X₂ Y₁ Y₂} →
         (X₁ ⇒ X₂) →
         (Y₁ ⇒ Y₂) →
         (X₁ ⊗ Y₁) ⇒ (X₂ ⊗ Y₂)
  (f ⊗m g) .mor (x , y) = (f .mor x) , (g .mor y)
  (f ⊗m g) .morlo =
    ⟨ m ⊗⟩ .proj₂ ∘-L
    (⟨ proj₁ ∘ m ⟩) .proj₂ ⊗mL (⟨ proj₂ ∘ m ⟩) .proj₂ ∘-L
    ((⟨ f .mor ∘ proj₁ ⟩) .proj₁) ⊗mL (⟨ g .mor ∘ proj₂ ⟩) .proj₁ ∘-L
    ⟨ proj₁ ⟩-map (f .morlo) ⊗mL ⟨ proj₂ ⟩-map (g .morlo)
     where m = λ p → (f .mor (p .proj₁) , g .mor (p .proj₂))

  -- FIXME: associativity

  unit-1 : ∀ {X} → (I ⊗ X) ⇒ X
  unit-1 .mor = proj₂
  unit-1 .morlo = (unit-L .proj₁) ∘-L ((I-subst proj₁ .proj₁) ⊗mL id-L)

  unit-2 : ∀ {X} → X ⇒ (I ⊗ X)
  unit-2 .mor x = (tt , x)
  unit-2 .morlo =
    (⟨ (λ x → tt , x) ⊗⟩ .proj₂) ∘-L
    ((((⟨ proj₁ ∘ (λ x → tt , x) ⟩) .proj₂) ⊗mL (⟨ proj₂ ∘ (λ x → tt , x) ⟩) .proj₂) ∘-L
    (((I-subst (λ x → tt) .proj₂) ⊗mL ⟨id⟩ .proj₁) ∘-L
    (unit-L .proj₂)))

  ------------------------------------------------------------------------
  -- Part III : Closure, which relies on products
  ev : ∀ {X Y : Set} → (X → Y) × X → Y
  ev (f , x) = f x

  _⊸_ : Obj → Obj → Obj
  (X ⊸ Y) .Hi = X .Hi → Y .Hi
  (X ⊸ Y) .Lo = `∀ (λ _ → X .Hi) ((⟨ proj₂ ⟩ X .Lo) ⊸L (⟨ ev ⟩ Y .Lo))

  Λ : ∀ {X Y Z} → (X ⊗ Y) ⇒ Z → X ⇒ (Y ⊸ Z)
  Λ f .mor   = λ x y → f .mor (x , y)
  Λ f .morlo =
    `∀-subst (λ x y → f .mor (x , y)) .proj₂ ∘-L
    `∀-map (⊸-subst _ .proj₂) ∘-L
    `∀-map (⊸-map ((⟨ proj₂ ∘ h ⟩) .proj₁) ((⟨ ev ∘ h ⟩) .proj₂)) ∘-L
    `∀-intro (ΛL (f .morlo))
    where h = λ x → (λ y → f .mor (x .proj₁ , y)) , x .proj₂

  apply : ∀ {X Y} → ((X ⊸ Y) ⊗ X) ⇒ Y
  apply .mor = ev
  apply .morlo = applyL ∘-L `∀-proj ⊗mL id-L

  ------------------------------------------------------------------------
  -- Part IV : Graded exponentials
  ![_] : ℕ → Obj → Obj
  ![ n ] X .Hi = X .Hi
  ![ n ] X .Lo = ![ n ]L (X .Lo)

{-
  ![_]-map : ∀ n {X Y} → (f : X ⇒ Y) → ![ n ] X ⇒ ![ n ] Y
  ![ n ]-map f .mor = f .mor
  ![ n ]-map f .morlo = {!!}
-}

  -- !-monoidal
  -- derelict
  -- discard
  -- duplicate
  -- comult

  ------------------------------------------------------------------------
  -- Part V : Embedding L

{- -- fails due to universe levels :/
  Em : Obj
  Em .Hi = {!⊤ -Obj!}
  Em .Lo = {!!}
-}
  ------------------------------------------------------------------------
  -- Dependent type structure, as a RCwF

  record Iso (X Y : Set) : Set where
    field
      fwd : X → Y
      bwd : Y → X
      fwd∘bwd : ∀ y → fwd (bwd y) ≡ y
      bwd∘fwd : ∀ x → bwd (fwd x) ≡ x
  open Iso

  add : (Δ₁ Δ₂ : Obj) → Iso (Δ₁ .Hi) (Δ₂ .Hi) → Obj
  add Δ₁ Δ₂ iso .Hi = Δ₁ .Hi
  add Δ₁ Δ₂ iso .Lo = (Δ₁ .Lo) ⊗L (⟨ iso .fwd ⟩ Δ₂ .Lo)

  -- Types only depend on sets, but also include information on the
  -- resource part
  record Ty (Γ : Set) : Set₂ where
    field
      Hi : Γ → Set
      Lo : (Σ Γ Hi) -Obj
  open Ty

  -- This won't preserve composition on the nose, because reindexing
  -- doesn't.
  ⟨_⟩Ty : ∀ {Γ₁ Γ₂} → (Γ₁ → Γ₂) → Ty Γ₂ → Ty Γ₁
  ⟨ f ⟩Ty A .Hi γ = A .Hi (f γ)
  ⟨ f ⟩Ty A .Lo = ⟨ (λ x → (f (x .proj₁) , x .proj₂)) ⟩ (A .Lo)

  record RTm (Δ : Obj) (A : Ty (Δ .Hi)) : Set where
    field
      mor   : (δ : Δ .Hi) → A .Hi δ
      morlo : Δ .Hi ⊢ Δ .Lo ⇒ (⟨ (λ δ → δ , mor δ) ⟩ A .Lo)
  open RTm

  ⟨_⟩RTm : ∀ {Δ₁ Δ₂ A} → (f : Δ₁ ⇒ Δ₂) → RTm Δ₂ A → RTm Δ₁ (⟨ f .mor ⟩Ty A)
  ⟨ f ⟩RTm M .mor δ₁ = M .mor (f .mor δ₁)
  ⟨ f ⟩RTm M .morlo =
     ((⟨ (λ x → (f .mor (x .proj₁) , x .proj₂)) ∘ (λ δ → δ , M .mor (f .mor δ)) ⟩) .proj₂) ∘-L
     (⟨ (λ δ → δ , M .mor δ) ∘ f .mor ⟩) .proj₁ ∘-L
     ⟨ f .mor ⟩-map (M .morlo) ∘-L
     f .morlo

  record Tm (Γ : Set) (A : Ty Γ) : Set where
    field
      mor   : (γ : Γ) → A .Hi γ
  open Tm

  -- Resourced comprehension
  _,[_]_ : (Δ : Obj) → ℕ → Ty (Δ .Hi) → Obj
  (Δ ,[ n ] A) .Hi = Σ[ δ ∈ Δ .Hi ] (A .Hi δ)
  (Δ ,[ n ] A) .Lo = (⟨ proj₁ ⟩ Δ .Lo) ⊗L ![ n ]L (A .Lo)

  infixl 10 _,[_]_

  p : ∀ {Δ A} → Δ ,[ 0 ] A ⇒ Δ
  p .mor = proj₁
  p .morlo = unit-L .proj₁ ∘-L swap-L ∘-L (id-L ⊗mL (discardL .proj₁))

  varR : ∀ {Δ A} → RTm ((![ 0 ] Δ) ,[ 1 ] A) (⟨ proj₁ ⟩Ty A)
  varR .mor = proj₂
  varR .morlo =
    ((⟨ (λ x → (proj₁ (x .proj₁) , x .proj₂)) ∘ (λ δ → δ , δ .proj₂) ⟩) .proj₂) ∘-L
    (⟨id⟩ .proj₁) ∘-L
    (unit-L .proj₁) ∘-L
    (discardL .proj₁ ⊗mL derelictL) ∘-L
    (!-subst proj₁ .proj₁ ⊗mL id-L)

  -- TODO: wk (7c)
  wk : ∀ {Δ₁ Δ₂ A ρ} → (f : Δ₁ ⇒ Δ₂) → (Δ₁ ,[ ρ ] ⟨ f .mor ⟩Ty A) ⇒ Δ₂ ,[ ρ ] A
  wk f .mor (δ , a) = f .mor δ , a
  wk f .morlo =
    (⟨ (λ δ' → f .mor (δ' .proj₁) , δ' .proj₂) ⊗⟩ .proj₂) ∘-L
     ((⟨ proj₁ ∘ (λ δ' → f .mor (δ' .proj₁) , δ' .proj₂) ⟩) .proj₂ ∘-L
     (⟨ f .mor ∘ proj₁ ⟩) .proj₁ ∘-L
     ⟨ proj₁ ⟩-map (f .morlo))
    ⊗mL
     !-subst (λ x → f .mor (x .proj₁) , x .proj₂) .proj₂

  eq-pair : ∀ {A : Set}{B : A → Set} →
              {a a' : A}{b : B a}{b' : B a'} →
            (e : a ≡ a') →
            subst B e b ≡ b' →
            (a , b) ≡ (a' , b')
  eq-pair refl refl = refl

  -- Resourced term to substitution (7d) which requires context addition
  1-subst : ∀ {Δ₁ Δ₂ : Obj}{A : Ty (Δ₁ .Hi)} {n : ℕ} (iso : Iso (Δ₁ .Hi) (Δ₂ .Hi)) → RTm Δ₂ (⟨ iso .bwd ⟩Ty A) →
            add Δ₁ (![ n ] Δ₂) iso ⇒ (Δ₁ ,[ n ] A)
  1-subst {A = A} iso M .mor δ = δ , subst (A .Hi) (iso .bwd∘fwd δ) (M .mor (iso .fwd δ))
  1-subst {Δ₁}{A = A} {n} iso M .morlo =
    ⟨ (λ δ → δ , subst (A .Hi) (iso .bwd∘fwd δ) (M .mor (iso .fwd δ))) ⊗⟩ .proj₂ ∘-L
    (((⟨ proj₁ ∘ (λ δ → δ , subst (A .Hi) (iso .bwd∘fwd δ) (M .mor (iso .fwd δ))) ⟩) .proj₂) ∘-L ⟨id⟩ .proj₁)
     ⊗mL  -- Ooft!
     ((((subst (λ □ → Δ₁ .Hi ⊢ (⟨ □ ⟩ ![ n ]L (A .Lo)) ⇒ (⟨ (λ δ → δ , subst (A .Hi) (iso .bwd∘fwd δ) (M .mor (iso .fwd δ))) ⟩ ![ n ]L (A .Lo))) (sym eq) id-L ∘-L ((⟨ (λ x → iso .bwd x , M .mor x) ∘ iso .fwd ⟩) .proj₁)) ∘-L (⟨ iso .fwd ⟩-map (!-subst (λ x → iso .bwd x , M .mor x) .proj₂))) ∘-L (⟨ iso .fwd ⟩-map (![ n ]-mapL ((⟨ (λ x → iso .bwd (x .proj₁) , x .proj₂) ∘ (λ δ → δ , M .mor δ) ⟩) .proj₁)))) ∘-L (⟨ iso .fwd ⟩-map (![ n ]-mapL (M .morlo))))
     where eq : (λ x → iso .bwd (iso .fwd x) , M .mor (iso .fwd x))
                  ≡
                (λ x → x , subst (A .Hi) (iso .bwd∘fwd x) (M .mor (iso .fwd x)))
           eq = fext (λ x → eq-pair (iso .bwd∘fwd x) refl)

  -- 7e
  0-subst : ∀ {Δ A} → Tm (Δ .Hi) A → Δ ⇒ Δ ,[ 0 ] A
  0-subst tm .mor δ = δ , tm .mor δ
  0-subst tm .morlo =
    ⟨ (λ δ → δ , tm .mor δ) ⊗⟩ .proj₂ ∘-L
    (⟨ proj₁ ∘ (λ δ → δ , tm .mor δ) ⟩) .proj₂ ⊗mL ⟨ (λ δ → δ , tm .mor δ) ⟩-map (discardL .proj₂) ∘-L
    (⟨id⟩ .proj₁ ⊗mL I-subst (λ δ → δ , tm .mor δ) .proj₂) ∘-L
    swap-L ∘-L
    unit-L .proj₂

  -- TODO: pt (6) about emp and ext and scaling and addition

  -- Context addition is EVIL! Relies on the underlying sets being
  -- equal, which is only going to work (w.o univalence) if they are
  -- constructed in an identical way. But maybe isomorphism is enough?
  -- Or I could use cubical?

  -- Is there a way of arranging the syntax / semantics so that the
  -- linear part is "an output" of typing, while the non-linear part
  -- is an input, so we don't have to check for equality (because it
  -- will always be true by sharing inputs).

  -- How to establish the additivity of two contexts without relying
  -- on equality?

  -- Γ ▷ Δ ⊢ M : X -- where Γ and Δ share variable
  -- structure. Presumably this is covered by "democratic" CwFs?

  -- Type checking takes a normal context as input and returns the
  -- annotated context. Can this be worked into the meaning somehow?

  -- Problem is that the matching is not necessarily preserved by
  -- isomorphism??

  -- Π-types
  Π : ∀ {Δ : Obj} (ρ : ℕ) (S : Ty (Δ .Hi)) (T : Ty (Σ (Δ .Hi) (λ δ → S .Hi δ))) → Ty (Δ .Hi)
  Π ρ S T .Hi δ = (s : S .Hi δ) → T .Hi (δ , s)
  Π ρ S T .Lo =
    `∀ (λ δ' → (S .Hi (δ' .proj₁)))
       ((⟨ (λ δ' → (δ' .proj₁ .proj₁ , δ' .proj₂)) ⟩ S .Lo) ⊸L
        (⟨ (λ δ' → ((δ' .proj₁ .proj₁ , δ' .proj₂) , δ' .proj₁ .proj₂ (δ' .proj₂))) ⟩ T .Lo))

  ΛTm : ∀ {Δ : Obj}{ρ S T} →
        Tm (Σ (Δ .Hi) (λ δ → S .Hi δ)) T →
        Tm (Δ .Hi) (Π {Δ} ρ S T)
  ΛTm f .mor δ s = f .mor (δ , s)

  ΛTm⁻¹ : ∀ {Δ : Obj}{ρ S T} →
          Tm (Δ .Hi) (Π {Δ} ρ S T) →
          Tm (Σ (Δ .Hi) (λ δ → S .Hi δ)) T
  ΛTm⁻¹ f .mor (δ , s) = f .mor δ s

  ΛRTm : ∀ {Δ : Obj}{ρ S T} →
         RTm (Δ ,[ ρ ] S) T →
         RTm Δ (Π {Δ} ρ S T)
  ΛRTm f .mor δ s = f .mor (δ , s)
  ΛRTm f .morlo = {!!}

  ΛRTm⁻¹ : ∀ {Δ : Obj}{ρ S T} →
           RTm Δ (Π {Δ} ρ S T) →
           RTm (Δ ,[ ρ ] S) T
  ΛRTm⁻¹ f .mor (δ , s) = f .mor δ s
  ΛRTm⁻¹ f .morlo = {!!}

  Σ⊗ : ∀ {Δ : Obj} (S : Ty (Δ .Hi)) (T : Ty (Σ (Δ .Hi) (λ δ → S .Hi δ))) → Ty (Δ .Hi)
  Σ⊗ S T .Hi δ = Σ (S .Hi δ) (λ s → T .Hi (δ , s))
  Σ⊗ S T .Lo =
    (⟨ (λ δ' → (δ' .proj₁ , δ' .proj₂ .proj₁)) ⟩ S .Lo) ⊗L
    (⟨ (λ δ' → ((δ' .proj₁ , δ' .proj₂ .proj₁) , δ' .proj₂ .proj₂)) ⟩ T .Lo)

  -- FIXME: introduction and elimination of Σ⊗

  ------------------------------------------------------------------------
  -- TODO: Boolean types

  ------------------------------------------------------------------------------
  -- TODO: Universe
