{-# OPTIONS --safe #-}

module AmortisedModel.Bundles where

open import Algebra.ResourceMonoid
open import Data.Product using (_,_)
open import IndexedLinear

module _ (ℳ : ResourceMonoid) (ℳ₀ : SubResourceMonoid ℳ) where

  import AmortisedModel.Preorder ℳ ℳ₀ as P
  import AmortisedModel.SMC ℳ ℳ₀ as S
  import AmortisedModel.Quantifiers ℳ ℳ₀ as Q
  import AmortisedModel.GradedExponential ℳ ℳ₀ as E

  open IndexedPreorder
  open IndexedSMC
  open IndexedProducts
  open IndexedExponential

  AmortIndexedPreorder : IndexedPreorder
  AmortIndexedPreorder .Obj = P._-Obj
  AmortIndexedPreorder ._⊢_⇒_ = P._⊢_⇒_
  AmortIndexedPreorder .⟨_⟩ = P.⟨_⟩_
  AmortIndexedPreorder .⟨_⟩-map = P.⟨_⟩-map
  AmortIndexedPreorder .⟨id⟩ = P.⟨id⟩
  AmortIndexedPreorder .⟨_∘_⟩ {Γ₁} {Γ₂} {Γ₃} {X} f g = P.⟨_∘_⟩ {Γ₁} {Γ₂} {Γ₃} {X} f g
  AmortIndexedPreorder .id = P.id
  AmortIndexedPreorder ._∘_ = P._∘_

  AmortIndexedSMC : IndexedSMC AmortIndexedPreorder
  AmortIndexedSMC .I = S.I
  AmortIndexedSMC ._⊗_ = S._⊗_
  AmortIndexedSMC ._⊗m_ = S._⊗m_
  AmortIndexedSMC .swap = S.swap
  AmortIndexedSMC .assoc = S.assoc
  AmortIndexedSMC .unit = S.unit-m , S.unit-inv-m
  AmortIndexedSMC .I-subst = S.I-subst
  AmortIndexedSMC .⊗-subst = S.⊗-subst
  AmortIndexedSMC ._⊸_ = S._⊸_
  AmortIndexedSMC .⊸-subst = S.⊸-subst
  AmortIndexedSMC .Λ = S.Λ
  AmortIndexedSMC .apply = S.apply

  AmortIndexedProducts : IndexedProducts AmortIndexedPreorder
  AmortIndexedProducts .`∀ = Q.`∀
  AmortIndexedProducts .`∀-intro = Q.`∀-intro
  AmortIndexedProducts .`∀-proj = Q.`∀-proj
  AmortIndexedProducts .`∀-subst = Q.`∀-subst

  AmortIndexedExponential : IndexedExponential AmortIndexedPreorder AmortIndexedSMC
  AmortIndexedExponential .![_] = E.![_]
  AmortIndexedExponential .![_]-map = E.![_]-map
  AmortIndexedExponential .!-subst f = E.!-subst f
  AmortIndexedExponential .discard = E.discard
  AmortIndexedExponential .comult = E.comult
  AmortIndexedExponential .derelict = E.derelict
  AmortIndexedExponential .duplicate = E.duplicate
  AmortIndexedExponential .monoidal = E.!-monoidal
  AmortIndexedExponential .weaken = E.!-wk
