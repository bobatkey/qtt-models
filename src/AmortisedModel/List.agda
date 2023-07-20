{-# OPTIONS --safe #-}

open import Algebra.ResourceMonoid

module AmortisedModel.List (ℳ : ResourceMonoid) (ℳ₀ : SubResourceMonoid ℳ) where

open import Data.Nat using (_+_; suc; zero)
open import Data.Empty using (⊥)
open import Data.Fin using (suc; zero)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax; _×_; Σ; _,_; proj₁; proj₂)

open import AmortisedModel.Preorder ℳ ℳ₀
open import AmortisedModel.SMC ℳ ℳ₀

open import MachineModel

open ResourceMonoid ℳ renaming (Carrier to |ℳ|)
open SubResourceMonoid ℳ₀ renaming (member to mor-potential)


list : ∀ {Γ} A → (Σ Γ A) -Obj → (Σ[ γ ∈ Γ ] (List (A γ))) -Obj
list A X (γ , []) .realises α (false , ⋆) = 0 ≤D⟨ α , ∅ ⟩
list A X (γ , []) .realises α _ = ⊥
list A X (γ , e ∷ elems) .realises α (true , (v₁ , v₂)) =
  Σ[ α₁ ∈ |ℳ| ] Σ[ α₂ ∈ |ℳ| ] (0 ≤D⟨ α , α₁ ⊕ α₂ ⟩ × X (γ , e) .realises α₁ v₁ × list A X (γ , elems) .realises α₂ v₂)
list A X (γ , e ∷ elems) .realises α _ = ⊥

`nil : ∀ {Γ A X} → Γ ⊢ I ⇒ ⟨ (λ γ → (γ , [])) ⟩ list A X
`nil .realiser .expr n = seq false then (zero , suc zero)
`nil .realiser .potential = acct 3
`nil .realiser .potential-ok = `acct
`nil .realises γ η α ⋆ x .result = false , ⋆
`nil .realises γ η α ⋆ x .steps = 3
`nil .realises γ η α ⋆ x .result-potential = α
`nil .realises γ η α ⋆ x .evaluation = seq false (mkpair zero (suc zero))
`nil .realises γ η α ⋆ x .result-realises = term
`nil .realises γ η α ⋆ x .accounted = acct⊕-

`cons : ∀ {Γ A X} →
        (Σ[ γ ∈ Γ ] (A γ × List (A γ))) ⊢
          ⟨ (λ (γ , e , es) → (γ , e)) ⟩ X ⊗ ⟨ (λ (γ , e , es) → (γ , es)) ⟩ list A X
          ⇒
          ⟨ (λ (γ , e , es) → (γ , e ∷ es)) ⟩ list A X
`cons .realiser .expr n = seq true then (zero , suc zero)
`cons .realiser .potential = acct 3
`cons .realiser .potential-ok = `acct
`cons .realises γ η α (v₁ , v₂) x .result = true , (v₁ , v₂)
`cons .realises γ η α (v₁ , v₂) x .steps = 3
`cons .realises γ η α (v₁ , v₂) x .result-potential = α
`cons .realises γ η α (v₁ , v₂) x .evaluation = seq true (mkpair zero (suc zero))
`cons .realises γ η α (v₁ , v₂) x .result-realises = x
`cons .realises γ η α (v₁ , v₂) x .accounted = acct⊕-

`match : ∀ {Γ A X Y Z} →
         Γ ⊢ X ⇒ ⟨ (λ γ → (γ , [])) ⟩ Z →
         (Σ[ γ ∈ Γ ] (A γ × List (A γ))) ⊢ (⟨ (λ (γ , e , es) → γ) ⟩ X ⊗ (⟨ (λ (γ , e , es) → (γ , e)) ⟩ Y ⊗ ⟨ (λ (γ , e , es) → (γ , es)) ⟩ list A Y)) ⇒ ⟨ (λ (γ , e , es) → (γ , e ∷ es)) ⟩ Z →
         (Σ[ γ ∈ Γ ] List (A γ)) ⊢ ⟨ proj₁ ⟩ X ⊗ list A Y ⇒ Z
`match nilCase consCase .realiser .expr n =
  letpair zero then
  letpair zero then
  cond suc zero
   then seq (suc (suc (suc zero)) , zero) then consCase .realiser .expr _
   else (seq ` (suc (suc (suc zero))) then nilCase .realiser .expr _)
`match nilCase consCase .realiser .potential =
  acct 5 ⊕ (consCase .realiser .potential ⊕ nilCase .realiser .potential)
`match nilCase consCase .realiser .potential-ok =
  `acct `⊕ (consCase .realiser .potential-ok `⊕ nilCase .realiser .potential-ok)
`match nilCase consCase .realises (γ , e ∷ es) η α (v , (true , (v₁ , v₂))) (α₁ , α₂ , d , X-α₁-v , (α₃ , α₄ , d' , Y-α₃-v₁ , ListY-α₄-v₂)) = is-realised
  where
  r = consCase .realises (γ , e , es) (η ,- _ ,- _ ,- _ ,- _ ,- _) α (v , (v₁ , v₂))
        (α₁ , α₂ , d , X-α₁-v , α₃ , α₄ , d' , Y-α₃-v₁ , ListY-α₄-v₂)

  is-realised : Eval _ _ _ _
  is-realised .result = r .result
  is-realised .steps = 5 + r .steps
  is-realised .result-potential = r .result-potential
  is-realised .evaluation = letpair zero (letpair zero (cond-true (suc zero) (seq (mkpair (suc (suc (suc zero))) zero) (r .evaluation))))
  is-realised .result-realises = r .result-realises
  is-realised .accounted =
    assoc-inv ；
    acct⊕- ；
    pair fst ；
    r .accounted

`match nilCase consCase .realises (γ , []) η α (v , (false , ⋆)) (α₁ , α₂ , d , X-α₁-v , d') = is-realised
  where
  r = nilCase .realises γ (η ,- _ ,- _ ,- _ ,- _ ,- _) α₁ v X-α₁-v

  is-realised : Eval _ _ _ _
  is-realised .result = r .result
  is-realised .steps = 5 + r .steps
  is-realised .result-potential = r .result-potential
  is-realised .evaluation =
    letpair zero
      (letpair zero
        (cond-false (suc zero)
          (seq (access (suc (suc (suc zero)))) (r .evaluation))))
  is-realised .result-realises = r .result-realises
  is-realised .accounted =
    assoc-inv ；
    acct⊕- ；
    pair (snd _ _) ；
    pair' (d ； fst) ；
    r .accounted
