{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat.Properties using (module ≤-Reasoning)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import MachineModel
open import ResourceMonoid
open import amort-realisers

-- ultimately would like to prove that for any finitary polynomial
-- type we have an initial fixpoint when it is augmented by diamonds.

module LFPL.Iterator
  (M : rmonoid) (M₀ : sub-monoid M)
  (open rmonoid M renaming (Carrier to |M|))
  (size         : ℕ → |M|)
  (raise        : |M| → |M|)
  (raise-ok     : ∀ {α} → M₀ .sub-monoid.member α → M₀ .sub-monoid.member (raise α))
  (scale        : ℕ → |M| → |M|)
  (raise→scale  : ∀ α n → 0 ≤D⟨ raise α ⊕ size n , scale n α ⊕ size n ⟩)
  (scale-zero   : ∀ α → 0 ≤D⟨ scale zero α , ∅ ⟩)
  (scale-suc    : ∀ n α → M₀ .sub-monoid.member α → 0 ≤D⟨ scale (1 + n) α , α ⊕ scale n α ⟩)
  -- one of these two is not possible in the Soft Affine category
  (size-suc     : ∀ n → 0 ≤D⟨ size (suc n) , size n ⊕ size 1 ⟩)
  (suc-size     : ∀ n → 0 ≤D⟨ size n ⊕ size 1 , size (suc n) ⟩)
      where

open amort-indexed-preorder M M₀ public
open sub-monoid M₀

`nat : ℕ -Obj
`nat n .realises α v = v ≡ nat-val n × 0 ≤D⟨ α , size (suc n) ⟩

◇ : ∀ {Γ} → Γ -Obj
◇ γ .realises α ⋆         = 0 ≤D⟨ α , size 1 ⟩
◇ γ .realises α (_ , _)   = ⊥
◇ γ .realises α true      = ⊥
◇ γ .realises α false     = ⊥
◇ γ .realises α (clo _ _) = ⊥

`zero : ∀ {Γ} → Γ ⊢ ◇ ⇒ ⟨ K zero ⟩ `nat
`zero .realiser .expr _ = seq true then seq ⋆ then (suc zero , zero)
`zero .realiser .potential = acct 5
`zero .realiser .potential-ok = `acct
`zero .realises γ η α ⋆ α⇒1 .result = nat-val 0
`zero .realises γ η α ⋆ α⇒1 .steps = 5
`zero .realises γ η α ⋆ α⇒1 .result-potential = α
`zero .realises γ η α ⋆ α⇒1 .evaluation =
  seq true (seq mkunit (mkpair (suc zero) zero))
`zero .realises γ η α ⋆ α⇒1 .result-realises =
  refl , α⇒1
`zero .realises γ η α ⋆ α⇒1 .accounted = acct⊕-

`succ : ℕ ⊢ ◇ ⊗ `nat ⇒ ⟨ suc ⟩ `nat
`succ .realiser .expr _ =
   seq false then
   letpair suc zero then
   (suc (suc zero) , zero)
`succ .realiser .potential = acct 4
`succ .realiser .potential-ok = `acct
`succ .realises n η α (⋆ , nv) (α₁ , α₂ , α-α₁α₂ , α₁-1 , refl , α₂-Sn) = is-realisable
  where
  is-realisable : Eval _ _ _ _
  is-realisable .result = false , nv
  is-realisable .steps = 4
  is-realisable .result-potential = α
  is-realisable .evaluation =
    seq false (letpair (suc zero) (mkpair (suc (suc zero)) zero))
  is-realisable .result-realises =
    refl ,
    (α-α₁α₂ ； pair α₁-1 ； pair' α₂-Sn ； symmetry ； suc-size (suc n))
  is-realisable .accounted = acct⊕-

body-expr : (z s : ∀ n → exp (1 + n)) → ∀ n → exp (3 + n)
body-expr z s n =
   letpair zero then
   cond suc zero then z (4 + n)
                 else (seq (suc (suc (suc zero)) · zero) then
                       seq ⋆ then
                       seq (suc zero , zero) then
                       s (7 + n))

rec-expr : (z s : ∀ n → exp (1 + n)) → ∀ n → exp (suc n)
rec-expr z s n = seq (ƛ (body-expr z s n)) then (zero · suc zero)

recursor : ∀ {Γ X} →
           Γ ⊢ ◇ ⇒ ⟨ κ zero ⟩ X →
           (Γ × ℕ) ⊢ (X ⊗ ◇) ⇒ ⟨ κ-map suc ⟩ X →
           (Γ × ℕ) ⊢ ⟨ proj₂ ⟩ `nat ⇒ X
recursor z s .realiser .expr = rec-expr (z .realiser .expr) (s .realiser .expr)
recursor z s .realiser .potential = acct 3 ⊕ raise (acct 8 ⊕ s .realiser .potential) ⊕ (acct 2 ⊕ z .realiser .potential)
recursor z s .realiser .potential-ok = (`acct `⊕ raise-ok (`acct `⊕ s .realiser .potential-ok)) `⊕ (`acct `⊕ z .realiser .potential-ok)
recursor{Γ}{X} z s .realises (γ , n) {n₀} η α v (refl , d) = is-realisable
  where
    η₀ = η ,- v
    η₁ = η₀ ,- clo (body-expr (z .realiser .expr) (s .realiser .expr) n₀) η₀

    loop-potential : ℕ → |M|
    loop-potential n = size (suc n) ⊕ scale n (acct 8 ⊕ s .realiser .potential) ⊕ (acct 2 ⊕ z .realiser .potential)

    loop : (n : ℕ) → Eval (X (γ , n)) (body-expr (z .realiser .expr) (s .realiser .expr) n₀) (loop-potential n) (η₁ ,- nat-val n)
    loop zero = is-realisable
      where
        r = z .realises γ (η₁ ,- _ ,- _) (size 1) ⋆ (identity {size 1})

        is-realisable : Eval _ _ _ _
        is-realisable .result = r .result
        is-realisable .steps = 2 + r .steps
        is-realisable .result-potential = r .result-potential
        is-realisable .evaluation = letpair zero (cond-true (suc zero) (r .evaluation))
        is-realisable .result-realises = r .result-realises
        is-realisable .accounted =
          pair (pair' (scale-zero (acct 8 ⊕ s .realiser .potential))) ；
          pair unit ；
          assoc ；
          pair symmetry ；
          assoc-inv ；
          acct⊕- ；
          symmetry ；
          r .accounted
    loop (suc n) = is-realisable
      where
        r-n = loop n
        r-s = s .realises (γ , n) (η₁ ,- _ ,- _ ,- _ ,- _ ,- _) (r-n .result-potential ⊕ size 1) (r-n .result , ⋆)
                    (r-n .result-potential , size 1 , identity , r-n .result-realises , identity)

        is-realisable : Eval _ _ _ _
        is-realisable .result = r-s .result
        is-realisable .steps = 3 + r-n .steps + 1 + (2 + (2 + r-s .steps))
        is-realisable .result-potential = r-s .result-potential
        is-realisable .evaluation =
          letpair zero (cond-false (suc zero)
                        (seq (app (suc (suc (suc zero))) zero (r-n .evaluation))
                        (seq mkunit
                        (seq (mkpair (suc zero) zero) (r-s .evaluation)))))
        is-realisable .result-realises = r-s .result-realises
        is-realisable .accounted =
          weaken (pair (pair' (scale-suc n (acct 8 ⊕ s .realiser .potential) (`acct `⊕ s .realiser .potential-ok))) ；
                  pair (pair (size-suc (suc n))) ；
                  assoc-inv ；
                  pair' assoc-inv ；
                  assoc ；
                  pair assoc-inv ；
                  pair symmetry ；
                  assoc-inv ；
                  pair' (assoc ； r-n .accounted) ；
                  pair symmetry ；
                  assoc-inv ；
                  assoc-inv ；
                  acct⊕- ；
                  pair' symmetry ；
                  r-s .accounted)
            (begin
              3 + r-n .steps + 1 + (2 + (2 + r-s .steps))
            ≡⟨ solve 2 (λ x y →  con 3 :+ x :+ con 1 :+ (con 2 :+ (con 2 :+ y))
                               := x :+ con 0 :+ con 0 :+ con 0 :+ con 8 :+ con 0 :+ y) refl (r-n .steps) (r-s .steps) ⟩
              r-n .steps + 0 + 0 + 0 + 8 + 0 + r-s .steps
            ∎)
          where open ≤-Reasoning
                open import Data.Nat.Solver
                open +-*-Solver

    is-realisable : Eval _ _ _ _
    is-realisable .result = loop n .result
    is-realisable .steps = 3 + loop n .steps
    is-realisable .result-potential = loop n .result-potential
    is-realisable .evaluation = seq lam (app zero (suc zero) (loop n .evaluation))
    is-realisable .result-realises = loop n .result-realises
    is-realisable .accounted =
      pair' d ；
      assoc-inv ；
      assoc-inv ；
      acct⊕- ；
      pair' symmetry ；
      assoc ；
      pair (pair' (size-suc n)) ；
      pair assoc ；
      pair (pair (raise→scale (acct 8 ⊕ s .realiser .potential) n)) ；
      pair assoc-inv ；
      pair (pair' (suc-size n)) ；
      pair symmetry ；
      loop n .accounted
