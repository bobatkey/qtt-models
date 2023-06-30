{-# OPTIONS --safe #-}

module MachineModel where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)

data exp : ℕ → Set where
  `_  : ∀{n} → Fin n → exp n
  ƛ   : ∀{n} → exp (2 + n) → exp n
  _·_ : ∀{n} → Fin n → Fin n → exp n
  -- pairs
  ⋆   : ∀{n} → exp n
  _,_ : ∀{n} → Fin n → Fin n → exp n
  letpair_then_ : ∀ {n} → Fin n → exp (2 + n) → exp n
  -- booleans
  true false      : ∀{n} → exp n
  cond_then_else_ : ∀{n} → Fin n → exp n → exp n → exp n
  -- sequencing
  seq_then_ : ∀{n} → exp n → exp (suc n) → exp n

mutual
  data val : Set where
    ⋆   : val
    _,_ : val → val → val
    true false : val
    clo : ∀{n} → exp (2 + n) → env n → val

  data env : ℕ → Set where
    nil  : env 0
    _,-_ : ∀{n} → env n → val → env (suc n)

nat-val : ℕ → val
nat-val zero    = true , ⋆
nat-val (suc n) = false , nat-val n

infixl 10 _,-_

data _,_⇓v_ : ∀{n} → Fin n → env n → val → Set where
  zero : ∀ {n V}     {η : env n} →               zero  , (η ,- V) ⇓v V
  suc  : ∀ {n i V V'}{η : env n} → i , η ⇓v V → suc i , (η ,- V') ⇓v V

data _,_⇓[_]_ : ∀{n} → exp n → env n → ℕ → val → Set where
  access : ∀{n i v}{η : env n} → i , η ⇓v v → (` i) , η ⇓[ 1 ] v

  lam    : ∀{n E}{η : env n} →
              (ƛ E) , η ⇓[ 1 ] (clo E η)
  app    : ∀{n n' x₁ x₂ E V V' k}{η : env n}{η' : env n'} →
              x₁ , η ⇓v (clo E η') →
              x₂ , η ⇓v V →
              E , (η' ,- clo E η' ,- V) ⇓[ k ] V' →
              (x₁ · x₂) , η ⇓[ 1 + k ] V'

  mkunit : ∀{n}{η : env n} →
              ⋆ , η ⇓[ 1 ] ⋆

  mkpair : ∀{n x₁ x₂ V₁ V₂}{η : env n} →
              x₁ , η ⇓v V₁ →
              x₂ , η ⇓v V₂ →
              (x₁ , x₂) , η ⇓[ 1 ] (V₁ , V₂)

  letpair  : ∀{n x E V₁ V₂ V' k}{η : env n} →
              x , η ⇓v (V₁ , V₂) →
              E , (η ,- V₁ ,- V₂) ⇓[ k ] V' →
              (letpair x then E) , η ⇓[ 1 + k ] V'

  true   : ∀{n}{η : env n} →
              true , η ⇓[ 1 ] true
  false  : ∀{n}{η : env n} →
              false , η ⇓[ 1 ] false

  cond-true : ∀{n x E₁ E₂ V k}{η : env n} →
              x , η ⇓v true →
              E₁ , η ⇓[ k ] V →
              (cond x then E₁ else E₂) , η ⇓[ 1 + k ] V
  cond-false : ∀{n x E₁ E₂ V k}{η : env n} →
              x , η ⇓v false →
              E₂ , η ⇓[ k ] V →
              (cond x then E₁ else E₂) , η ⇓[ 1 + k ] V

  seq   : ∀{n E₁ E₂ V V' k₁ k₂}{η : env n} →
              E₁ , η ⇓[ k₁ ] V →
              E₂ , (η ,- V) ⇓[ k₂ ] V' →
              (seq E₁ then E₂) , η ⇓[ k₁ + 1 + k₂ ] V'
