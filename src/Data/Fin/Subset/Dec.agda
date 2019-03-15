{-# OPTIONS --safe --without-K #-}

module Data.Fin.Subset.Dec where
open import Data.Nat as ℕ 
open import Data.Fin as Fin
open import Data.Fin.Subset 
open import Relation.Nullary
open import Relation.Unary renaming (Decidable to Decidable₁) using ()
open import Function using (_∘_)
open import Data.Vec using ([]; _∷_)
  
subset : ∀ {n}{p} {P : Fin n → Set p} → Decidable₁ P → Subset n
subset {zero} dec = []
subset {suc n} dec with dec (# 0)
subset {suc n} dec | yes p0 = inside ∷ subset (dec ∘ Fin.suc)
subset {suc n} dec | no ¬p0 = outside ∷ subset (dec ∘ Fin.suc)

