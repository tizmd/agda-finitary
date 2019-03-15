{-# OPTIONS --safe --without-K #-}
module Data.Fin.Subset.Properties.Dec where

open import Data.Nat as ℕ 
open import Data.Fin as Fin
open import Data.Empty using (⊥-elim)
open import Data.Fin.Subset
open import Data.Fin.Subset.Dec
open import Data.Fin.Subset.Properties using (⊆⊤; p⊆p∪q; q⊆p∪q ; p∩q⊆p ; p∩q⊆q ; ⊆-poset)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Unary renaming (Decidable to Decidable₁) using ()
open import Data.Vec
open import Function using (_∘_)
open import Function.Equivalence using (_⇔_ ; equivalence)
open import Relation.Nullary.Negation using (¬?)
  
subset¬⊆∁subset : ∀ {n}{p} {P : Fin n → Set p}(P? : Decidable₁ P) → subset (¬? ∘ P?) ⊆ ∁ (subset P?)
subset¬⊆∁subset {zero} P? ()
subset¬⊆∁subset {suc n} P? x∈s with P? (# 0)
subset¬⊆∁subset {suc n} P? here | no ¬p0 = here
subset¬⊆∁subset {suc n} P? (there x∈s) | no ¬p0 = there (subset¬⊆∁subset (P? ∘ suc) x∈s)
subset¬⊆∁subset {suc n} P? (there x∈s) | yes p0 = there (subset¬⊆∁subset (P? ∘ suc) x∈s)

∁subset⊆subset¬ : ∀ {n}{p}{P : Fin n → Set p}(P? : Decidable₁ P) →  ∁ (subset P?) ⊆ subset (¬? ∘ P?)
∁subset⊆subset¬  {zero} P? ()
∁subset⊆subset¬ {suc n} P? x∈s with P? (# 0)
∁subset⊆subset¬ {suc n} P? here | no ¬p0 = here
∁subset⊆subset¬ {suc n} P? (there x∈s) | yes p0 = there (∁subset⊆subset¬ (P? ∘ suc) x∈s) 
∁subset⊆subset¬ {suc n} P? (there x∈s) | no ¬p0 = there (∁subset⊆subset¬ (P? ∘ suc) x∈s)

subset¬≡∁subset  : ∀ {n}{p}{P : Fin n → Set p}(P? : Decidable₁ P) → subset (¬? ∘ P?) ≡ ∁ (subset P?)
subset¬≡∁subset {n} P? = ⊆-antisym (subset¬⊆∁subset P?) (∁subset⊆subset¬ P?)
  where
    open Poset (⊆-poset n) renaming (antisym to ⊆-antisym) using () 

      
∈subset⁺ : ∀ {n}{p}{P : Fin n → Set p}(P? : Decidable₁ P){x} → P x → x ∈ subset P? 
∈subset⁺ {zero} P? {()} Px
∈subset⁺ {suc n} P? {x} Px with P? (# 0)
∈subset⁺ {suc n} P? {zero} Px | yes p0 = here
∈subset⁺ {suc n} P? {suc x} Px | yes p0 = there (∈subset⁺ (P? ∘ suc) Px)
∈subset⁺ {suc n} P? {zero} Px | no ¬p0 = ⊥-elim (¬p0 Px)
∈subset⁺ {suc n} P? {suc x} Px | no ¬p0 = there (∈subset⁺ (P? ∘ suc) Px)

∈subset⁻ : ∀ {n}{p} {P : Fin n → Set p}(P? : Decidable₁ P){x} → x ∈ subset P? → P x 
∈subset⁻ {zero} P? {()} x∈s
∈subset⁻ {suc n} P? {x} x∈s with P? (# 0)
∈subset⁻ {suc n} P? {zero} here | yes p0 = p0
∈subset⁻ {suc n} P? {suc x} (there x∈s) | yes p0 = ∈subset⁻ (P? ∘ suc) x∈s 
∈subset⁻ {suc n} P? {.(suc _)} (there x∈s) | no ¬p0 = ∈subset⁻ (P? ∘ suc) x∈s 

⇔∈subset : ∀ {n}{p}{P : Fin n → Set p}(P? : Decidable₁ P) {x} → x ∈ subset P? ⇔ P x  
⇔∈subset P? = equivalence (∈subset⁻ P?) (∈subset⁺ P?)

∈∁subset⁺ : ∀ {n}{p}{P : Fin n → Set p}(P? : Decidable₁ P){x} → ¬ P x → x ∈ ∁ (subset P?) 
∈∁subset⁺ P?  = subset¬⊆∁subset P? ∘ (∈subset⁺ (¬? ∘ P? ))
∈∁subset⁻ : ∀ {n}{p}{P : Fin n → Set p}(P? : Decidable₁ P){x} → x ∈ ∁ (subset P?) → ¬ P x 
∈∁subset⁻ P? = ∈subset⁻ (¬? ∘ P?) ∘ ∁subset⊆subset¬ P?

⇔∈∁subset : ∀ {n}{p}{P : Fin n → Set p}(P? : Decidable₁ P) {x} → x ∈ ∁ (subset P?) ⇔ (¬ P x)  
⇔∈∁subset P? = equivalence (∈∁subset⁻ P?) (∈∁subset⁺ P?)
