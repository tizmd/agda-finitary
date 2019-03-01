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
  
subset¬⊆∁subset : ∀ {n} {P : Fin n → Set}{p : Decidable₁ P} → subset (¬? ∘ p) ⊆ ∁ (subset p)
subset¬⊆∁subset {zero} {p = p} ()
subset¬⊆∁subset {suc n} {p = p} x∈s with p (# 0)
subset¬⊆∁subset {suc n} {p = p} here | no ¬p0 = here
subset¬⊆∁subset {suc n} {p = p} (there x∈s) | no ¬p0 = there (subset¬⊆∁subset {p = p ∘ suc} x∈s)
subset¬⊆∁subset {suc n} {p = p} (there x∈s) | yes p0 = there (subset¬⊆∁subset {p = p ∘ suc} x∈s)

∁subset⊆subset¬ : ∀ {n} {P : Fin n → Set}{p : Decidable₁ P} →  ∁ (subset p) ⊆ subset (¬? ∘ p)
∁subset⊆subset¬  {zero} {p = p} ()
∁subset⊆subset¬ {suc n} {p = p} x∈s with p (# 0)
∁subset⊆subset¬ {suc n} {p = p} here | no ¬p0 = here
∁subset⊆subset¬ {suc n} {p = p} (there x∈s) | yes p0 = there (∁subset⊆subset¬ {p = p ∘ suc} x∈s) 
∁subset⊆subset¬ {suc n} {p = p} (there x∈s) | no ¬p0 = there (∁subset⊆subset¬ {p = p ∘ suc} x∈s)

subset¬≡∁subset  : ∀ {n} {P : Fin n → Set}{p : Decidable₁ P} → subset (¬? ∘ p) ≡ ∁ (subset p)
subset¬≡∁subset {n} = ⊆-antisym subset¬⊆∁subset ∁subset⊆subset¬
  where
    open Poset (⊆-poset n) renaming (antisym to ⊆-antisym) using () 

      
∈subset⁺ : ∀ {n} {P : Fin n → Set}{p :  Decidable₁ P}{x} → P x → x ∈ subset p 
∈subset⁺ {zero} {p = p} {()} Px
∈subset⁺ {suc n} {p = p} {x} Px with p (# 0)
∈subset⁺ {suc n} {p = p} {zero} Px | yes p0 = here
∈subset⁺ {suc n} {p = p} {suc x} Px | yes p0 = there (∈subset⁺ Px)
∈subset⁺ {suc n} {p = p} {zero} Px | no ¬p0 = ⊥-elim (¬p0 Px)
∈subset⁺ {suc n} {p = p} {suc x} Px | no ¬p0 = there (∈subset⁺ Px)

∈subset⁻ : ∀ {n} {P : Fin n → Set}{p :  Decidable₁ P}{x} → x ∈ subset p → P x 
∈subset⁻ {zero} {p = p} {()} x∈s
∈subset⁻ {suc n} {p = p} {x} x∈s with p (# 0)
∈subset⁻ {suc n} {p = p} {zero} here | yes p0 = p0
∈subset⁻ {suc n} {p = p} {suc x} (there x∈s) | yes p0 = ∈subset⁻ {p = p ∘ suc} x∈s 
∈subset⁻ {suc n} {p = p} {.(suc _)} (there x∈s) | no ¬p0 = ∈subset⁻ {p = p ∘ suc} x∈s 

⇔∈subset : ∀ {n} {P : Fin n → Set}{p :  Decidable₁ P} {x} → x ∈ subset p ⇔ P x  
⇔∈subset = equivalence ∈subset⁻ ∈subset⁺

∈∁subset⁺ : ∀ {n} {P : Fin n → Set}{p :  Decidable₁ P}{x} → ¬ P x → x ∈ ∁ (subset p) 
∈∁subset⁺  = subset¬⊆∁subset ∘ ∈subset⁺
∈∁subset⁻ : ∀ {n} {P : Fin n → Set}{p :  Decidable₁ P}{x} → x ∈ ∁ (subset p) → ¬ P x 
∈∁subset⁻ = ∈subset⁻ ∘ ∁subset⊆subset¬ 

⇔∈∁subset : ∀ {n} {P : Fin n → Set}{p :  Decidable₁ P} {x} → x ∈ ∁ (subset p) ⇔ (¬ P x)  
⇔∈∁subset = equivalence ∈∁subset⁻ ∈∁subset⁺
