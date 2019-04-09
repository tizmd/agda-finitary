module Data.Finitude where

open import Data.Fin as Fin
open import Data.Nat as ℕ
open import Level

open import Function as Fun hiding (id; _∘_)
open import Function.Equality as F using (_⟨$⟩_)
open import Function.Injection as Inj hiding (id; _∘_)
open import Function.Bijection as Bij hiding (id; _∘_)
open import Function.LeftInverse      hiding (id; _∘_)
open import Function.Inverse   as Inv hiding (id; _∘_)
open import Relation.Binary
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

Finitude : ∀ {a ℓ} (A : Setoid a ℓ) (n : ℕ) → Set _
Finitude A n = Inverse A (P.setoid (Fin n))

module Subset where
  open import Data.Product as Prod hiding (map)
  open import Data.Fin.Subset using (Subset; _∈_; outside; inside; ∣_∣) renaming (⊥ to ∅)
  open import Data.Vec 
  subset-finitude : ∀ {n}(s : Subset n) → Finitude (P.setoid (∃ (_∈ s))) ∣ s ∣
  subset-finitude {ℕ.zero} [] = record {
      to = P.→-to-⟶ (λ ())
    ; from = P.→-to-⟶ (λ () )
    ; inverse-of = record {
        left-inverse-of = λ ()
      ; right-inverse-of = λ ()
      }
    }
  subset-finitude {ℕ.suc n} (inside ∷ s) = record {
        to = P.→-to-⟶ λ { (_ , here) → Fin.zero 
                          ; (_ , there p) → Fin.suc (to ⟨$⟩ (_ , p)) } 
      ; from = P.→-to-⟶ λ { Fin.zero → _ , here
                           ; (Fin.suc i) → _ , there (proj₂ (from ⟨$⟩ i))}
      ; inverse-of = record {
            left-inverse-of = λ { (_ , here) → P.refl
                                 ; (_ , there p) → P.cong
                                   (Prod.map Fin.suc there) (linv (_ , p))}
          ; right-inverse-of = λ { Fin.zero → P.refl
                                 ; (Fin.suc i) → P.cong Fin.suc (rinv i)}
        }
      }
    where
      open Inverse (subset-finitude s) 
      open _InverseOf_ inverse-of renaming (left-inverse-of to linv
                                           ;right-inverse-of to rinv)
      
  subset-finitude {ℕ.suc n} (outside ∷ s) = record {
      to = P.→-to-⟶ (λ { (_ , there p) → to ⟨$⟩ (_ , p)})
    ; from = P.→-to-⟶ (λ i → Prod.map Fin.suc there (from ⟨$⟩ i) )
    ; inverse-of = record {
           left-inverse-of = λ { (_ , there p) →
             P.cong (Prod.map Fin.suc there) (linv (_ , p)) }
         ; right-inverse-of = rinv
      }
    }
      where
        open Inverse (subset-finitude s)
        open _InverseOf_ inverse-of renaming ( left-inverse-of to linv
                                             ; right-inverse-of to rinv)
                                                          
