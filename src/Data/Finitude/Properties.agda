module Data.Finitude.Properties where
open import Data.Fin as Fin using (Fin; #_ )
open import Data.Fin.Properties hiding (decSetoid)
open import Relation.Nullary
open import Relation.Unary 
open import Relation.Binary renaming (Decidable to Dec₂) hiding (Irrelevant)
open import Relation.Binary.PropositionalEquality as P hiding (decSetoid; isEquivalence)
open import Data.Finitude
open import Function.Equality as F using (_⟨$⟩_) 
open import Function.Inverse as Inv using (Inverse)
open import Data.Nat as ℕ hiding (_≟_)
import Level

finitude→≡ : ∀ {n m} → Finitude (P.setoid (Fin n)) m → n ≡ m
finitude→≡ fin = ⇒Fin∼Fin fin
  where
    open import Data.Fin.PigeonHole 

dec-≈ : ∀ {a ℓ n}{S : Setoid a ℓ} → Finitude S n → Dec₂ (Setoid._≈_ S)
dec-≈ {S = S} fin x y with (Inverse.to fin ⟨$⟩ x) ≟ (Inverse.to fin ⟨$⟩ y)
dec-≈ {S = S} fin x y | yes fx≡fy = yes (Inverse.injective fin fx≡fy)
dec-≈ {S = S} fin x y | no fx≢fy = no (λ x≈y → fx≢fy (F.cong (Inverse.to fin) x≈y))

decSetoid : ∀ {a ℓ n}{S : Setoid a ℓ} → Finitude S n → DecSetoid a ℓ
decSetoid {S = S} fin = record {
          isDecEquivalence = record {
            _≟_ = dec-≈ fin
          ; isEquivalence = isEquivalence
          }   
          }
          where open Setoid S
          
same-size↔  : ∀ {n a₁ a₂ ℓ₁ ℓ₂}{A₁ : Setoid a₁ ℓ₁}{A₂ : Setoid a₂ ℓ₂} → Finitude A₁ n → Finitude A₂ n → Inverse A₁ A₂
same-size↔ fin₁ fin₂ = Inv.sym fin₂ Inv.∘  fin₁ 

size-unique : ∀ {a ℓ} {A : Setoid a ℓ} {n m} → Finitude A n → Finitude A m → n ≡ m
size-unique finN finM = finitude→≡ (finM Inv.∘ Inv.sym finN)

{-
open import Data.Empty
open import Data.Unit

Irr : ∀ {a ℓ}(S : Setoid a ℓ) → Set (a Level.⊔ ℓ)
Irr S = ∀ x y → x ≈ y
  where
    open Setoid S 


⊥-Irr : Irrelevant ⊥
⊥-Irr = λ ()

⊤-Irr : Irrelevant ⊤
⊤-Irr = λ _ _ → P.refl

Irr-finitude : ∀ {a ℓ n}{S : Set a} → Irrelevant S → Finitude (P.setoid S) n → n ℕ.≤ 1
Irr-finitude {n = ℕ.zero} irr fin = z≤n
Irr-finitude {n = ℕ.suc ℕ.zero} irr fin = s≤s z≤n
Irr-finitude {n = ℕ.suc (ℕ.suc n)}{S} irr fin = ⊥-elim contra
   where
     open Setoid S
     x₀ = Inverse.from fin ⟨$⟩ # 0
     x₁ = Inverse.from fin ⟨$⟩ # 1

     contra : ⊥
     contra with Inverse.injective (Inv.sym fin) (irr x₀ x₁)
     ... | ()
-}
