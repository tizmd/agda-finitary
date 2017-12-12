module Data.Fin.PigeonHole where

open import Data.Fin as Fin
open import Data.Fin.Properties
open import Data.Product hiding (swap)
open import Relation.Nullary
import Data.Nat as ℕ
import Data.Nat.Properties as ℕ
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; _≢_)
open import Function.Equality as Fun
open import Function.Injection renaming (_∘_ to _⟨∘⟩_)
open import Function.LeftInverse hiding (id ; _∘_ )  
open import Function.Surjection  hiding (id ; _∘_ )  
open import Function.Related
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim; ⊥)

inj→≤ : ∀ {n m} → (Fin n ↣ Fin m) → n ℕ.≤ m 
inj→≤ {n}{m} f = ℕ.≮⇒≥ (contra f)
  where
    inject≤I : ∀ {m n} → m ℕ.≤ n → (Fin m ↣ Fin n)
    inject≤I m≤n  = record {
                           to = PropEq.→-to-⟶ (λ i → inject≤ i m≤n )
                          ; injective = injective m≤n
                          }
            where
              injective : ∀ {n m} → (m≤n  : m ℕ.≤ n) → ∀ {i j} → inject≤ i m≤n ≡ inject≤ j m≤n → i ≡ j
              injective (ℕ.s≤s m≤n) {zero} {zero} PropEq.refl = PropEq.refl
              injective (ℕ.s≤s m≤n) {zero} {suc j} ()
              injective (ℕ.s≤s m≤n) {suc i} {zero} ()
              injective (ℕ.s≤s m≤n) {suc i} {suc j} feq = PropEq.cong suc (injective m≤n (suc-injective feq))

    contra₁ : ∀ {m} → (Fin (ℕ.suc m) ↣ Fin m) → ⊥
    contra₁ {m = ℕ.zero} f with Injection.to f ⟨$⟩ # 0
    contra₁ {ℕ.zero} f | () 
    contra₁ {m = ℕ.suc m} f = contra₁ h
      where
        k : Fin (ℕ.suc m) 
        k = Injection.to f ⟨$⟩ # 0

        sucI : Fin (ℕ.suc m) ↣ Fin (ℕ.suc (ℕ.suc m))
        sucI = record {
               to = PropEq.→-to-⟶ suc 
             ; injective = suc-injective
          }

        g : Fin (ℕ.suc m) ↣ Fin (ℕ.suc m)
        g = f ⟨∘⟩ sucI

        k≢g : ∀ (i : Fin (ℕ.suc m)) → k ≢ Injection.to g ⟨$⟩ i
        k≢g i = contraposition (Injection.injective f) λ ()
          where
            open import Relation.Nullary.Negation
            
        h : Fin (ℕ.suc m) ↣ Fin m
        h = record {
            to = PropEq.→-to-⟶ to
          ; injective = to-injective
          }
          where
            to : Fin (ℕ.suc m) → Fin m
            to i = punchOut (k≢g i) 

            to-injective :  ∀ {i j} → to i ≡ to j → i ≡ j
            to-injective {i}{j} eq = Injection.injective g
              (punchOut-injective (k≢g i) (k≢g j) eq)
            
    contra : ∀ {n m} → (Fin n ↣ Fin m) → n ℕ.≯ m 
    contra {ℕ.zero} {m} f ()
    contra {ℕ.suc n} {ℕ.zero} f n>m with Injection.to f ⟨$⟩ # 0
    contra {ℕ.suc n} {ℕ.zero} f n>m | ()
    contra {ℕ.suc n} {ℕ.suc m} f n>m = contra₁ (f ⟨∘⟩ inject≤I n>m) 


FinRelated : ∀ {n m k} → Fin n ∼[ k ] Fin m → Set
FinRelated {n} {m} {implication} f = ⊤
FinRelated {n} {m} {reverse-implication} f = ⊤
FinRelated {n} {m} {equivalence} f = ⊤
FinRelated {n} {m} {injection} f = n ℕ.≤ m
FinRelated {n} {m} {reverse-injection} f = n ℕ.≥ m
FinRelated {n} {m} {left-inverse} f = n ℕ.≤ m
FinRelated {n} {m} {surjection} f = n ℕ.≥ m
FinRelated {n} {m} {bijection} f = n ≡ m

⇒Fin∼Fin : ∀ {n m k} (f : Fin n ∼[ k ] Fin m) → FinRelated f
⇒Fin∼Fin {n} {m} {implication} f = tt
⇒Fin∼Fin {n} {m} {reverse-implication} f = tt
⇒Fin∼Fin {n} {m} {equivalence} f = tt
⇒Fin∼Fin {n} {m} {injection} f = inj→≤ f
⇒Fin∼Fin {n} {m} {reverse-injection} f = inj→≤ (app-↢ f)
⇒Fin∼Fin {n} {m} {left-inverse} f = inj→≤ (LeftInverse.injection f)
⇒Fin∼Fin {n} {m} {surjection} f = inj→≤ (Surjection.injection f)
⇒Fin∼Fin {n} {m} {bijection} f = ℕ.≤-antisym (inj→≤ (↔⇒ f))
                                             (inj→≤ (app-↢ (↔⇒ f)))

                       


