module Data.Finitary.Permutation where

open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)
open import Function.Inverse as Inv using (Inverse)
import Function.Equality as F
open import Function.LeftInverse using (_LeftInverseOf_)
open import Data.Finitary
open import Data.Vec as Vec using (Vec)
open import Data.Vec.Distinct as Distinct using (Distinct)
open import Data.Product hiding (swap)

Permutation : ℕ → Set
Permutation n = Finitary (P.setoid (Fin n)) n

identity : ∀ {n} → Permutation n
identity = Inv.id

swap : ∀ {n} → Fin n → Fin n → Permutation n
swap {n} i j = record {
         to = P.→-to-⟶ swap′ 
       ; from = P.→-to-⟶ swap′
       ; inverse-of = record {
           left-inverse-of = swap′-involutive
         ; right-inverse-of = swap′-involutive
           }
         }
         where
           open import Data.Fin.Properties as FinP
           open import Relation.Nullary
           open import Data.Empty using (⊥-elim)
           swap′ : Fin n → Fin n
           swap′ k with k FinP.≟ i
           swap′ k | yes k≡i = j
           swap′ k | no ¬p with k FinP.≟ j
           swap′ k | no ¬p | yes k≡j = i
           swap′ k | no ¬p | no ¬p₁ = k
     
           swap′-involutive : ∀ k → swap′ (swap′ k) ≡ k
           swap′-involutive k with k FinP.≟ i
           swap′-involutive k | yes k≡i with k≡i | j FinP.≟ i 
           swap′-involutive _ | yes k≡i | P.refl | yes j≡i = j≡i
           swap′-involutive _ | yes k≡i | P.refl | no j≢i with j FinP.≟ j
           swap′-involutive _ | yes k≡i | P.refl | no j≢i | yes j≡j = P.refl
           swap′-involutive _ | yes k≡i | P.refl | no j≢i | no j≢j = ⊥-elim (j≢j P.refl)
           swap′-involutive k | no k≢i with k FinP.≟ j
           swap′-involutive k | no k≢i | yes k≡j with k≡j | i FinP.≟ i
           swap′-involutive k | no k≢i | yes k≡j | P.refl | yes P.refl = P.refl
           swap′-involutive k | no k≢i | yes k≡j | P.refl | no i≢i = ⊥-elim (i≢i P.refl)
           swap′-involutive k | no k≢i | no k≢j = lemma k≢i k≢j
             where
               open P.≡-Reasoning 
               lemma : ∀ {k} → k ≢ i → k ≢ j → swap′ k ≡ k 
               lemma {k} k≢i k≢j with k FinP.≟ i 
               lemma k≢i k≢j | yes k≡i  = ⊥-elim (k≢i k≡i)
               lemma {k} k≢i k≢j | no ¬k≡i with k FinP.≟ j
               lemma {k} k≢i k≢j | no ¬k≡i | yes k≡j = ⊥-elim (k≢j k≡j)
               lemma {k} k≢i k≢j | no ¬k≡i | no ¬p = P.refl
    
shift : ∀ {n} → Permutation n → Permutation (ℕ.suc n)
shift {n} p = record {
         to = P.→-to-⟶ (shift′ Perm.to)
       ; from = P.→-to-⟶ (shift′ Perm.from)
       ; inverse-of = record {
           left-inverse-of = shift′-inverse-of Perm.left-inverse-of
         ; right-inverse-of = shift′-inverse-of Perm.right-inverse-of
       }
    }
    where  
      module Perm = Inverse p
      shift′ : P.setoid (Fin n) F.⟶ P.setoid (Fin n) → Fin (ℕ.suc n) → Fin (ℕ.suc n)
      shift′ f Fin.zero = Fin.zero
      shift′ f (Fin.suc i) = Fin.suc (f F.⟨$⟩ i)
      shift′-inverse-of : ∀ {from : P.setoid (Fin n) F.⟶ P.setoid (Fin n)}{to : P.setoid (Fin n) F.⟶ P.setoid (Fin n)} → from LeftInverseOf to → (P.→-to-⟶ (shift′ from)) LeftInverseOf (P.→-to-⟶ (shift′ to))
      shift′-inverse-of inv Fin.zero = P.refl
      shift′-inverse-of inv (Fin.suc i) = P.cong Fin.suc (inv i)
    

Perm→Distinct : ∀ {n} → Permutation n → ∃ λ (xs : Vec (Fin n) n) → Distinct xs
Perm→Distinct {n} p = , xs-distinct
  where
    open Inverse p renaming (to to f)
    open import Data.Vec.Properties

    xs-distinct : Distinct (Vec.tabulate (f F.⟨$⟩_)) 
    xs-distinct = P.subst Distinct (P.sym (tabulate-allFin _))
                  (Distinct.map injection (Distinct.allFin n))

