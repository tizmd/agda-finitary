module Data.Finitary.FinType where
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Data.Nat as ℕ
open import Data.Fin as Fin using (Fin; #_)
open import Data.Finitary
open import Function.Equality using (_⟨$⟩_)
open import Function.Injection as Inj using (Injective)
open import Function.Inverse as Inv using (Inverse)
open import Data.Vec
open import Data.Vec.Membership.Propositional
open import Data.Vec.Membership.Propositional.Properties
open import Data.Vec.Membership.Propositional.Distinct as Distinct using (Distinct)

record FinType {a} (A : Set a) : Set a where
  field
    size : ℕ
    finitary : Finitary (P.setoid A) size
  open import Data.Vec.Properties   
  
  index  : A → Fin size
  index  = Inverse.to finitary ⟨$⟩_

  index-injective : ∀ {x y} → index x ≡ index y → x ≡ y
  index-injective = Inverse.injective finitary

  enum  : Fin size → A
  enum = Inverse.from finitary ⟨$⟩_

  enum-injective : ∀ {i j} → enum i ≡ enum j → i ≡ j
  enum-injective = Inverse.injective (Inv.sym finitary)

  elems : Vec A size
  elems = tabulate enum  

  elems-distinct : Distinct elems
  elems-distinct = Distinct.tabulate (Inverse.injection (Inv.sym finitary))

  _∈elems : ∀ x → x ∈ elems
  x ∈elems rewrite P.sym (Inverse.left-inverse-of finitary x) = ∈-tabulate⁺ enum (index x)
  
open FinType ⦃ ... ⦄ using (index ; _∈elems)

size : ∀ {a} (A : Set a) ⦃ fin : FinType A ⦄ → ℕ
size A {{ fin }} = FinType.size fin 

elems : ∀ {a} (A : Set a) ⦃ fin : FinType A ⦄ → Vec A (size A)
elems A {{ fin }} = FinType.elems fin

instance
  open import Data.Bool
  open import Data.Unit
  open import Data.Empty
  empty   : FinType ⊥
  empty = record {
            size = 0
          ; finitary = record {
              to = P.→-to-⟶ λ()
            ; from = P.→-to-⟶ λ()
            ; inverse-of = record {
              left-inverse-of = λ ()
            ; right-inverse-of = λ ()
            }
            }
          }

  
  unit   : FinType ⊤
  unit   = record {
          size = 1
        ; finitary = record {
          to = P.→-to-⟶ λ _ → Fin.zero
        ; from = P.→-to-⟶ λ _ → tt
        ; inverse-of = record {
           left-inverse-of = λ _ → P.refl
         ; right-inverse-of = λ { Fin.zero → P.refl ; (Fin.suc ()) }
        }
        }
        }

  bool    : FinType Bool
  bool    = record {
          size = 2
        ; finitary = record {
            to = P.→-to-⟶ λ { false → # 0 ; true → # 1 }
          ; from = P.→-to-⟶ λ { Fin.zero → false ; (Fin.suc Fin.zero) → true ; (Fin.suc (Fin.suc ())) }
          ; inverse-of = record {
            left-inverse-of = λ { false → P.refl ; true → P.refl }
          ; right-inverse-of = λ { Fin.zero → P.refl ; (Fin.suc Fin.zero) → P.refl ; (Fin.suc (Fin.suc ())) }
          }
          }
          }
private          
  bools : Vec Bool _
  bools = elems Bool  

  example : bools ≡ false ∷ true ∷ []
  example = P.refl
