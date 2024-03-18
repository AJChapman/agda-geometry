module Geometry.Properties {ℓ} where

open import Level

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)
open import Relation.Unary using (Pred; _≐_; _∪_; _∩_)

open import Geometry.Structures {ℓ}

ab→ba : ⦃ _ : Geometry ⦄ → (a b : Point) → {p : Point} → (a ∙—∙ b) p → (b ∙—∙ a) p
ab→ba a b {p} ab = trans (+-comm (b ⊢⊣ p) (a ⊢⊣ p)) (trans ab (⊢⊣-comm a b))

-- The line from a to b is the same as from b to a
∙—∙-comm : ⦃ _ : Geometry ⦄ → (a b : Point) → a ∙—∙ b ≐ b ∙—∙ a
∙—∙-comm a b = (ab→ba a b , ab→ba b a)

