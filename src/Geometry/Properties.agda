module Geometry.Properties {ℓ} where

open import Level

open import Data.Product using (_×_; _,_; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)
open import Relation.Unary using (Pred; _≐_; _∪_; _∩_)

open import Geometry.Structures {ℓ}

ab→ba : ⦃ _ : Geometry ⦄ → (a b : Point) → {p : Point} → (a ∙—∙ b) p → (b ∙—∙ a) p
ab→ba a b {p} ab = trans (+-comm (b ⊢⊣ p) (a ⊢⊣ p)) (trans ab (⊢⊣-comm a b))

-- The line from a to b is the same as from b to a
∙—∙-comm : ⦃ _ : Geometry ⦄ → (a b : Point) → a ∙—∙ b ≐ b ∙—∙ a
∙—∙-comm a b = (ab→ba a b , ab→ba b a)

-- TODO: cases for circles:

-- Circles identical

-- Circles coincide, one fully within the other

-- ⨀-fully-within
--   : ⦃ _ : Geometry ⦄
--   → (c₁ c₂ : Point)
--   → (r₁ r₂ : Distance)
--   → Set ℓ
-- ⨀-fully-within c₁ c₂ r₁ r₂ = c₁ ⊢⊣ c₂ + r₁ < r₂

-- Circles touch, one within the other

⨀-touch-from-within
  : ⦃ _ : Geometry ⦄
  → (c₁ c₂ : Point)
  → (r₁ r₂ : Distance)
  → Set ℓ
⨀-touch-from-within c₁ c₂ r₁ r₂ = c₁ ⊢⊣ c₂ + r₁ ≡ r₂

-- Circles overlap, intersecting at two points

-- Circles touch when the distance between their centres
-- equals the sum of their radii
⨀-touch : ⦃ _ : Geometry ⦄
        → (c₁ c₂ : Point)
        → (r₁ r₂ : Distance)
        → Set ℓ
⨀-touch c₁ c₂ r₁ r₂ = c₁ ⊢⊣ c₂ ≡ r₁ + r₂

-- Circles intersect at a single point
⨀-one-∩ : ⦃ _ : Geometry ⦄
        → (c₁ c₂ : Point)
        → (r₁ r₂ : Distance)
        → Set ℓ
⨀-one-∩ c₁ c₂ r₁ r₂ =
  ∃ λ p →
    (∙ p ≡ ⨀ c₁ r₁ ∩ ⨀ c₂ r₂)
    × (c₁ ⊢⊣ p ≡ r₁)
    × (c₂ ⊢⊣ p ≡ r₂)

-- Circles touch when they intersect at a single point
⨀-touch-one-∩ : ⦃ _ : Geometry ⦄
              → (c₁ c₂ : Point)
              → (r₁ r₂ : Distance)
              → Set ℓ
⨀-touch-one-∩ c₁ c₂ r₁ r₂ = ⨀-touch c₁ c₂ r₁ r₂ ≐ ⨀-one-∩ c₁ c₂ r₁ r₂

-- Circles are separate


Equilateral : ⦃ Geometry ⦄ → (a b c : Point) → Set ℓ
Equilateral a b c = a ⊢⊣ b ≡ b ⊢⊣ c × a ⊢⊣ b ≡ a ⊢⊣ c

-- equilateral-△-sides-equal : ⦃ Geometry ⦄ → equilateral-△ (a b : Point) → Set ℓ
-- equilateral-△-sides-equal a b c = △ a b c × (∃ λ d → a ⊢⊣ b ≡ d × b ⊢⊣ c ≡ d × c ⊢⊣ a ≡ d)
