module Geometry.Constructions {ℓ} where

open import Level

open import Geometry.Structures {ℓ}

equilateral-third-point : ⦃ Geometry ⦄ → (a b : Point) → Point
  let d = a ⊢⊣ b
      c₁ = ⨀ a d
      c₂ = ⨀ b d
  in c₁ ∩ c₂ -- TODO: work out how to get a Point here (via Decidable -> Dec -> reflects?)

equilateral-△ : ⦃ Geometry ⦄ → (a b : Point) → Drawing
equilateral-△ a b c = △ a b (equilateral-third-point a b)
