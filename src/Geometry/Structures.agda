module Geometry.Structures where

open import Level

open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic using (⊤)
open import Relation.Unary as P using (Pred; _≐_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Geometry as predicates on a point type?
-- Every member of the type is drawn.

record Geometry {ℓ} : Set (suc ℓ) where
  field
    Point : Set ℓ
    Distance : Set ℓ
    distance : Point → Point → Distance
    _+_ : Distance → Distance → Distance

    -- TODO: Angles

  Drawing : Set (suc ℓ)
  Drawing = Pred Point ℓ

  -- Is this point in this drawing?
  _∈_ : Point → Drawing → Set _
  _∈_ = P._∈_

  -- Empty drawing
  ∅ : Drawing
  ∅ _ = ⊥

  -- Full drawing (some diligent toddler coloured the whole space in!)
  𝟙 : Drawing
  𝟙 _ = ⊤

  -- A single-point drawing
  ∙ : Point → Drawing
  ∙ x = x ≡_

  -- All intersection points of two drawings
  _∩_ : Drawing → Drawing → Drawing
  _∩_ = P._∩_
  infixl 4 _∩_

  -- Both drawings
  _∪_ : Drawing → Drawing → Drawing
  _∪_ = P._∪_
  infixl 4 _∪_

  -- A line from point-to-point (input with \.\em\.)
  _∙—∙_ : Point → Point → Drawing
  (a ∙—∙ b) p = distance a p + distance b p ≡ distance a b
  infixl 5 _∙—∙_

  -- An extension of a line to infinity on the right (doesn't draw between the points, only beyond)
  _∙~∙→_ : Point → Point → Drawing
  (a ∙~∙→ b) p = distance a p ≡ distance a b + distance b p

  -- An extension of a line to infinity on the left (doesn't draw between the points, only beyond)
  _←∙~∙_ : Point → Point → Drawing
  a ←∙~∙ b = b ∙~∙→ a

  -- A line extended to infinity on the right
  _∙—∙→_ : Point → Point → Drawing
  a ∙—∙→ b = a ∙—∙ b ∪ a ∙~∙→ b

  -- A line extended to infinity on the left
  _←∙—∙_ : Point → Point → Drawing
  a ←∙—∙ b = b ∙—∙→ a

  -- A line extended to infinity in both directions
  _←∙—∙→_ : Point → Point → Drawing
  a ←∙—∙→ b = a ←∙~∙ b ∪ a ∙—∙→ b

  -- A circle centred on a point with a radius
  ⨀ : Point → Distance → Drawing
  ⨀ c r p = distance c p ≡ r

  -- A triangle with these three points as vertices
  △ : (a b c : Point) → Drawing
  △ a b c = a ∙—∙ b ∪ b ∙—∙ c ∪ c ∙—∙ a

  -- The line from a to b is the same as from b to a
  -- ∙—∙-comm : (a b : Point) → a ∙—∙ b ≐ b ∙—∙ a
  -- ∙—∙-comm a b = {!   !}

{-
mk-equilateral-△ : ⦃ Geometry ⦄ → (a b : Point) → _
mk-equilateral-△ a b c =
  let d = distance a b
      c₁ = ⨀ a d
      c₂ = ⨀ b d
      i = c₁ ∩ c₂ -- TODO: work out how to get a Point here (via Decidable -> Dec -> reflects?)
  in △ a b i
    -}

