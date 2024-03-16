module Geometry.Structures {ℓ} where

open import Level

open import Data.Empty.Polymorphic using (⊥)
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_)
open import Data.Unit.Polymorphic using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

Pred : Set ℓ → Set (suc ℓ)
Pred A = A → Set ℓ

-- Geometry as predicates on a point type?
-- Every member of the type is drawn.

record Geometry : Set (suc ℓ) where
  infixl 6 _⊢⊣_
  infixl 5 _+_
  field
    -- A type for points, e.g. ℝ²
    Point : Set ℓ

    -- A type for distances between points
    Distance : Set ℓ

    -- Measure the distance between two points
    _⊢⊣_ : Point → Point → Distance

    -- Add the distance between two points
    _+_ : Distance → Distance → Distance
    +-comm : (a b : Distance) → a + b ≡ b + a

    -- TODO: Angles

  Drawing : Set (suc ℓ)
  Drawing = Pred Point

  -- Is this point in this drawing?
  _∈_ : Point → Drawing → Set _
  p ∈ P = P p

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
  (P ∩ Q) p = P p ⊎ Q p
  infixl 4 _∩_

  -- Both drawings
  _∪_ : Drawing → Drawing → Drawing
  (P ∪ Q) p = P p × Q p
  infixl 4 _∪_

  -- A line from point-to-point (input with \.\em\.)
  _∙—∙_ : Point → Point → Drawing
  (a ∙—∙ b) p = a ⊢⊣ p + b ⊢⊣ p ≡ a ⊢⊣ b
  infixl 5 _∙—∙_

  -- An extension of a line to infinity on the right (doesn't draw between the points, only beyond)
  _∙~∙→_ : Point → Point → Drawing
  (a ∙~∙→ b) p = a ⊢⊣ p ≡ a ⊢⊣ b + b ⊢⊣ p

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
  ⨀ c r p = c ⊢⊣ p ≡ r

  -- A triangle with these three points as vertices
  △ : (a b c : Point) → Drawing
  △ a b c = a ∙—∙ b ∪ b ∙—∙ c ∪ c ∙—∙ a

  -- Drawing equality
  _≐_ : Drawing → Drawing → Set ℓ
  P ≐ Q = ∀ {p} → (P p → Q p) × (Q p → P p)
  infix 4 _≐_

  -- The line from a to b is the same as from b to a
  ∙—∙-comm : (a b : Point) → a ∙—∙ b ≐ b ∙—∙ a
  ∙—∙-comm a b = {!   !}

{-
mk-equilateral-△ : ⦃ Geometry ⦄ → (a b : Point) → _
mk-equilateral-△ a b c =
  let d = distance a b
      c₁ = ⨀ a d
      c₂ = ⨀ b d
      i = c₁ ∩ c₂ -- TODO: work out how to get a Point here (via Decidable -> Dec -> reflects?)
  in △ a b i
    -}

