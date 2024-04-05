open import Algebra.Bundles using (Monoid; Ring; Semiring)

-- We assume each dimension is the same ring,
-- and what we're using for dimensions won't change, so we
-- parameterise the whole module by dimension.
module Geometry.Nested {a ℓ} (dimension : Ring a ℓ) where

open import Level
open import Level.Literals

open import Data.Bool using (Bool; _∧_; true; if_then_else_)
open import Data.Nat as ℕ using (ℕ; _⊔′_; _+_; _≡ᵇ_)
open import Data.Nat.Binary.Subtraction using (_∸_)
open import Data.Rational using (ℚ)
open import Data.Vec.Functional using (Vector; _∷_; []; foldr; drop)
open import Function using (_∘_)

-- What do we make geometries out of? Other geometries?
-- What then are the ground-level building blocks,
-- and how do we combine them?

-- Maybe we want to allow different dimensions?
-- Is that a starting point?
-- A point is 0-dimensional so can be embedded in any higher geometric space.
-- A line is 1-dimensional, plane 2-dimensional, etc.

private
  variable
    n m : ℕ
    A : Set a

open Ring dimension using () renaming (Carrier to C; 0# to c0; _≈_ to _≡ᶜ_)

Coord : ℕ → Set a
Coord n = Vector C n

Angle : Set
Angle = ℚ

Geometry : Set a → ℕ → Set a
Geometry A n = Coord n → A

pure : A → Geometry A n
pure x = λ _ → x

-- Anything in here requires that values at least be monoidal
module Empty {monoid : Monoid a ℓ} where
  open Monoid monoid using (ε) renaming (Carrier to M)

  -- Create an empty space of this many dimensions
  empty : Geometry M n
  empty = pure ε

  0-space : Geometry M 0
  0-space = empty

  1-space : Geometry M 1
  1-space = empty

  2-space : Geometry M 2
  2-space = empty

  3-space : Geometry M 3
  3-space = empty

  4-space : Geometry M 4
  4-space = empty

  -- Ensure the given Geometry has at least n dimensions,
  -- creating some if necessary and placing the geometry's
  -- origin at the new dimension's origin.
  liftD : {n m : ℕ} → {n ℕ.≤ m} → Geometry A n → Geometry A m
  -- liftD {ℕ.zero} {ℕ.zero} a = a
  -- To lift e.g. a Geometry A 1 to a Geometry A 3, it changes from (Vector C 1 → A) to (Vector C 3 → A),
  -- or to (λ (x ∷ y ∷ z ∷ []) → if (y == c0 && z == c0) then (a (x ∷ [])) else ε
  -- To lift Geometry A 0 to Geometry A (suc m), we don't want to recurse; we want to say that if all the
  -- remaining coordinates are c0 then we should return a, otherwise empty.
  -- To lift Geometry A 2 to Geometry A 2, we remove the first two coordinates, then if the rest (none) are all c0 (they are) we return a else empty
  -- To lift Geometry A 2 to Geometry A 3, we remove the first two coordinates, then if the rest are all c0 then return a else empty
  liftD {n} {m} a cs = if (all (_≡ᶜ c0) (drop (m ∸ n) cs)) then a else empty
    where
      all : {b : Level} {o : ℕ} {B : Set b} → (B → Bool) → Vector B o → Bool
      all f = foldr (λ x b → b ∧ f x) true


module Full (x : A) where
  -- Create a geometry filling this many dimensions.
  -- Filling 0 dimensions is a point,
  -- filling 1 dimension is an infinite line,
  -- filling 2 dimensions is an infinite plane,
  -- filling 3 dimensions is an infinite solid,
  -- and so on.
  full : Geometry A n
  full = pure

  point : Geometry A 0 -- Create a point
  point = full

  line : Geometry A 1 -- Create a line, extending infinitely in both directions
  line = full

  plane : Geometry A 2 -- Create an infine plane
  plane = full

  solid : Geometry A 3 -- Create an infinite solid
  solid = full


-- Join these two geometries at their origins.
-- E.g. `join point 1-space` puts a point at the origin
-- in a fresh new 1-space.
-- join : Geometry A n → Geometry A m → Geometry A (n ⊔′ m)
-- join a b = λ c → -- TODO: lift the lower-dimensioned geometry, call both, then use monoid to merge values

-- Connect two geometries together,
-- E.g. connect two points with a line,
-- connect a point and a line to make a filled triangle (or just extend the line if the point is in line with it)
-- connect two lines to make a 2D surface
-- connect : Geometry A n → Geometry A m → Geometry A (ℕ.suc (n ⊔′ m))

-- rotate : Vec Angle n → Geometry n  

