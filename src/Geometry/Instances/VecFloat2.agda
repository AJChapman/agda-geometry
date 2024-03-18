module Geometry.Instances.VecFloat2 where

open import Level

open import Data.Float using (Float; _+_; _*_; _-_; sqrt)
open import Geometry.Structures {0ℓ} using (Geometry)
open import Data.Vec.Functional using (Vector; zipWith; foldr)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  Point : Set
  Point = Vector Float 2

  Distance : Set
  Distance = Float

  distance : Point → Point → Distance
  distance a b =
    let sqrdiffs = zipWith (λ a b → sqr (b - a)) a b
        sumsqrdiffs = foldr _+_ 0.0 sqrdiffs
    in sqrt sumsqrdiffs
    where
      sqr : Float → Float
      sqr x = x * x

  -- TODO
  postulate
    distance-comm : (a b : Point) → distance a b ≡ distance b a

  -- TODO
  postulate
    +-comm : (x y : Float) → x + y ≡ y + x

instance
  VecFloat2Geometry : Geometry
  VecFloat2Geometry = record
    { Point = Point
    ; Distance = Distance
    ; _⊢⊣_ = distance
    ; ⊢⊣-comm = distance-comm
    ; _+_ = _+_
    ; +-comm = +-comm
    }
