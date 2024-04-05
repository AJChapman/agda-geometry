open import Algebra.Bundles using (Ring)

module Geometry.NDimensional.Spec {a ℓ} (dimension : Ring a ℓ) where

open import Level

open import Data.Empty.Polymorphic using (⊥)
open import Data.Nat as ℕ using (ℕ; _⊔′_; _+_; _≡ᵇ_)
open import Data.Product using (_×_)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Vec.Functional using (Vector)
open import Relation.Unary using (Pred)

private
  variable
    n m : ℕ
    A : Set a

open Ring dimension using () renaming (Carrier to C; 0# to c0; _≈_ to _≡ᶜ_)

Coord : ℕ → Set a
Coord n = Vector C n

Geometry : ℕ → Set (a ⊔ suc ℓ)
Geometry n = Pred (Coord n) ℓ

∅ : Geometry n
∅ c = ⊥

U : Geometry n
U c = ⊤

′ : {n : ℕ} → Coord n → Geometry n
′ c c′ = c′ ≡ᶜ c

_∙_ : A → Geometry n
(s ∙ P) c = s × P c
