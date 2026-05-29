import Mathlib

section polygonal_line

/-- A line segment in a vector space E can be written as the sum of a linear map and a constant.-/
@[ext]
structure LineSegment (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  affine_linearity : ∃ (f : ℝ →ₗ[ℝ] E) (c : E), ∀ x : ℝ, toFun x = f x + c

instance (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : CoeFun (LineSegment E) fun _ ↦ ℝ → E where
  coe := LineSegment.toFun

@[ext]
structure PolygonalLine (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : E) where
  toFun : ℝ → E
  continuity : Continuous toFun
  path_origin : toFun 0 = a
  path_end : toFun 1 = b
  piecewise_segment : ∃ (n : ℕ) (ι : ℕ → ℝ), ι 0 = 0 ∧ ι n = 1 ∧ ∀ i ∈ Finset.range n, ∃ (l : ℕ → LineSegment E), ∀ x ∈ Set.Icc (ι i) (ι (i + 1)), toFun x = (l i) x
