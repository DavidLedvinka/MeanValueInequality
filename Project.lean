import Mathlib

section polygonal_line

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : E)
open Set

--/-- A line segment in a vector space E can be written as the sum of a linear map and a constant.-/
--@[ext]
--structure LineSegment (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
--  toFun : ℝ → E
--  affine_linearity : ∃ (f : ℝ →ₗ[ℝ] E) (c : E), ∀ x : ℝ, toFun x = f x + c
--
--instance (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : CoeFun (LineSegment E) fun _ ↦ ℝ → E where
--  coe := LineSegment.toFun

--@[ext]
--structure PolygonalLine (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : E) where
--  toFun : ℝ → E
--  /--A polygonal line is a continuous mapping.-/
--  continuity : Continuous toFun
--  path_origin : toFun 0 = a
--  path_end : toFun 1 = b
--  piecewise_segment : ∃ (n : ℕ) (ι : ℕ → ℝ), ι 0 = 0 ∧ ι n = 1 ∧ ∀ i ∈ Finset.range n, ∃ (l : ℕ → LineSegment E), ∀ x ∈ Set.Icc (ι i) (ι (i + 1)), toFun x = (l i) x

#check Path a b
#check AffineMap

/--A path is piecewise affine if it can be divided into pieces of affine maps.-/
structure IsPiecewiseAffine (ϕ : Path a b) : Prop where
  piecewise_affine : ∃ (n : ℕ) (ι : Fin (n + 1) → unitInterval), ι 0 = 0 → ι (Fin.last n) = 1 → ∀ i : Fin n, ∃ (l : Fin n → ℝ →ᵃ[ℝ] E), ∀ x ∈ Set.Icc (ι (Fin.castLE (show n ≤ n + 1 from by linarith) i)) (ι (Fin.castSucc i)), ϕ x = (l i) x

/--A polygonal line is a path that is piecewise affine.-/
structure PolygonalLine (a b : E) extends Path a b where
  piecewise_affine : IsPiecewiseAffine a b toPath

/--A polygonal line behaves like a path, which is a function from the unit interval to the vector space E.-/
instance : CoeFun (PolygonalLine a b) fun _ ↦ unitInterval → E where
  coe := fun ϕ ↦ ϕ.toPath.toFun

#check IsConnected.isPreconnected
#check connectedSpace_iff_clopen

def constant_polygonal_line (x : E) : PolygonalLine x x := by
  constructor
  show Path x x
  use (ContinuousMap.const unitInterval x) <;> dsimp
  constructor
  use 1, Fin.cases 0 (fun _ ↦ 1)
  intros; dsimp
  use fun _ ↦ AffineMap.const ℝ ℝ x; intros; rfl

lemma polygonal_connected_of_connected (U : Set E) (Uopen : IsOpen U)  :
  IsConnected U → ∀ x y : E, x ∈ U → y ∈ U → ∃ ϕ : PolygonalLine x y, Set.range ϕ ⊆ U := by
  intro Uconnected x y xu yu
  have Uconnected : ConnectedSpace U := by
    rw [isConnected_iff_connectedSpace] at Uconnected
    exact Uconnected
  set V : Set E := {u ∈ U | ∃ l : PolygonalLine x u, Set.range l ⊆ U} with V_def
  set V' : Set U := Subtype.val ⁻¹' V with V'_def
  have V'_eq_V : ∀ x : U, x.1 ∈ V ↔ x ∈ V' := by simp [V'_def]
  have : x ∈ V := by
    simp [V_def]
    constructor; exact xu
    use constant_polygonal_line x
    simp [constant_polygonal_line, Set.range]; assumption
  -- have Vnonempty : Nonempty V := by simp; use x
  have V'nonempty : V' ≠ ∅ := by
    rw [V'_eq_V ⟨x, xu⟩] at this
    contrapose! this; rw [this]; exact notMem_empty _
  have V'clopen : IsClopen V' := sorry
  have : V' = Set.univ := by
    rcases ((connectedSpace_iff_clopen.mp Uconnected).2 V' V'clopen)
    · contradiction
    assumption
  have : V = U := by
    ext x₀; constructor
    · rw [V_def]; dsimp; rintro ⟨_, _⟩; assumption
    intro hx₀; rw [V'_eq_V ⟨x₀, hx₀⟩, this]; trivial
  rw [← this, V_def] at yu
  rcases yu; assumption
