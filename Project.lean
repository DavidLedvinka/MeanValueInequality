import Mathlib

section polygonal_line

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b c: E)
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
  piecewise_affine : ∃ (n : ℕ) (ι : Fin (n + 1) → unitInterval), ι 0 = 0 → ι (Fin.last n) = 1 → ∃ l : Fin n → ℝ →ᵃ[ℝ] E, ∀ i : Fin n, ∀ x ∈ Set.Icc (ι (Fin.castLE (show n ≤ n + 1 from by linarith) i)) (ι (Fin.castSucc i)), ϕ x = (l i) x

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

def line_segment (x y : E) : PolygonalLine x y := by
  constructor
  show Path x y
  have : Continuous (fun t : unitInterval ↦ t.1 • y + (1 - t.1) • x) := by
    refine Continuous.add ?_ ? _
    exact continuous_subtype_val.smul continuous_const
    exact (continuous_const.sub continuous_subtype_val).smul continuous_const
  use ⟨fun ⟨t, _⟩ ↦ t • y + (1 - t) • x, this⟩ <;> dsimp; simp
  simp
  dsimp; use 1, Fin.cases 0 (fun _ ↦ 1)
  dsimp; intros
  use fun _ ↦ (AffineMap.lineMap x y); intros
  rw [AffineMap.lineMap]; dsimp; rw [smul_sub, sub_smul, one_smul, add_sub, ← add_sub_right_comm]

lemma segment_range_eq_segment (x y : E) : Set.range (line_segment x y) = segment ℝ x y := by
  ext; simp [segment, line_segment]
  constructor; rintro ⟨a, ⟨⟨a0, a1⟩, sum_eq⟩⟩; use (1 - a), by linarith, a, a0, by ring_nf
  rw [← sum_eq]; simp [add_comm]
  rintro ⟨a, ⟨a0, ⟨b, ⟨b0, ⟨sum, sum_eq⟩⟩⟩⟩⟩; use b
  constructor; constructor; exact b0; linarith
  rw [← sum_eq, add_comm]; simp [← sum]


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
  have V'clopen : IsClopen V' := by
    constructor
    · apply closure_subset_iff_isClosed.mp
      rintro ⟨a, au⟩ aV'
      have aV : a ∈ closure V := by
        apply map_mem_closure continuous_subtype_val aV'
        rintro v vv
        apply (V'_eq_V v).mpr; assumption
      apply (V'_eq_V ⟨a, au⟩).mp
      rw [V_def]; dsimp; constructor; exact au
      have ball : ∃ ε > 0, Metric.ball a ε ⊆ U := Metric.isOpen_iff.mp Uopen a au
      rcases ball with ⟨ε, ⟨εpos, ball⟩⟩
      have : ((Metric.ball a ε) ∩ V).Nonempty := mem_closure_iff.mp aV (Metric.ball a ε) Metric.isOpen_ball (Metric.mem_ball_self εpos)
      rw [Set.nonempty_def] at this
      rcases this with ⟨b, ⟨binball, bV⟩⟩
      have polygonalpath₁ : ∃ ϕ₁ : PolygonalLine x b, Set.range ϕ₁ ⊆ U := by rw [V_def] at bV; dsimp at bV; exact bV.2
      have polygonalpath₂ : ∃ ϕ₂ : PolygonalLine b a, Set.range ϕ₂ ⊆ U := by
        use line_segment b a
        rw [segment_range_eq_segment b a]
        apply subset_trans (convex_iff_segment_subset.mp (convex_ball a ε) binball (Metric.mem_ball_self εpos)) ball
      rcases polygonalpath₁ with ⟨ϕ₁, hϕ₁⟩
      rcases polygonalpath₂ with ⟨ϕ₂, hϕ₂⟩
      sorry
    apply IsOpen.preimage continuous_subtype_val
    apply Metric.isOpen_iff.mpr
    rintro a aV
    sorry
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
