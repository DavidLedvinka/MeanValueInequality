module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Int.Star
public import Mathlib.Analysis.Calculus.MeanValue

section polygonal_line

variable {E : Type*} {U : Set E} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : E)
open Set unitInterval

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

structure PolygonalLine (U : Set E) (a b : E) where
  n    : ℕ
  vertice  : Fin (n + 2) → E
  source  : vertice 0 = a
  target  : vertice (Fin.last (n + 1)) = b
  segments : ∀ i : Fin (n + 1), ∀ t ∈ Icc (0 : ℝ) 1,
           (1 - t) • vertice i.castSucc + t • vertice i.succ ∈ U

theorem test {a b} (l : PolygonalLine U a b) (i : Fin (l.n + 1)) :
  MapsTo (AffineMap.lineMap (l.vertice i.castSucc) (l.vertice i.succ))
    (Icc 0 1 : Set ℝ) U := by
    simp[AffineMap.lineMap, MapsTo, - Set.mem_Icc]
    intro t ht
    convert l.segments i t ht using 1
    rw[smul_sub, sub_smul]
    grind [one_smul]



def PolygonalLine.toNat_vertices {a b : E} (l : PolygonalLine U a b) (i : ℕ) : E :=
  if h : i < l.n + 2 then l.vertice ⟨i, h⟩ else b


theorem test2 {a b} (l : PolygonalLine U a b) (i : ℕ) (hi : i < l.n + 1) :
  MapsTo (AffineMap.lineMap (l.toNat_vertices i) (l.toNat_vertices (i + 1)))
    (Icc 0 1 : Set ℝ) U := by
  unfold MapsTo
  have hi1: i < l.n +2 := by
    grind
  simp [PolygonalLine.toNat_vertices, hi1, hi, - Set.mem_Icc]
  --simp [AffineMap.lineMap]
  intro t ht
  apply test l ⟨i, hi⟩ ht




lemma toNat_eq_vertice1 {a b : E} (l : PolygonalLine U a b): l.toNat_vertices 0 = a := by
  have h : 0 < l.n + 2 := by
    grind
  unfold PolygonalLine.toNat_vertices
  simp [h, l.source]

lemma toNat_eq_vertice2 {a b : E} (l : PolygonalLine U a b): l.toNat_vertices (l.n + 1) = b := by
  have h : l.n + 1 < l.n + 2 := by
    grind
  unfold PolygonalLine.toNat_vertices
  simp [h]
  apply l.target

lemma PolygonalLine.ver_mem (p : PolygonalLine U a b) (i : Fin (p.n + 2)) :
    p.vertice i ∈ U := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨h1, h⟩ | h2
  convert (p.segments h1 0)
  simp [h]
  convert (p.segments (Fin.last (p.n)) 1)
  simp [h2]


-- /--A path is piecewise affine if it can be divided into pieces of affine maps.-/
-- structure IsPiecewiseAffine {a b : E} (ϕ : Path a b) : Prop where
--   piecewise_affine : ∃ (n : ℕ+), ∃ (ι : Fin (n + 1) → I), ι 0 = 0 ∧ ι (Fin.last n) = 1 ∧ ∃ l : Fin n → ℝ →ᵃ[ℝ] E, ∀ i : Fin n, ∀ t ∈ Set.Icc (ι ⟨i, by linarith [i.2]⟩) (ι i.succ), ϕ t = (l i) t

-- /--A polygonal line is a path that is piecewise affine.-/
-- @[ext]
-- structure PolygonalLine (a b : E) extends Path a b where
--   piecewise_affine : IsPiecewiseAffine toPath

theorem nonempty_polygonalLine {U : Set E} (hU : IsConnected U) (a b : E) :
    Nonempty (PolygonalLine U a b) := by
  sorry

def PolygonalLine.length {a b : E} (ϕ : PolygonalLine U a b) : ℝ :=
  ∑ i ∈ Set.Icc 1 (Fin.last (ϕ.n + 1)), dist (ϕ.vertice i) (ϕ.vertice (i - 1))

theorem PolygonalLine.length_toNat_vertices {a b : E} (ϕ : PolygonalLine U a b) :
    ϕ.length = ∑ i ∈ Finset.range (ϕ.n + 1), dist (ϕ.toNat_vertices i) (ϕ.toNat_vertices (i + 1)) := by
  sorry

lemma PolygonalLine.zero_le_length {a b : E} (ϕ : PolygonalLine U a b) : 0 ≤ ϕ.length := by
  unfold length
  apply Finset.sum_nonneg
  intro i h
  apply dist_nonneg

noncomputable
def pathDistance {U : Set E} (x y : U) : ℝ :=
  ⨅ l : PolygonalLine U (x : E) (y : E), l.length

lemma PolygonalLine.zero_le_pathDistance {U : Set E} {a b : U}: 0 ≤ pathDistance a b := by
  unfold pathDistance
  apply Real.iInf_nonneg
  intro i
  apply PolygonalLine.zero_le_length

def constantPolygonalLine (x : E) (hu : x ∈ U) : PolygonalLine U x x where
  n := 0
  vertice := fun _ ↦ x
  source := rfl
  target := rfl
  segments := by intros; rw [← add_smul]; simpa

lemma constantPolygonalLine.zero_eq_length {x} (hU : x ∈ U) :
    0 = (constantPolygonalLine x hU).length := by
      unfold PolygonalLine.length
      simp [constantPolygonalLine]

def PolygonalLine.symm {x y : E} (ϕ : PolygonalLine U x y) : PolygonalLine U y x where
  n := ϕ.n
  vertice := fun i ↦ ϕ.vertice (Fin.revPerm i)
  source := ϕ.target
  target := by simp [ϕ.source]
  segments := by
    intro i t trange
    simp [Fin.rev]
    convert (ϕ.segments ⟨ϕ.n - i, by grind⟩ (1 - t) ⟨by linarith [trange.2], by linarith [trange.1]⟩) using 1
    simp; grind

lemma PolygonalLine.length_eq_rev_length {a b : E} (ϕ : PolygonalLine U a b) :
    ϕ.length = ϕ.symm.length := by
      rw [PolygonalLine.length, PolygonalLine.symm, PolygonalLine.length_toNat_vertices]
      simp only [PolygonalLine.toNat_vertices]
      sorry
    --  apply Finset.sum_bijective Fin.revPerm
    --  exact Equiv.bijective Fin.revPerm
    --  intro i; simp [Fin.rev]

noncomputable instance {U : Set E} (hU : IsConnected U) (hU' : IsOpen U) : MetricSpace U where
  dist := pathDistance
  dist_self := by
    intro x
    apply eq_of_le_of_ge
    unfold pathDistance
    · calc
      pathDistance x x ≤ (constantPolygonalLine (x : E) (U := U) (by grind)).length := by
        simp only [pathDistance]
        apply ciInf_le
        refine ⟨0, ?_⟩
        rintro a ⟨l, hl⟩
        simp at hl
        rw [← hl]; exact l.zero_le_length
      _ = 0 := by apply (constantPolygonalLine.zero_eq_length _).symm
    apply PolygonalLine.zero_le_pathDistance
  dist_comm := by
    intro x y
    simp only [pathDistance]
    apply le_antisymm
    have : Nonempty (PolygonalLine U y x) := by sorry
    apply le_ciInf; intro ϕ
    apply le_of_le_of_eq
    apply ciInf_le _ ϕ.symm
    refine ⟨0, ?_⟩
    rintro a ⟨l, hl⟩
    simp at hl; rw [← hl]; exact l.zero_le_length
    exact ϕ.length_eq_rev_length.symm
    have : Nonempty (PolygonalLine U x y) := by sorry
    apply le_ciInf; intro ϕ
    apply le_of_le_of_eq
    apply ciInf_le _ ϕ.symm
    refine ⟨0, ?_⟩
    rintro a ⟨l, hl⟩
    simp at hl; rw [← hl]; exact l.zero_le_length
    exact ϕ.length_eq_rev_length.symm
  eq_of_dist_eq_zero := by
    intro x y hxy
    rw [pathDistance] at hxy
    sorry
    -- epsilon delta definition of infimum
  dist_triangle := sorry

#check IsConnected.isPreconnected
#check connectedSpace_iff_clopen

/--The trivial path from x to itself is a polygonal line.-/
def constantPolygonalLine (x : E) (hu : x ∈ U) : PolygonalLine U x x where
  n := 0
  vertice := fun _ ↦ x
  source := rfl
  target := rfl
  segments := by intros; rw [← add_smul]; simpa

-- def constantPolygonalLine (x : E) : PolygonalLine x x where
--   toFun := fun _ ↦ x
--   source' := rfl
--   target' := rfl
--   piecewise_affine := by
--     use 1; dsimp; refine ⟨by norm_num, ?_⟩; use Fin.cases 0 (fun _ ↦ 1)
--     refine ⟨rfl, rfl, ?_⟩
--     use fun _ ↦ AffineMap.const ℝ ℝ x; intros; dsimp

/--The segment connecting x and y is a polygonal line.-/
def lineSegment (x y : E) (hu : segment ℝ x y ⊆ U) : PolygonalLine U x y where
  n := 0
  vertice := Fin.cases x (fun _ ↦ y)
  source := rfl
  target := rfl
  segments := by
    intro i t trange; rcases i with ⟨i, ieq0⟩
    have : i = 0 := Nat.lt_one_iff.mp ieq0
    simp [this]
    rw [← Fin.succ_zero_eq_one, Fin.cases_succ]
    apply hu
    simp [segment]
    exact ⟨1 - t, by simp [trange.2], t, trange.1, by norm_num, rfl⟩

-- def lineSegment (x y : E) : PolygonalLine x y where
--   toFun := fun ⟨t, _⟩ ↦ t • y + (1 - t) • x
--   source' := by simp
--   target' := by simp
--   piecewise_affine := by
--     use 1
--     refine ⟨by norm_num, ?_⟩
--     use Fin.cases 0 (fun _ ↦ 1)
--     dsimp
--     refine ⟨rfl, rfl, ?_⟩
--     use fun _ ↦ (AffineMap.lineMap x y); intros
--     rw [AffineMap.lineMap]; dsimp; rw [smul_sub, sub_smul, one_smul, add_sub, ← add_sub_right_comm]

-- /--The range of a segment-polygonal-line is a segment.-/
-- lemma segment_range_eq_segment (x y : E) : Set.range (lineSegment x y) = segment ℝ x y := by
--   ext; simp [segment, lineSegment]
--   constructor; rintro ⟨a, ⟨⟨a0, a1⟩, sum_eq⟩⟩; use (1 - a), by linarith, a, a0, by ring_nf
--   rw [← sum_eq]; simp [add_comm]; rfl
--   rintro ⟨b, ⟨bpos, ⟨a, ⟨apos, ⟨sum_eq_1, sum_eq⟩⟩⟩⟩⟩
--   apply eq_sub_of_add_eq at sum_eq_1
--   have : 0 ≤ 1 - a := by
--     rw [sum_eq_1] at bpos; exact bpos
--   use a, ⟨apos, by linarith [bpos]⟩
--   rw [← sum_eq]; rw [add_comm (b • x)]; simp [sum_eq_1]; rfl

noncomputable section

-- /--The head-to-tail composition of two piecewise-affine Paths is piecewise-affine.-/
-- lemma piecewise_affine_trans {x y z : E} {φ : Path x y} {φ' : Path y z} (hφ : IsPiecewiseAffine φ) (hφ' : IsPiecewiseAffine φ') :
--   IsPiecewiseAffine (φ.trans φ') := by
--   rcases hφ with ⟨n₁, ⟨n₁pos,⟨ι₁, ⟨ι₁0, ⟨ι₁n₁, ⟨l₁, h₁⟩⟩⟩⟩⟩⟩
--   rcases hφ' with ⟨n₂, ⟨n₂pos, ⟨ι₂, ⟨ι₂0, ⟨ι₂n₂, ⟨l₂, h₂⟩⟩⟩⟩⟩⟩
--   rw [Path.trans]; use (n₁ + n₂); refine ⟨by linarith, ?_⟩
--   use fun ⟨n, hn⟩ ↦ if h : n ≤ n₁
--     then ⟨↑(ι₁ ⟨n, by omega⟩)/2, ⟨div_nonneg (ι₁ _).2.1 (by norm_num), by field_simp; exact le_trans (ι₁ _).2.2 (by norm_num)⟩⟩
--     else ⟨(↑(ι₂ ⟨n - n₁, by omega⟩) + 1)/2, ⟨div_nonneg (add_nonneg (ι₂ _).2.1 (by norm_num)) (by norm_num), by field_simp; apply add_le_of_le_sub_right; exact le_trans (ι₂ _).2.2 (by norm_num)⟩⟩
--   constructor
--   · simp [ι₁0]
--   constructor
--   · dsimp
--     simp [ne_of_gt n₂pos]; ext; dsimp; field_simp; apply add_eq_of_eq_sub; norm_num
--     exact ι₂n₂
--   use fun ⟨n, hn⟩ ↦ if h : n < n₁ then (l₁ ⟨n, by omega⟩).comp ((2 : ℝ) • LinearMap.id).toAffineMap
--     else (l₂ ⟨n - n₁, by omega⟩).comp ⟨fun x ↦ 2 * x - 1, (2 : ℝ) • LinearMap.id, by intro p v; simp [two_mul, sub_eq_add_neg, mul_add, add_assoc, add_left_comm, add_comm]⟩
--   intros i t trange
--   dsimp; split_ifs with ht hi hi
--   <;> simp <;> dsimp at trange
--   · rw [φ.extend_apply];
--     apply h₁ ⟨i, _⟩ ⟨2 * t, _⟩
--     simp [(le_of_lt hi), hi] at trange; rcases trange with ⟨t₁, t₂⟩
--     constructor
--     · show ↑(ι₁ ⟨↑i, _⟩) ≤ (2 : ℝ) * ↑t
--       change ((ι₁ ⟨↑i, _⟩) : ℝ) / 2 ≤ (t:ℝ) at t₁
--       linarith
--     simp; show (2 : ℝ) * t ≤ ((ι₁ ⟨↑i + 1, _⟩) : ℝ)
--     change (t:ℝ) ≤ ((ι₁ ⟨↑i + 1, _⟩) : ℝ) / 2 at t₂
--     linarith
--     exact ⟨mul_nonneg (by norm_num) t.2.1, by linarith⟩
--   · rcases (eq_or_lt_of_le (ι₂ ⟨↑i - n₁, by omega⟩).2.1) with hi' | hi'
--     · have : (1:ℝ) / 2 ≤ ↑t := by
--         rcases trange with ⟨trange, _⟩
--         rcases (lt_or_eq_of_le (by push Not at hi; exact hi)) with h | h
--         · simp [not_le_of_gt h] at trange;
--           change (((ι₂ ⟨↑i - n₁, _⟩) : ℝ) + 1) / 2 ≤ (t : ℝ) at trange
--           refine le_trans ?_ trange
--           linarith [(ι₂ ⟨↑i - n₁, by omega⟩).2.1]
--         simp [← h] at trange; change ((ι₁ (Fin.last n₁)):ℝ) / 2 ≤ (t : ℝ) at trange
--         rw [ι₁n₁] at trange; exact trange
--       have : (1:ℝ) / 2 = (t : ℝ) := eq_of_le_of_ge this ht
--       rw [φ.extend_apply]; simp [← this]
--       rw [← h₂ ⟨↑i - n₁, by omega⟩ ⟨0, unitInterval.zero_mem⟩]; dsimp
--       rw [φ'.source]
--       refine ⟨?_, unitInterval.nonneg _⟩; simp [hi']
--       exact ⟨mul_nonneg (by norm_num) t.2.1, by rw [← this]; norm_num⟩
--     absurd ht; push Not; push Not at hi
--     have : n₁ < ↑i := by
--       by_contra!; have : n₁ = ↑i := eq_of_ge_of_le this hi
--       have : ((ι₂ ⟨↑i - n₁, by omega⟩) : ℝ) = 0 := by simp [this, ι₂0]
--       rw [this] at hi'; exact (lt_irrefl 0) hi'
--     rcases trange with ⟨trange, _⟩
--     simp [not_le_of_gt this] at trange; change (((ι₂ ⟨↑i - n₁, by omega⟩) : ℝ) + 1) / 2 ≤ (t : ℝ) at trange
--     linarith
--   · exfalso
--     apply ht
--     rcases trange with ⟨_, trange⟩
--     simp [Nat.succ_le_of_lt hi] at trange; change (t : ℝ) ≤ ((ι₁ ⟨↑i + 1, by omega⟩) : ℝ) / 2 at trange
--     linarith [(ι₁ ⟨↑i + 1, by omega⟩).2.2]
--   rw [φ'.extend_apply]
--   apply h₂ ⟨i - n₁, _⟩ ⟨2 * t - 1, _⟩
--   push Not at ht hi
--   show ((2 * t - 1) : ℝ) ∈ Icc ((ι₂ ⟨↑i - n₁, by omega⟩) : ℝ) ((ι₂ ⟨↑i - n₁ + 1, by omega⟩) : ℝ)
--   rcases (eq_or_lt_of_le hi) with hi | hi
--   · simp [le_of_eq hi.symm, not_lt_iff_eq_or_lt.mpr (Or.inl hi.symm)] at trange
--     rcases trange with ⟨_, trange⟩; change (t : ℝ) ≤ (((ι₂ ⟨↑i + 1 - n₁, by omega⟩) : ℝ) + 1) / 2 at trange
--     simp [hi] at trange
--     simp [hi, ι₂0]; exact ⟨by linarith, by linarith⟩
--   simp [not_le_of_gt hi, not_lt_of_gt hi] at trange
--   rcases trange with ⟨t₁, t₂⟩;
--   change (((ι₂ ⟨↑i - n₁, by omega⟩) : ℝ) + 1) / 2 ≤ (t : ℝ) at t₁; change (t : ℝ) ≤ (((ι₂ ⟨↑i + 1 - n₁, by omega⟩) : ℝ) + 1) / 2 at t₂
--   simp [Nat.succ_sub (le_of_lt hi)] at t₂
--   exact ⟨by linarith, by linarith⟩
--   exact ⟨by linarith, by linarith [t.2.2]⟩

-- @[trans]
-- def PolygonalLine.trans {x y z : E} (φ : PolygonalLine x y) (φ' : PolygonalLine y z) : PolygonalLine x z where
--   toFun := (fun t : ℝ => if t ≤ 1 / 2 then φ.extend (2 * t) else φ'.extend (2 * t - 1)) ∘ (↑)
--   continuous_toFun := by
--     refine
--       (Continuous.if_le ?_ ?_ continuous_id continuous_const (by simp)).comp
--         continuous_subtype_val <;>
--     fun_prop
--   source' := by simp
--   target' := by norm_num
--   piecewise_affine := piecewise_affine_trans φ.piecewise_affine φ'.piecewise_affine

@[simp]
def glued_append {m n : ℕ} (f : Fin (n + 2) → E) (g : Fin (m + 2) → E):
    Fin (n + m + 2 + 1) → E := by
  intro i
  by_cases! hi : i.1 ≤ n + 1
  exact (f ⟨i.1, Nat.lt_succ_of_le hi⟩)
  exact (g ⟨i.1 - (n + 1), by omega⟩)

@[trans]
def PolygonalLine.trans {x y z : E} (p : PolygonalLine U x y) (p' : PolygonalLine U y z) : PolygonalLine U x z where
  n := p.n + p'.n + 1
  vertice := glued_append p.vertice p'.vertice
  source := by simp; exact p.source
  target := by simp; convert p'.target using 1; congr; rw [add_assoc]; apply (Nat.add_sub_cancel_left)
  segments := by
    intro i t trange
    dsimp; split_ifs with h1 h2 h2
    · refine (p.segments ⟨i, ?_⟩ t trange)
      omega
    · push Not at h2
      have : p.n + 1 = i := le_antisymm (Nat.le_of_lt_succ h2) h1
      simp [this]; simp [← this]
      show (1 - t) • p.vertice (Fin.last (p.n + 1)) + t • p'.vertice 1 ∈ U
      simp [p.target, ← p'.source]
      exact (p'.segments 0 t trange)
    · linarith
    push Not at h1 h2
    convert (p'.segments ⟨i - (p.n + 1), _⟩ t trange)
    dsimp; omega
    omega

end

-- /--The head-to-tail composition of two polygonal lines contained in a subset is still contained in that subset.-/
-- lemma polygonal_line_trans_subset {x y z : E} {U : Set E} {φ : PolygonalLine x y} {φ' : PolygonalLine y z} (hφ : Set.range ↑φ ⊆ U) (hφ' : Set.range ↑φ' ⊆ U) :
--   Set.range ↑(φ.trans φ') ⊆ U := by
--       rintro w ⟨t, h⟩; simp [PolygonalLine.trans] at h
--       change (ite _ _ _) = w at h; split_ifs at h with range_t
--       · rw [← h]
--         have : φ.extend (2 * ↑t) ∈ range ↑φ := ⟨⟨2 * ↑t, ⟨by linarith [t.2.1], by linarith⟩⟩, by rw [φ.extend_apply ⟨by linarith [t.2.1], by linarith⟩]; rfl⟩
--         exact hφ this
--       rw [← h]
--       have : φ'.extend (2 * ↑t - 1) ∈ range ↑φ' := ⟨⟨2 * ↑t - 1, ⟨by linarith, by linarith [t.2.2]⟩⟩, by rw [φ'.extend_apply ⟨by linarith, by linarith [t.2.2]⟩]; rfl⟩
--       exact hφ' this

/--A subset of a normed vector space is connected by polygonal lines if it is connected.-/
lemma polygonal_connected_of_connected (U : Set E) (Uopen : IsOpen U)  :
    IsConnected U → ∀ x y : E, x ∈ U ∧ y ∈ U → Nonempty (PolygonalLine U x y) := by
  intro Uconnected x y ⟨xu, yu⟩
  have Uconnected : ConnectedSpace U := by
    rw [isConnected_iff_connectedSpace] at Uconnected
    exact Uconnected
  set V : Set E := {u | Nonempty (PolygonalLine U x u)} with V_def
  set V' : Set U := Subtype.val ⁻¹' V with V'_def
  have V'_eq_V : ∀ x : U, x.1 ∈ V ↔ x ∈ V' := by simp [V'_def]
  have : x ∈ V := by
    simp [V_def]
    constructor
    exact constantPolygonalLine x xu
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
      rw [V_def]; dsimp; constructor
      have ball : ∃ ε > 0, Metric.ball a ε ⊆ U := Metric.isOpen_iff.mp Uopen a au
      have : Nonempty (PolygonalLine U x a) := by
        rcases ball with ⟨ε, ⟨εpos, ball⟩⟩
        have : ((Metric.ball a ε) ∩ V).Nonempty := mem_closure_iff.mp aV (Metric.ball a ε) Metric.isOpen_ball (Metric.mem_ball_self εpos)
        rw [Set.nonempty_def] at this
        rcases this with ⟨b, ⟨binball, bV⟩⟩
        have ϕ₁ : PolygonalLine U x b := by rw [V_def] at bV; dsimp at bV; exact Classical.choice bV
        have ϕ₂ : PolygonalLine U b a := by
          refine (lineSegment b a) ?_
          apply subset_trans (convex_iff_segment_subset.mp (convex_ball a ε) binball (Metric.mem_ball_self εpos)) ball
        exact ⟨ϕ₁.trans ϕ₂⟩
      apply Classical.choice this
    apply IsOpen.preimage continuous_subtype_val
    apply Metric.isOpen_iff.mpr
    rintro a aV
    rw [V_def] at aV
    have ϕ : PolygonalLine U x a := Classical.choice aV
    have : ∃ ε > 0, Metric.ball a ε ⊆ U := by
      refine Metric.isOpen_iff.mp Uopen a ?_
      rw [← ϕ.target]; apply ϕ.ver_mem
    rcases this with ⟨ε, ⟨εpos, ballinU⟩⟩
    use ε, εpos; rintro b binball; rw [V_def]
    have : segment ℝ a b ⊆ Metric.ball a ε := by
      apply convex_iff_segment_subset.mp (convex_ball _ _) (Metric.mem_ball_self _) binball
      exact εpos
    have hϕ₂ : segment ℝ a b ⊆ U := by intros x h; apply ballinU; apply this; apply h
    exact ⟨ϕ.trans (lineSegment a b hϕ₂)⟩
  have : V' = Set.univ := by
    rcases ((connectedSpace_iff_clopen.mp Uconnected).2 V' V'clopen)
    · contradiction
    assumption
  have : V = U := by
    ext x₀; constructor
    · rw [V_def]; intro hx₀; apply Classical.choice at hx₀
      rw [← hx₀.target]; apply hx₀.ver_mem
    intro hx₀; rw [V'_eq_V ⟨x₀, hx₀⟩, this]; trivial
  rw [← this, V_def] at yu
  exact yu

-- #check Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le

/-
Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le.{u_1, u_3, u_4} {E : Type u_1}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {𝕜 : Type u_3} {G : Type u_4} [NontriviallyNormedField 𝕜]
  [IsRCLikeNormedField 𝕜] [NormedSpace 𝕜 E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : E → G}
  {C : ℝ} {s : Set E} {x y : E} {f' : E → E →L[𝕜] G} (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
  (bound : ∀ x ∈ s, ‖f' x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s)
  (ys : y ∈ s) : ‖f y - f x‖ ≤ C * ‖y - x‖
-/

/- variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : E) -/

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

#check Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le

lemma sublength_sum_geq_distance (a : ℕ → E) :
  ∀ n : ℕ, ‖a n - a 0‖ ≤ ∑ i ∈ Finset.range n, ‖a (i+1) - a i‖:= by
    intro n
    induction n with
    | zero =>
      simp
    | succ k hk =>
      calc
        ‖a (k + 1) - a 0‖ = ‖(a (k + 1) - a k) + (a k - a 0)‖ := by
          simp
        _ ≤ ‖(a (k + 1) - a k)‖ + ‖(a k - a 0)‖ :=
          norm_add_le _ _
        _ ≤ ‖a (k + 1) - a k‖ + ∑ i ∈ Finset.range k, ‖a (i + 1) - a i‖ :=
          add_le_add_right hk _
        _ = ∑ i ∈ Finset.range (k + 1), ‖a (i + 1) - a i‖ := by
          rw [Finset.sum_range_succ]; rw[add_comm]



theorem norm_image_sub_le_of_norm_hasFDerivWithin_le' {f : E → G} {C : ℝ} {s : Set E} {x y : s}
    {f' : E → E →L[ℝ] G} (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖ ≤ C)
    (hs : IsConnected s) (hs' : IsOpen s) : ‖f y - f x‖ ≤ C * pathDistance y x := by
  simp [pathDistance]
  have hC : 0 ≤ C := by
    apply le_trans
    apply norm_nonneg (f' x)
    apply bound
    simp
  rw[Real.mul_iInf_of_nonneg]
  have : Nonempty (PolygonalLine s y x) :=
    polygonal_connected_of_connected s hs' hs y x (by grind)
  apply le_ciInf
  intro x_1
  nth_rw 1 [← toNat_eq_vertice1 x_1]
  nth_rw 2 [← toNat_eq_vertice2 x_1]
  conv => enter [1, 1, 1]; change (f ∘ x_1.toNat_vertices) _
  conv => enter [1, 1, 2]; change (f ∘ x_1.toNat_vertices) _
  grw [norm_sub_rev, sublength_sum_geq_distance]
  apply le_trans
  apply Finset.sum_le_sum
  intro i hi
  simp
  set g := (AffineMap.lineMap (x_1.toNat_vertices i) (x_1.toNat_vertices (i + 1)) : ℝ → E)
  have segm : MapsTo g (Icc 0 1 : Set ℝ) s := by
    unfold g
    apply test2
    grind

  have hD : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (f ∘ g) (f' (g t) ((x_1.toNat_vertices (i + 1)) - (x_1.toNat_vertices i))) (Icc 0 1) t := fun t ht => by
    simpa using ((hf (g t) (segm ht)).restrictScalars ℝ).comp_hasDerivWithinAt _
      AffineMap.hasDerivWithinAt_lineMap segm
  have bound : ∀ t ∈ Ico (0 : ℝ) 1, ‖f' (g t) ((x_1.toNat_vertices (i + 1)) - (x_1.toNat_vertices i))‖ ≤ C * ‖(x_1.toNat_vertices (i + 1)) - (x_1.toNat_vertices i)‖ := fun t ht =>
    ContinuousLinearMap.le_of_opNorm_le _ (bound _ <| segm <| Ico_subset_Icc_self ht) _
  simpa [g] using norm_image_sub_le_of_norm_deriv_le_segment_01' hD bound
  rw [PolygonalLine.length_toNat_vertices]
  simp[dist_eq_norm, norm_sub_rev]
  rw[Finset.mul_sum]
  exact hC
