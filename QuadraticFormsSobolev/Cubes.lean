/-
Definition 2.5 (cubes) of Bux–Kassmann–Schulze, the comparison between the
Euclidean and the maximum norm, and Lemma 2.7 in the concrete form stated in the
paper.
-/
import QuadraticFormsSobolev.Defs

open Real Set Metric Finset

namespace QFS

variable {d : ℕ}

/-- The maximum norm `‖x‖_∞` on `ℝ^d`, used in Definition 2.5. -/
noncomputable def infNorm (x : EuclideanSpace ℝ (Fin d)) : ℝ := ⨆ i, |x i|

lemma infNorm_nonneg (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ infNorm x := by
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · simp [infNorm, Real.iSup_of_isEmpty]
  · exact le_ciSup_of_le (Finite.bddAbove_range _) (Classical.arbitrary _) (abs_nonneg _)

lemma le_infNorm (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |x i| ≤ infNorm x := by
  unfold infNorm
  exact le_ciSup (f := fun j => |x j|) (Finite.bddAbove_range _) i

lemma infNorm_le {x : EuclideanSpace ℝ (Fin d)} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, |x i| ≤ c) : infNorm x ≤ c := by
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · simpa [infNorm, Real.iSup_of_isEmpty] using hc
  · exact ciSup_le h

/-- Each coordinate is dominated by the Euclidean norm. -/
lemma abs_coord_le_norm (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |x i| ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq]
  have h1 : ‖x i‖ ^ 2 ≤ ∑ j, ‖x j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
  have h2 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (norm_nonneg _), Real.norm_eq_abs] at h2

/-- The maximum norm is dominated by the Euclidean norm: `|v|_∞ ≤ |v|`.
This is the left half of equation (3.1) in the proof of Lemma 3.4. -/
lemma infNorm_le_norm (x : EuclideanSpace ℝ (Fin d)) : infNorm x ≤ ‖x‖ :=
  infNorm_le (norm_nonneg _) (fun i => abs_coord_le_norm x i)

/-- The Euclidean norm is dominated by `√d` times the maximum norm:
`|v| ≤ √d |v|_∞`. This is the right half of equation (3.1). -/
lemma norm_le_sqrt_dim_mul_infNorm (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ ≤ Real.sqrt d * infNorm x := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i, ‖x i‖ ^ 2 ≤ (d : ℝ) * infNorm x ^ 2 := by
    calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin d, infNorm x ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have h1 : ‖x i‖ ≤ infNorm x := by simpa [Real.norm_eq_abs] using le_infNorm x i
          exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = (d : ℝ) * infNorm x ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
  calc Real.sqrt (∑ i, ‖x i‖ ^ 2) ≤ Real.sqrt ((d : ℝ) * infNorm x ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * infNorm x := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (infNorm_nonneg x)]

/-- `‖·‖_∞` is symmetric under negation. -/
@[simp] lemma infNorm_neg (x : EuclideanSpace ℝ (Fin d)) : infNorm (-x) = infNorm x := by
  simp [infNorm]

/-- The triangle inequality for `‖·‖_∞`. -/
lemma infNorm_add_le (x y : EuclideanSpace ℝ (Fin d)) :
    infNorm (x + y) ≤ infNorm x + infNorm y := by
  refine infNorm_le (add_nonneg (infNorm_nonneg x) (infNorm_nonneg y)) (fun i => ?_)
  have h1 : |(x + y) i| = |x i + y i| := by simp
  rw [h1]
  exact (abs_add_le _ _).trans (add_le_add (le_infNorm x i) (le_infNorm y i))

/-- On a nonempty index set the supremum defining `‖·‖_∞` is attained. -/
lemma exists_infNorm_eq [Nonempty (Fin d)] (x : EuclideanSpace ℝ (Fin d)) :
    ∃ i, infNorm x = |x i| := by
  obtain ⟨i₀, -, hi₀⟩ :=
    Finset.exists_max_image Finset.univ (fun i => |x i|)
      ⟨Classical.arbitrary _, Finset.mem_univ _⟩
  exact ⟨i₀, le_antisymm (infNorm_le (abs_nonneg _) (fun i => hi₀ i (Finset.mem_univ i)))
    (le_infNorm x i₀)⟩

/-! ## Definition 2.5: cubes -/

/-- The open cube `A_h(u)` with centre `u` and side length `h` (Definition 2.5). -/
def cube (h : ℝ) (u : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | infNorm (x - u) < h / 2}

/-- The half-closed cube `Ã_h(u) = ∏ [u_i − h/2, u_i + h/2)` (Definition 2.5). -/
def halfClosedCube (h : ℝ) (u : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, x i ∈ Ico (u i - h / 2) (u i + h / 2)}

lemma mem_cube_iff {h : ℝ} {u x : EuclideanSpace ℝ (Fin d)} :
    x ∈ cube h u ↔ infNorm (x - u) < h / 2 := Iff.rfl

lemma mem_cube_of_forall {h : ℝ} {u x : EuclideanSpace ℝ (Fin d)} (hh : 0 < h)
    (hlt : ∀ i, |x i - u i| < h / 2) : x ∈ cube h u := by
  rw [mem_cube_iff]
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · simpa [infNorm, Real.iSup_of_isEmpty] using by linarith
  · obtain ⟨i₀, -, hi₀⟩ :=
      Finset.exists_max_image Finset.univ (fun i => |(x - u) i|)
        ⟨Classical.arbitrary _, Finset.mem_univ _⟩
    have hle : infNorm (x - u) ≤ |(x - u) i₀| :=
      infNorm_le (abs_nonneg _) (fun i => hi₀ i (Finset.mem_univ i))
    refine lt_of_le_of_lt hle ?_
    simpa using hlt i₀

lemma abs_sub_lt_of_mem_cube {h : ℝ} {u x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ cube h u) (i : Fin d) : |x i - u i| < h / 2 := by
  have := le_infNorm (x - u) i
  have h2 : |(x - u) i| = |x i - u i| := by simp
  rw [h2] at this
  exact lt_of_le_of_lt this hx

/-- `A_h(x) ⊆ B̄_{(h/2)√d}(x)`: the observation closing the proof of Lemma 2.7. -/
lemma cube_subset_closedBall {h : ℝ} (u : EuclideanSpace ℝ (Fin d)) :
    cube h u ⊆ closedBall u (h / 2 * Real.sqrt d) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  calc ‖x - u‖ ≤ Real.sqrt d * infNorm (x - u) := norm_le_sqrt_dim_mul_infNorm _
    _ ≤ Real.sqrt d * (h / 2) := by
        exact mul_le_mul_of_nonneg_left (le_of_lt hx) (Real.sqrt_nonneg _)
    _ = h / 2 * Real.sqrt d := by ring

/-! ## Lemma 2.7 -/

/-- **Lemma 2.7** of Bux–Kassmann–Schulze. For each `x` and each `ξ ∈ A_h(x)`,
`V_{h√d}[ξ] ⊆ V_{(h/2)√d}[x] ⊆ V[ξ]`.

The paper states this for a cone `V`; its proof uses nothing about `V`, and we
record the general version. -/
theorem cone_in_intersection (V : Set (EuclideanSpace ℝ (Fin d))) {h : ℝ} (hh : 0 ≤ h)
    (x : EuclideanSpace ℝ (Fin d)) {ξ : EuclideanSpace ℝ (Fin d)} (hξ : ξ ∈ cube h x) :
    shift (shrink V (h * Real.sqrt d)) ξ ⊆ shift (shrink V (h / 2 * Real.sqrt d)) x ∧
      shift (shrink V (h / 2 * Real.sqrt d)) x ⊆ shift V ξ := by
  have hℓ : (0 : ℝ) ≤ h / 2 * Real.sqrt d := by positivity
  have hnorm : ‖ξ - x‖ ≤ h / 2 * Real.sqrt d := by
    have := cube_subset_closedBall x hξ
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have h2 : 2 * (h / 2 * Real.sqrt d) = h * Real.sqrt d := by ring
  have := shift_shrink_sandwich V hℓ x hnorm
  rwa [h2] at this

/-- **Lemma 2.7**, "in other words": the union/intersection form. -/
theorem cone_in_intersection' (V : Set (EuclideanSpace ℝ (Fin d))) {h : ℝ} (hh : 0 ≤ h)
    (x : EuclideanSpace ℝ (Fin d)) :
    (⋃ ξ ∈ cube h x, shift (shrink V (h * Real.sqrt d)) ξ)
        ⊆ shift (shrink V (h / 2 * Real.sqrt d)) x ∧
      shift (shrink V (h / 2 * Real.sqrt d)) x ⊆ ⋂ ξ ∈ cube h x, shift V ξ := by
  constructor
  · refine Set.iUnion₂_subset (fun ξ hξ => ?_)
    exact (cone_in_intersection V hh x hξ).1
  · refine Set.subset_iInter₂ (fun ξ hξ => ?_)
    exact (cone_in_intersection V hh x hξ).2


/-- The *closed* cube `Ā_ℓ(u) = {y : ‖y − u‖_∞ ≤ ℓ/2}`.

Section 5.2 of the paper "recalls" the cube notation with a non-strict
inequality, whereas Definition 2.5 defines `A_h(u)` with a strict one. The two
sections therefore use different sets; we keep both, and the results of Section
5.2 are proved for the closed cube, as stated there. -/
def closedCube (h : ℝ) (u : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | infNorm (x - u) ≤ h / 2}

lemma cube_subset_closedCube (h : ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    cube h u ⊆ closedCube h u := by
  intro x hx
  rw [mem_cube_iff] at hx
  exact le_of_lt hx

/-- `Ā_ℓ(u) ⊆ B̄_{(ℓ/2)√d}(u)`. -/
lemma closedCube_subset_closedBall {h : ℝ} (_hh : 0 ≤ h) (u : EuclideanSpace ℝ (Fin d)) :
    closedCube h u ⊆ closedBall u (h / 2 * Real.sqrt d) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  calc ‖x - u‖ ≤ Real.sqrt d * infNorm (x - u) := norm_le_sqrt_dim_mul_infNorm _
    _ ≤ Real.sqrt d * (h / 2) := mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg _)
    _ = h / 2 * Real.sqrt d := by ring

end QFS
