/-
Lemma 7.2 of Bux–Kassmann–Schulze: a Lebesgue differentiation theorem along
cubes.

  *Let `φ : ℝ^d → ℝ` be locally integrable. For almost every `s`: if `(x_h)_{h>0}`
  is a sequence in `hℤ^d` with `s ∈ Ã_h(x_h)` for every `h`, then*
  `λ_d(A_h(x_h))^{-1} ∫_{A_h(x_h)} φ → φ(s)` *as `h → 0`.*

The cubes are not centred at `s`, so this is not the plain differentiation
theorem for balls; but a cube of side `h` containing `s` sits inside
`B̄_{h√d}(s)` and has volume `h^d`, a fixed fraction of that ball's volume, so
the cubes form a Vitali family and Mathlib's `VitaliFamily.ae_tendsto_average`
applies. Nothing here needs the cubes to be centred at lattice points, so the
statement is proved for arbitrary centres.
-/
import QuadraticFormsSobolev.Section3

open Real Set Metric MeasureTheory ENNReal Filter Topology
open scoped NNReal

namespace QFS

variable {d : ℕ}

/-! ## Cubes are closed, and open cubes are open -/

lemma continuous_coord (i : Fin d) :
    Continuous (fun x : EuclideanSpace ℝ (Fin d) => x i) := by
  refine LipschitzWith.continuous (K := 1) (fun x y => ?_)
  rw [edist_dist, edist_dist, ENNReal.coe_one, one_mul]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.dist_eq, dist_eq_norm]
  have h := abs_coord_le_norm (x - y) i
  have he : (x - y) i = x i - y i := by simp
  rw [he] at h
  exact h

lemma closedCube_eq_iInter {h : ℝ} (hh : 0 ≤ h) (u : EuclideanSpace ℝ (Fin d)) :
    closedCube h u = ⋂ i, (fun x : EuclideanSpace ℝ (Fin d) => x i) ⁻¹'
      (Icc (u i - h / 2) (u i + h / 2)) := by
  rw [closedCube_eq_preimage hh]
  ext x
  simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]

lemma cube_eq_iInter {h : ℝ} (hh : 0 < h) (u : EuclideanSpace ℝ (Fin d)) :
    cube h u = ⋂ i, (fun x : EuclideanSpace ℝ (Fin d) => x i) ⁻¹'
      (Ioo (u i - h / 2) (u i + h / 2)) := by
  rw [cube_eq_preimage hh]
  ext x
  simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]

lemma isClosed_closedCube {h : ℝ} (hh : 0 ≤ h) (u : EuclideanSpace ℝ (Fin d)) :
    IsClosed (closedCube h u) := by
  rw [closedCube_eq_iInter hh]
  exact isClosed_iInter (fun i => isClosed_Icc.preimage (continuous_coord i))

lemma isOpen_cube {h : ℝ} (hh : 0 < h) (u : EuclideanSpace ℝ (Fin d)) :
    IsOpen (cube h u) := by
  rw [cube_eq_iInter hh]
  exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (continuous_coord i))

lemma mem_cube_self {h : ℝ} (hh : 0 < h) (u : EuclideanSpace ℝ (Fin d)) :
    u ∈ cube h u := by
  have he : infNorm (u - u) = 0 := by
    rw [sub_self]
    simp [infNorm]
  simp only [cube, Set.mem_ofPred_eq, he]
  linarith

/-- A cube of side `h` containing `x` lies in the ball of radius `h√d` about
`x`. -/
lemma closedCube_subset_closedBall_of_mem {h : ℝ} {u x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ closedCube h u) : closedCube h u ⊆ closedBall x (h * Real.sqrt d) := by
  intro y hy
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h1 : infNorm (y - u) ≤ h / 2 := hy
  have h2 : infNorm (x - u) ≤ h / 2 := hx
  have h3 : infNorm (y - x) ≤ h := by
    have he : y - x = (y - u) + (u - x) := by abel
    have h4 : infNorm (u - x) = infNorm (x - u) := infNorm_sub_comm _ _
    calc infNorm (y - x) ≤ infNorm (y - u) + infNorm (u - x) := by
          rw [he]; exact infNorm_add_le _ _
      _ ≤ h := by rw [h4]; linarith
  calc ‖y - x‖ ≤ Real.sqrt d * infNorm (y - x) := norm_le_sqrt_dim_mul_infNorm _
    _ ≤ Real.sqrt d * h := mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
    _ = h * Real.sqrt d := by ring

/-! ## The Vitali family of cubes -/

/-- The volume of the unit ball of `ℝ^d`. -/
noncomputable def unitBallVol (d : ℕ) : ℝ≥0∞ :=
  volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)

lemma unitBallVol_ne_top : unitBallVol d ≠ ⊤ := measure_closedBall_lt_top.ne

lemma volume_closedBall_eq (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall x r) = ENNReal.ofReal (r ^ d) * unitBallVol d := by
  rw [unitBallVol, Measure.addHaar_closedBall' volume x hr, finrank_euclideanSpace_fin]

/-- The doubling constant of the Vitali family of cubes: big enough both for the
doubling condition on balls and for a cube of side `h` to fill a fixed fraction
of the ball of radius `3h√d`. -/
noncomputable def cubeVitaliConst (d : ℕ) : ℝ≥0 :=
  (3 : ℝ≥0) ^ d + Real.toNNReal ((3 * Real.sqrt d) ^ d) * (unitBallVol d).toNNReal

lemma cubeVitali_doubling (x : EuclideanSpace ℝ (Fin d)) :
    ∃ᶠ r in 𝓝[>] (0:ℝ), volume (closedBall x (3 * r))
      ≤ cubeVitaliConst d * volume (closedBall x r) := by
  refine Filter.Eventually.frequently ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : (0:ℝ) < r := hr
  rw [volume_closedBall_eq x (by positivity), volume_closedBall_eq x hr0.le,
    show (3 * r) ^ d = 3 ^ d * r ^ d by ring,
    ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 3 ^ d)]
  have hc : ENNReal.ofReal ((3:ℝ) ^ d) ≤ ((cubeVitaliConst d : ℝ≥0) : ℝ≥0∞) := by
    have h1 : ENNReal.ofReal ((3:ℝ) ^ d) = (((3:ℝ≥0) ^ d : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_pow]
      rw [show ((3:ℝ) ^ d) = ((3:ℝ) ^ d) from rfl, ENNReal.ofReal_pow (by norm_num)]
      congr 1
      simp [ENNReal.ofReal]
    rw [h1]
    simp only [cubeVitaliConst]
    exact ENNReal.coe_le_coe.mpr le_self_add
  calc ENNReal.ofReal ((3:ℝ) ^ d) * ENNReal.ofReal (r ^ d) * unitBallVol d
      = ENNReal.ofReal ((3:ℝ) ^ d) * (ENNReal.ofReal (r ^ d) * unitBallVol d) := by ring
    _ ≤ ((cubeVitaliConst d : ℝ≥0) : ℝ≥0∞) * (ENNReal.ofReal (r ^ d) * unitBallVol d) :=
        mul_le_mul' hc le_rfl

/-- The Vitali family in which the closed cubes live. -/
noncomputable def cubeVitali (d : ℕ) :
    VitaliFamily (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  Vitali.vitaliFamily volume (cubeVitaliConst d) cubeVitali_doubling

lemma closedCube_mem_setsAt {h : ℝ} (hh : 0 < h) {u x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ closedCube h u) : closedCube h u ∈ (cubeVitali d).setsAt x := by
  refine ⟨isClosed_closedCube hh.le u, ⟨u, ?_⟩, h * Real.sqrt d,
    closedCube_subset_closedBall_of_mem hx, ?_⟩
  · exact ((isOpen_cube hh u).subset_interior_iff.mpr (cube_subset_closedCube h u))
      (mem_cube_self hh u)
  · have hsd : (0:ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
    rw [volume_closedBall_eq x (by positivity), volume_closedCube hh.le,
      show (3 * (h * Real.sqrt d)) ^ d = (3 * Real.sqrt d) ^ d * h ^ d by ring,
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (3 * Real.sqrt d) ^ d)]
    have hc : ENNReal.ofReal ((3 * Real.sqrt d) ^ d) * unitBallVol d
        ≤ ((cubeVitaliConst d : ℝ≥0) : ℝ≥0∞) := by
      have h1 : ENNReal.ofReal ((3 * Real.sqrt d) ^ d) * unitBallVol d
          = ((Real.toNNReal ((3 * Real.sqrt d) ^ d) * (unitBallVol d).toNNReal :
              ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.coe_mul, ENNReal.coe_toNNReal unitBallVol_ne_top]
        rfl
      rw [h1]
      simp only [cubeVitaliConst]
      exact ENNReal.coe_le_coe.mpr le_add_self
    calc ENNReal.ofReal ((3 * Real.sqrt d) ^ d) * ENNReal.ofReal (h ^ d) * unitBallVol d
        = (ENNReal.ofReal ((3 * Real.sqrt d) ^ d) * unitBallVol d)
          * ENNReal.ofReal (h ^ d) := by ring
      _ ≤ ((cubeVitaliConst d : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (h ^ d) :=
          mul_le_mul' hc le_rfl

/-- The cubes of a shrinking sequence containing `x` converge to `x` in the
Vitali family's filter. -/
lemma tendsto_closedCube_filterAt {ι : Type} {l : Filter ι} {x : EuclideanSpace ℝ (Fin d)}
    (hn : ι → ℝ) (un : ι → EuclideanSpace ℝ (Fin d)) (hpos : ∀ i, 0 < hn i)
    (hlim : Tendsto hn l (𝓝 0)) (hmem : ∀ i, x ∈ closedCube (hn i) (un i)) :
    Tendsto (fun i => closedCube (hn i) (un i)) l ((cubeVitali d).filterAt x) := by
  refine (cubeVitali d).tendsto_filterAt_iff.mpr
    ⟨Eventually.of_forall (fun i => closedCube_mem_setsAt (hpos i) (hmem i)), fun ε hε => ?_⟩
  have hsd : (0:ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hlim' : Tendsto (fun i => hn i * Real.sqrt d) l (𝓝 0) := by
    simpa using hlim.mul_const (Real.sqrt d)
  filter_upwards [hlim' (Iio_mem_nhds (show (0:ℝ) < ε from hε))] with i hi
  exact (closedCube_subset_closedBall_of_mem (hmem i)).trans
    (closedBall_subset_closedBall (le_of_lt hi))

/-! ## Lemma 7.2 -/

/-- **Lemma 7.2** of Bux–Kassmann–Schulze. For a locally integrable `φ` and
almost every `s`, the averages of `φ` over any shrinking sequence of cubes
containing `s` converge to `φ(s)`.

The paper takes the cubes centred at points of `hℤ^d`; the proof needs only that
they contain `s` and shrink, so no lattice hypothesis appears. The paper's
`λ_d(A_h(x_h))^{-1} ∫_{A_h(x_h)} φ` is the average over the open cube, which
agrees with the average over the closed one since they differ by a null set. -/
theorem lemma_lebesgue_diff {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : LocallyIntegrable φ volume) :
    ∀ᵐ s : EuclideanSpace ℝ (Fin d),
      ∀ {ι : Type} {l : Filter ι} (hn : ι → ℝ) (un : ι → EuclideanSpace ℝ (Fin d)),
        (∀ i, 0 < hn i) → Tendsto hn l (𝓝 0) → (∀ i, s ∈ closedCube (hn i) (un i)) →
        Tendsto (fun i => ⨍ y in closedCube (hn i) (un i), φ y) l (𝓝 (φ s)) := by
  filter_upwards [(cubeVitali d).ae_tendsto_average hφ] with s hs ι l hn un hpos hlim hmem
  exact hs.comp (tendsto_closedCube_filterAt hn un hpos hlim hmem)

end QFS
