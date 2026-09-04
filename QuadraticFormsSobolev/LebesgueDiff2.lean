/-
Lemma 7.2 of Bux–Kassmann–Schulze on the *product* space `ℝ^d × ℝ^d`.

Section 3.2 differentiates a function of a pair, `(f(s) − f(t))² k(s,t)`, along
the product cubes `Ã_h(x) × Ã_h(y)` of the tiling.  Those are the cubes of the
tiling of `ℝ^{2d}`, so this is again the Lebesgue differentiation theorem, but
`ℝ^d × ℝ^d` is not the type `EuclideanSpace ℝ (Fin 2d)` and its norm is the
maximum of the two, not the Euclidean one.  Rather than transport the result
along a measure-preserving equivalence, the Vitali family of
`QuadraticFormsSobolev.LebesgueDiff` is rebuilt here for the product; every step
is the product of the corresponding step there, and the maximum norm makes the
balls of the product literally the products of balls.
-/
import QuadraticFormsSobolev.LebesgueDiff

open Real Set Metric MeasureTheory ENNReal Filter Topology
open scoped NNReal

namespace QFS

variable {d : ℕ}

/-! ## Balls and cubes of the product -/

/-- The volume of the unit ball of `ℝ^d × ℝ^d`. -/
noncomputable def unitBallVol₂ (d : ℕ) : ℝ≥0∞ := unitBallVol d * unitBallVol d

lemma unitBallVol₂_ne_top : unitBallVol₂ d ≠ ⊤ :=
  ENNReal.mul_ne_top unitBallVol_ne_top unitBallVol_ne_top

lemma volume_closedBall₂_eq (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))
    {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall p r) = ENNReal.ofReal (r ^ (2 * d)) * unitBallVol₂ d := by
  rw [show p = (p.1, p.2) from rfl, ← closedBall_prod_same, Measure.volume_eq_prod,
    Measure.prod_prod, volume_closedBall_eq p.1 hr, volume_closedBall_eq p.2 hr,
    unitBallVol₂, two_mul, pow_add, ENNReal.ofReal_mul (by positivity)]
  ring

/-- The closed cube of the product tiling: a product of two closed cubes. -/
def closedCube₂ (h : ℝ) (u : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  closedCube h u.1 ×ˢ closedCube h u.2

lemma volume_closedCube₂ {h : ℝ} (hh : 0 ≤ h)
    (u : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    volume (closedCube₂ h u) = ENNReal.ofReal (h ^ (2 * d)) := by
  rw [closedCube₂, Measure.volume_eq_prod, Measure.prod_prod, volume_closedCube hh,
    volume_closedCube hh, two_mul, pow_add, ENNReal.ofReal_mul (by positivity)]

lemma isClosed_closedCube₂ {h : ℝ} (hh : 0 ≤ h)
    (u : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    IsClosed (closedCube₂ h u) :=
  (isClosed_closedCube hh u.1).prod (isClosed_closedCube hh u.2)

lemma closedCube₂_subset_closedBall_of_mem {h : ℝ}
    {u p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)} (hp : p ∈ closedCube₂ h u) :
    closedCube₂ h u ⊆ closedBall p (h * Real.sqrt d) := by
  rw [show p = (p.1, p.2) from rfl, ← closedBall_prod_same]
  exact Set.prod_mono (closedCube_subset_closedBall_of_mem hp.1)
    (closedCube_subset_closedBall_of_mem hp.2)

/-! ## The Vitali family of product cubes -/

/-- The doubling constant of the product family. -/
noncomputable def cubeVitaliConst₂ (d : ℕ) : ℝ≥0 :=
  (3 : ℝ≥0) ^ (2 * d) +
    Real.toNNReal ((3 * Real.sqrt d) ^ (2 * d)) * (unitBallVol₂ d).toNNReal

lemma cubeVitali₂_doubling (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    ∃ᶠ r in 𝓝[>] (0:ℝ), volume (closedBall p (3 * r))
      ≤ cubeVitaliConst₂ d * volume (closedBall p r) := by
  refine Filter.Eventually.frequently ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : (0:ℝ) < r := hr
  rw [volume_closedBall₂_eq p (by positivity), volume_closedBall₂_eq p hr0.le,
    show (3 * r) ^ (2 * d) = 3 ^ (2 * d) * r ^ (2 * d) by ring,
    ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 3 ^ (2 * d))]
  have hc : ENNReal.ofReal ((3:ℝ) ^ (2 * d)) ≤ ((cubeVitaliConst₂ d : ℝ≥0) : ℝ≥0∞) := by
    have h1 : ENNReal.ofReal ((3:ℝ) ^ (2 * d)) = (((3:ℝ≥0) ^ (2 * d) : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_pow, ENNReal.ofReal_pow (by norm_num)]
      congr 1
      simp [ENNReal.ofReal]
    rw [h1]
    simp only [cubeVitaliConst₂]
    exact ENNReal.coe_le_coe.mpr le_self_add
  calc ENNReal.ofReal ((3:ℝ) ^ (2 * d)) * ENNReal.ofReal (r ^ (2 * d)) * unitBallVol₂ d
      = ENNReal.ofReal ((3:ℝ) ^ (2 * d)) *
          (ENNReal.ofReal (r ^ (2 * d)) * unitBallVol₂ d) := by ring
    _ ≤ ((cubeVitaliConst₂ d : ℝ≥0) : ℝ≥0∞) *
          (ENNReal.ofReal (r ^ (2 * d)) * unitBallVol₂ d) := mul_le_mul' hc le_rfl

/-- The Vitali family in which the product cubes live. -/
noncomputable def cubeVitali₂ (d : ℕ) :
    VitaliFamily (volume : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) :=
  Vitali.vitaliFamily volume (cubeVitaliConst₂ d) cubeVitali₂_doubling

lemma closedCube₂_mem_setsAt {h : ℝ} (hh : 0 < h)
    {u p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)} (hp : p ∈ closedCube₂ h u) :
    closedCube₂ h u ∈ (cubeVitali₂ d).setsAt p := by
  refine ⟨isClosed_closedCube₂ hh.le u, ⟨u, ?_⟩, h * Real.sqrt d,
    closedCube₂_subset_closedBall_of_mem hp, ?_⟩
  · refine (((isOpen_cube hh u.1).prod (isOpen_cube hh u.2)).subset_interior_iff.mpr ?_) ?_
    · exact Set.prod_mono (cube_subset_closedCube h u.1) (cube_subset_closedCube h u.2)
    · exact ⟨mem_cube_self hh u.1, mem_cube_self hh u.2⟩
  · have hsd : (0:ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
    rw [volume_closedBall₂_eq p (by positivity), volume_closedCube₂ hh.le,
      show (3 * (h * Real.sqrt d)) ^ (2 * d) = (3 * Real.sqrt d) ^ (2 * d) * h ^ (2 * d) by ring,
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (3 * Real.sqrt d) ^ (2 * d))]
    have hc : ENNReal.ofReal ((3 * Real.sqrt d) ^ (2 * d)) * unitBallVol₂ d
        ≤ ((cubeVitaliConst₂ d : ℝ≥0) : ℝ≥0∞) := by
      have h1 : ENNReal.ofReal ((3 * Real.sqrt d) ^ (2 * d)) * unitBallVol₂ d
          = ((Real.toNNReal ((3 * Real.sqrt d) ^ (2 * d)) * (unitBallVol₂ d).toNNReal :
              ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.coe_mul, ENNReal.coe_toNNReal unitBallVol₂_ne_top]
        rfl
      rw [h1]
      simp only [cubeVitaliConst₂]
      exact ENNReal.coe_le_coe.mpr le_add_self
    calc ENNReal.ofReal ((3 * Real.sqrt d) ^ (2 * d)) * ENNReal.ofReal (h ^ (2 * d))
          * unitBallVol₂ d
        = (ENNReal.ofReal ((3 * Real.sqrt d) ^ (2 * d)) * unitBallVol₂ d)
          * ENNReal.ofReal (h ^ (2 * d)) := by ring
      _ ≤ ((cubeVitaliConst₂ d : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (h ^ (2 * d)) :=
          mul_le_mul' hc le_rfl

lemma tendsto_closedCube₂_filterAt {ι : Type} {l : Filter ι}
    {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)} (hn : ι → ℝ)
    (un : ι → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) (hpos : ∀ i, 0 < hn i)
    (hlim : Tendsto hn l (𝓝 0)) (hmem : ∀ i, p ∈ closedCube₂ (hn i) (un i)) :
    Tendsto (fun i => closedCube₂ (hn i) (un i)) l ((cubeVitali₂ d).filterAt p) := by
  refine (cubeVitali₂ d).tendsto_filterAt_iff.mpr
    ⟨Eventually.of_forall (fun i => closedCube₂_mem_setsAt (hpos i) (hmem i)), fun ε hε => ?_⟩
  have hlim' : Tendsto (fun i => hn i * Real.sqrt d) l (𝓝 0) := by
    simpa using hlim.mul_const (Real.sqrt d)
  filter_upwards [hlim' (Iio_mem_nhds (show (0:ℝ) < ε from hε))] with i hi
  exact (closedCube₂_subset_closedBall_of_mem (hmem i)).trans
    (closedBall_subset_closedBall (le_of_lt hi))

/-! ## Lemma 7.2 on the product -/

/-- **Lemma 7.2 for functions of a pair.** For a locally integrable `Φ` on
`ℝ^d × ℝ^d` and almost every pair `p`, the averages of `Φ` over any shrinking
sequence of product cubes containing `p` converge to `Φ p`. -/
theorem lemma_lebesgue_diff₂
    {Φ : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ}
    (hΦ : LocallyIntegrable Φ volume) :
    ∀ᵐ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ∀ {ι : Type} {l : Filter ι} (hn : ι → ℝ)
        (un : ι → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)),
        (∀ i, 0 < hn i) → Tendsto hn l (𝓝 0) → (∀ i, p ∈ closedCube₂ (hn i) (un i)) →
        Tendsto (fun i => ⨍ q in closedCube₂ (hn i) (un i), Φ q) l (𝓝 (Φ p)) := by
  filter_upwards [(cubeVitali₂ d).ae_tendsto_average hΦ] with p hp ι l hn un hpos hlim hmem
  exact hp.comp (tendsto_closedCube₂_filterAt hn un hpos hlim hmem)

end QFS
