import QuadraticFormsSobolev.Nonvacuous
import QuadraticFormsSobolev.Section7
import QuadraticFormsSobolev.Section3Kernel
import QuadraticFormsSobolev.Section32

/-!
# Beyond the paper — new mathematics, not a formalisation of Bux–Kassmann–Schulze

**Everything in this file is outside the scope of the paper being certified.**
None of it appears in arXiv:1707.09277, in any form: not the statements, not the
constants, not the proofs. It is an attempt to close the one gap the
formalisation of that paper leaves open, and it should be read as new (and
incomplete) research rather than as a record of what the authors wrote. Nothing
elsewhere in this repository depends on this file.

## The problem

Section 3.2's dominated-convergence step needs an a priori hypothesis its own
argument never establishes: that `f ∈ H_k(B*)` already lies in `H^{α/2}(B*)`.
The formalisation of that step (`QFS.limsup_lintegral_stepG_le`) and of the
whole of §3.2 (`QFS.formHs_ball_le_form_of_formHs_ne_top`) carries the
hypothesis explicitly. This file discharges it in dimension two.

## What this file proves

The route is a local Poincaré inequality: for two points `s`, `t`,

  (★)  `(f(s) − f(t))²` is recovered by chaining through intermediate points
       that *do* see the relevant cones, averaged over a positive-measure set of
       such points,

which converts the cone-restricted energy into the full fractional energy.
`exists_ball_in_two_cones` is its geometric heart: for two distinct points
sharing a cone direction it supplies a **ball** of intermediate points lying in
both cones — a positive-measure strengthening of the paper's Lemma 4.3, which
produces a single point. In the plane the same is true without a shared
direction (`mem_two_cones_of_mem_planarBall`), because two non-parallel lines
meet; that is what closes dimension two, and `no_common_neighbour_of_skew_axes`
proves it cannot be done this way in dimension three.

Downstream of the inclusion, this file also carries the consequences that the
paper's own machinery then yields in the plane:

* `sobolevInclusion_planar` — `H_k(ℝ²) ⊆ H^{α/2}(ℝ²)`, and
  `formHs_ball_ne_top_of_planar` — its ball form, which is exactly §3.2's
  missing hypothesis;
* `formHs_ball_le_form_planar` and `theoremOneOneBallCondMeas_two` — Theorem
  1.1's enlarged-ball form in the plane, in the paper's own shape;
* `formHs_le_form_planar`, `Hk_ball_eq_Hs_ball_planar` — Theorem 1.1 and
  Lemma 3.7 on the same ball, granted the Whitney/Dyda input Lemma 7.1 quotes;
* `formHs_univ_le_form_univ_planar`, `Hk_univ_eq_Hs_univ_planar`,
  `Hk_domain_eq_Hs_domain_planar` — Theorem 1.4 for `ℝ²` and for a domain with a
  Whitney family.

`planar_hypotheses_nonvacuous` records that none of this is vacuous.

## What this file does not prove

Dimension three and above. Two thin double cones with skew axes need not meet at
all, so one intermediate point cannot suffice and genuinely longer chains are
required; producing them, with a uniform bound on the length and with positive
measure at every link, is the continuous analogue of the paper's §§5–6. The
paper establishes that machinery only in the discrete setting — which is
precisely why it goes through `ℤ^d` — and reproducing it in the continuum is an
open research problem, not a gap in this formalisation.
-/

open Metric Set MeasureTheory
open scoped Real InnerProductSpace ENNReal

namespace QFS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The cone gap is never below `−‖p‖`. -/
lemma neg_norm_le_coneGap {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    (p : E) : -‖p‖ ≤ coneGap v ϑ p := by
  have h := coneGap_sub_le hv hϑ hϑ' 0 p
  rw [coneGap_zero, zero_sub, zero_sub, norm_neg] at h
  linarith

/-- **A ball of common cone-neighbours.**

If `s ≠ t` and both points admit the cone direction `v` with aperture `ϑ`, then
there is a whole ball of radius `‖s − t‖` — hence of positive measure — every
point `z` of which satisfies `z − s ∈ Ṽ(v,ϑ)` and `z − t ∈ Ṽ(v,ϑ)`, and which
lies within `O(‖s − t‖ / sin ϑ)` of both.

The paper's Lemma 4.3 produces one such `z`; for a chaining argument that is not
enough, because a single point is a null set and cannot absorb an average. The
ball is what makes the averaging step of `(★)` possible.

The construction is to walk from `s` a distance `3‖s − t‖ / sin ϑ` along the
axis: `coneGap` grows by exactly `sin ϑ` per unit step along `v`, so after that
walk the gap exceeds `3‖s − t‖`, leaving room `‖s − t‖` for the ball and a
further `2‖s − t‖` to absorb the displacement from `s` to `t`. -/
theorem exists_ball_in_two_cones {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ π / 2) {s t : E} (hst : s ≠ t) :
    ∃ z₀ : E, ∀ z ∈ closedBall z₀ ‖s - t‖,
      z - s ∈ cone v ϑ ∧ z - t ∈ cone v ϑ ∧
        ‖z - s‖ ≤ (1 + 3 / Real.sin ϑ) * ‖s - t‖ ∧
        ‖z - t‖ ≤ (2 + 3 / Real.sin ϑ) * ‖s - t‖ := by
  have hδ : 0 < ‖s - t‖ := by rw [norm_pos_iff]; exact sub_ne_zero_of_ne hst
  have hsin : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  set δ : ℝ := ‖s - t‖ with hδdef
  set lam : ℝ := 3 * δ / Real.sin ϑ with hlamdef
  have hlam : 0 < lam := by positivity
  have hlamsin : lam * Real.sin ϑ = 3 * δ := by
    rw [hlamdef]; field_simp
  refine ⟨s + lam • v, fun z hz => ?_⟩
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  set q : E := z - (s + lam • v) with hqdef
  have hq : ‖q‖ ≤ δ := hz
  have hzs : z - s = q + lam • v := by rw [hqdef]; abel
  have hzt : z - t = (q + (s - t)) + lam • v := by rw [hqdef]; abel
  have hq' : ‖q + (s - t)‖ ≤ 2 * δ :=
    le_trans (norm_add_le _ _) (by rw [← hδdef]; linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem_cone_iff_coneGap_pos hv hϑ hϑ', hzs, coneGap_add_smul_axis hv, hlamsin]
    have := neg_norm_le_coneGap hv hϑ hϑ' q
    linarith
  · rw [mem_cone_iff_coneGap_pos hv hϑ hϑ', hzt, coneGap_add_smul_axis hv, hlamsin]
    have := neg_norm_le_coneGap hv hϑ hϑ' (q + (s - t))
    linarith
  · rw [hzs]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam, hv, mul_one, hlamdef]
    have : 3 * δ / Real.sin ϑ = 3 / Real.sin ϑ * δ := by ring
    rw [this]
    nlinarith
  · rw [hzt]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam, hv, mul_one, hlamdef]
    have : 3 * δ / Real.sin ϑ = 3 / Real.sin ϑ * δ := by ring
    rw [this]
    nlinarith


/-! ## The averaging set, explicitly

For the chaining average one needs the ball of common neighbours as an explicit
function of `(s,t)` — a measurable selection is not enough, since the estimate
must be integrated in `s` and `t`. The centre is an explicit continuous
function, which is what the next definition records. -/

/-- The centre of the ball of common cone-neighbours of `s` and `t`: walk from
`s` along the axis `v` far enough that the cone has opened past `‖s − t‖`. -/
noncomputable def midCentre (v : E) (ϑ : ℝ) (s t : E) : E :=
  s + (3 * ‖s - t‖ / Real.sin ϑ) • v

/-- `exists_ball_in_two_cones` with the centre named. -/
theorem mem_two_cones_of_mem_midBall {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ π / 2) {s t : E} (hst : s ≠ t) {z : E}
    (hz : z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖) :
    z - s ∈ cone v ϑ ∧ z - t ∈ cone v ϑ ∧
      ‖z - s‖ ≤ (1 + 3 / Real.sin ϑ) * ‖s - t‖ ∧
      ‖z - t‖ ≤ (2 + 3 / Real.sin ϑ) * ‖s - t‖ := by
  have hδ : 0 < ‖s - t‖ := by rw [norm_pos_iff]; exact sub_ne_zero_of_ne hst
  have hsin : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hlamsin : (3 * ‖s - t‖ / Real.sin ϑ) * Real.sin ϑ = 3 * ‖s - t‖ := by field_simp
  have hlam : 0 < 3 * ‖s - t‖ / Real.sin ϑ := by positivity
  rw [Metric.mem_closedBall, dist_eq_norm, midCentre] at hz
  set q : E := z - (s + (3 * ‖s - t‖ / Real.sin ϑ) • v) with hqdef
  have hzs : z - s = q + (3 * ‖s - t‖ / Real.sin ϑ) • v := by rw [hqdef]; abel
  have hzt : z - t = (q + (s - t)) + (3 * ‖s - t‖ / Real.sin ϑ) • v := by rw [hqdef]; abel
  have hq' : ‖q + (s - t)‖ ≤ 2 * ‖s - t‖ := le_trans (norm_add_le _ _) (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem_cone_iff_coneGap_pos hv hϑ hϑ', hzs, coneGap_add_smul_axis hv, hlamsin]
    have := neg_norm_le_coneGap hv hϑ hϑ' q
    linarith
  · rw [mem_cone_iff_coneGap_pos hv hϑ hϑ', hzt, coneGap_add_smul_axis hv, hlamsin]
    have := neg_norm_le_coneGap hv hϑ hϑ' (q + (s - t))
    linarith
  · rw [hzs]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam, hv, mul_one]
    have h3 : 3 * ‖s - t‖ / Real.sin ϑ = 3 / Real.sin ϑ * ‖s - t‖ := by ring
    rw [h3]; nlinarith
  · rw [hzt]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam, hv, mul_one]
    have h3 : 3 * ‖s - t‖ / Real.sin ϑ = 3 / Real.sin ϑ * ‖s - t‖ := by ring
    rw [h3]; nlinarith

/-- The norm bounds of `mem_two_cones_of_mem_midBall`, stated without needing
`s ≠ t`: a point of the averaging ball is at distance `O(‖s − t‖ / sin ϑ)` from
both `s` and `t`. Both directions of this comparison are needed for the
chaining average — the upper bound to keep the chain inside a slightly enlarged
cube, the resulting lower bound on `‖s − t‖` to control the fibre integral. -/
theorem norm_sub_le_of_mem_midBall {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ π / 2) {s t z : E}
    (hz : z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖) :
    ‖z - s‖ ≤ (1 + 3 / Real.sin ϑ) * ‖s - t‖ ∧
      ‖z - t‖ ≤ (2 + 3 / Real.sin ϑ) * ‖s - t‖ := by
  have hsin : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hlam : 0 ≤ 3 * ‖s - t‖ / Real.sin ϑ := by positivity
  rw [Metric.mem_closedBall, dist_eq_norm, midCentre] at hz
  set q : E := z - (s + (3 * ‖s - t‖ / Real.sin ϑ) • v) with hqdef
  have hzs : z - s = q + (3 * ‖s - t‖ / Real.sin ϑ) • v := by rw [hqdef]; abel
  have hzt : z - t = (q + (s - t)) + (3 * ‖s - t‖ / Real.sin ϑ) • v := by rw [hqdef]; abel
  have hq' : ‖q + (s - t)‖ ≤ 2 * ‖s - t‖ := le_trans (norm_add_le _ _) (by linarith)
  have hsmul : ‖(3 * ‖s - t‖ / Real.sin ϑ) • v‖ = 3 / Real.sin ϑ * ‖s - t‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam, hv, mul_one]; ring
  constructor
  · rw [hzs]
    refine le_trans (norm_add_le _ _) ?_
    rw [hsmul]; linarith
  · rw [hzt]
    refine le_trans (norm_add_le _ _) ?_
    rw [hsmul]; linarith

/-- **The slice bound.** For fixed `s` and `z`, the points `t` for which `z` is
one of their common cone-neighbours have `‖s − t‖` pinned to within a factor two
by `⟪v, z − s⟫`.

This is the second quantitative input to the chaining average: it says the map
`(s,t) ↦ (s,z)` does not compress, so the `t`-fibre over each `z` is an annulus
of measure `O(‖z − s‖^d)`. Without it the average over the balls could not be
exchanged with the integration in `t`. -/
theorem inner_mem_Icc_of_mem_midBall {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ}
    {s t z : E} (hz : z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖) :
    ‖s - t‖ * (3 / Real.sin ϑ - 1) ≤ ⟪v, z - s⟫_ℝ ∧
      ⟪v, z - s⟫_ℝ ≤ ‖s - t‖ * (3 / Real.sin ϑ + 1) := by
  rw [Metric.mem_closedBall, dist_eq_norm, midCentre] at hz
  set q : E := z - (s + (3 * ‖s - t‖ / Real.sin ϑ) • v) with hqdef
  have hinner : ⟪v, q⟫_ℝ = ⟪v, z - s⟫_ℝ - 3 * ‖s - t‖ / Real.sin ϑ := by
    rw [hqdef, show z - (s + (3 * ‖s - t‖ / Real.sin ϑ) • v)
        = (z - s) - (3 * ‖s - t‖ / Real.sin ϑ) • v from by abel,
      inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hv]
    ring
  have hcs : |⟪v, q⟫_ℝ| ≤ ‖q‖ := by
    have := abs_real_inner_le_norm v q
    rwa [hv, one_mul] at this
  have habs : |⟪v, z - s⟫_ℝ - 3 * ‖s - t‖ / Real.sin ϑ| ≤ ‖s - t‖ := by
    rw [← hinner]; exact le_trans hcs hz
  rw [abs_le] at habs
  have heq : 3 * ‖s - t‖ / Real.sin ϑ = ‖s - t‖ * (3 / Real.sin ϑ) := by ring
  rw [heq] at habs
  constructor <;> [linarith [habs.1]; linarith [habs.2]]

/-- The `t`-fibre lies in a ball whose radius is comparable to `‖z − s‖`, hence
has measure `O(‖z − s‖^d)` — the compression bound in the form the averaging
step uses. -/
theorem midBall_fibre_subset_closedBall {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ π / 2) (s z : E) :
    {t | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖}
      ⊆ closedBall s (‖z - s‖ / (3 / Real.sin ϑ - 1)) := by
  intro t ht
  have hsin : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hsin1 : Real.sin ϑ ≤ 1 := Real.sin_le_one ϑ
  have h3 : (3 : ℝ) ≤ 3 / Real.sin ϑ := by
    have hnn : (0 : ℝ) ≤ 3 * (1 - Real.sin ϑ) / Real.sin ϑ :=
      div_nonneg (by linarith) hsin.le
    have heq : 3 + 3 * (1 - Real.sin ϑ) / Real.sin ϑ = 3 / Real.sin ϑ := by
      field_simp
      ring
    linarith [heq]
  have hden : 0 < 3 / Real.sin ϑ - 1 := by linarith
  obtain ⟨hlow, -⟩ := inner_mem_Icc_of_mem_midBall (t := t) hv ht
  have hcs : ⟪v, z - s⟫_ℝ ≤ ‖z - s‖ := by
    have := real_inner_le_norm v (z - s)
    rwa [hv, one_mul] at this
  have hdist : dist t s = ‖s - t‖ := by rw [dist_eq_norm, norm_sub_rev]
  rw [Metric.mem_closedBall, hdist, le_div_iff₀ hden]
  linarith


/-- The third quantitative input: the ball of common neighbours has volume
exactly `c_d ‖s − t‖^d`, so the average over it is normalised by a factor that
scales correctly against the `‖s − t‖^{-d-α}` weight. -/
theorem volume_midBall {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (ϑ : ℝ)
    (s t : EuclideanSpace ℝ (Fin d)) :
    MeasureTheory.volume (closedBall (midCentre v ϑ s t) ‖s - t‖)
      = ENNReal.ofReal (‖s - t‖ ^ d) * unitBallVol d :=
  volume_closedBall_eq _ (norm_nonneg _)


/-! ## The fibre estimate

The chaining average is exchanged with the integration in `t` by Tonelli, and
what has to survive that exchange is the weight. This is the estimate that makes
it work, and it is the reason the argument is scale-invariant: the singular
weight `‖s − t‖^{-2d-α}` integrated over the `t`-fibre above a point `z` comes
back as `‖z − s‖^{-d-α}`, exactly the weight of the `H_k` form on the pair
`(s,z)` — which the lower bound of (1.4) then converts into `k(s,z)`. -/

/-- The constant in the fibre estimate: `(1 + 3/sin ϑ)^{2d+α} / (3/sin ϑ − 1)^d`. -/
noncomputable def chainConst (d : ℕ) (ϑ α : ℝ) : ℝ :=
  (1 + 3 / Real.sin ϑ) ^ (2 * (d : ℝ) + α) / (3 / Real.sin ϑ - 1) ^ d

/-- **The fibre estimate.** Integrating `‖s − t‖^{-2d-α}` over the set of `t` for
which `z` is a common cone-neighbour of `s` and `t` returns `‖z − s‖^{-d-α}`, up
to a constant depending only on `d`, `ϑ` and `α`. -/
theorem lintegral_midBall_fibre_le {d : ℕ} {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α) (hd : 0 < d)
    (s z : EuclideanSpace ℝ (Fin d)) :
    ∫⁻ t in {t | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖},
        ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α))
      ≤ ENNReal.ofReal (chainConst d ϑ α * ‖z - s‖ ^ (-(d : ℝ) - α)) * unitBallVol d := by
  have hsin : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hsin1 : Real.sin ϑ ≤ 1 := Real.sin_le_one ϑ
  have h3 : (3 : ℝ) ≤ 3 / Real.sin ϑ := by
    have hnn : (0 : ℝ) ≤ 3 * (1 - Real.sin ϑ) / Real.sin ϑ := div_nonneg (by linarith) hsin.le
    have heq : 3 + 3 * (1 - Real.sin ϑ) / Real.sin ϑ = 3 / Real.sin ϑ := by field_simp; ring
    linarith [heq]
  have hA : (0 : ℝ) < 1 + 3 / Real.sin ϑ := by linarith
  have hB : (0 : ℝ) < 3 / Real.sin ϑ - 1 := by linarith
  have hsub := midBall_fibre_subset_closedBall hv hϑ hϑ' s z
  -- the fibre is closed, hence measurable
  have hmeas : MeasurableSet {t : EuclideanSpace ℝ (Fin d) |
      z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖} := by
    have h1 : Continuous fun t : EuclideanSpace ℝ (Fin d) => dist z (midCentre v ϑ s t) := by
      unfold midCentre; fun_prop
    have h2 : Continuous fun t : EuclideanSpace ℝ (Fin d) => ‖s - t‖ := by fun_prop
    simpa [Metric.mem_closedBall] using (isClosed_le h1 h2).measurableSet
  rcases eq_or_ne z s with rfl | hzs
  · have hnull : volume {t : EuclideanSpace ℝ (Fin d) |
        z ∈ closedBall (midCentre v ϑ z t) ‖z - t‖} = 0 := by
      have hball0 : volume (closedBall z (0 : ℝ)) = 0 := by
        rw [volume_closedBall_eq _ le_rfl, zero_pow (Nat.ne_of_gt hd), ENNReal.ofReal_zero,
          zero_mul]
      refine measure_mono_null (le_trans hsub (le_of_eq ?_)) hball0
      simp
    rw [setLIntegral_measure_zero _ _ hnull]
    simp
  · have hn : 0 < ‖z - s‖ := by rw [norm_pos_iff]; exact sub_ne_zero_of_ne hzs
    have hexp : -(2 * (d : ℝ)) - α ≤ 0 := by
      have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith
    have hquot : 0 < ‖z - s‖ / (1 + 3 / Real.sin ϑ) := by positivity
    -- the scalar identity behind the constant
    have hAe : (1 + 3 / Real.sin ϑ) ^ (-(2 * (d : ℝ)) - α)
        = ((1 + 3 / Real.sin ϑ) ^ (2 * (d : ℝ) + α))⁻¹ := by
      rw [show -(2 * (d : ℝ)) - α = -(2 * (d : ℝ) + α) from by ring, Real.rpow_neg hA.le]
    have hxe : ‖z - s‖ ^ (-(2 * (d : ℝ)) - α) * ‖z - s‖ ^ ((d : ℕ) : ℝ)
        = ‖z - s‖ ^ (-(d : ℝ) - α) := by
      rw [← Real.rpow_add hn]; congr 1; ring
    have hscalar : (‖z - s‖ / (1 + 3 / Real.sin ϑ)) ^ (-(2 * (d : ℝ)) - α) *
        (‖z - s‖ ^ d / (3 / Real.sin ϑ - 1) ^ d)
        = chainConst d ϑ α * ‖z - s‖ ^ (-(d : ℝ) - α) := by
      have e1 : (‖z - s‖ / (1 + 3 / Real.sin ϑ)) ^ (-(2 * (d : ℝ)) - α)
          = ‖z - s‖ ^ (-(2 * (d : ℝ)) - α) * (1 + 3 / Real.sin ϑ) ^ (2 * (d : ℝ) + α) := by
        rw [Real.div_rpow hn.le hA.le, hAe, div_eq_mul_inv, inv_inv]
      rw [e1, ← Real.rpow_natCast ‖z - s‖ d, chainConst]
      rw [show ‖z - s‖ ^ (-(2 * (d : ℝ)) - α) * (1 + 3 / Real.sin ϑ) ^ (2 * (d : ℝ) + α) *
            (‖z - s‖ ^ ((d : ℕ) : ℝ) / (3 / Real.sin ϑ - 1) ^ d)
          = (‖z - s‖ ^ (-(2 * (d : ℝ)) - α) * ‖z - s‖ ^ ((d : ℕ) : ℝ)) *
            ((1 + 3 / Real.sin ϑ) ^ (2 * (d : ℝ) + α) / (3 / Real.sin ϑ - 1) ^ d) from by ring,
        hxe]
      ring
    calc ∫⁻ t in {t | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖},
            ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α))
        ≤ ∫⁻ _ in {t | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖},
            ENNReal.ofReal ((‖z - s‖ / (1 + 3 / Real.sin ϑ)) ^ (-(2 * (d : ℝ)) - α)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hmeas] with t ht
          obtain ⟨h1, -⟩ := norm_sub_le_of_mem_midBall hv hϑ hϑ' ht
          refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hquot ?_ hexp)
          rw [div_le_iff₀ hA]
          linarith [h1]
      _ = ENNReal.ofReal ((‖z - s‖ / (1 + 3 / Real.sin ϑ)) ^ (-(2 * (d : ℝ)) - α)) *
            volume {t | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖} := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal ((‖z - s‖ / (1 + 3 / Real.sin ϑ)) ^ (-(2 * (d : ℝ)) - α)) *
            volume (closedBall s (‖z - s‖ / (3 / Real.sin ϑ - 1))) :=
          mul_le_mul' le_rfl (measure_mono hsub)
      _ = ENNReal.ofReal (chainConst d ϑ α * ‖z - s‖ ^ (-(d : ℝ) - α)) * unitBallVol d := by
          rw [volume_closedBall_eq _ (by positivity), ← mul_assoc,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hquot.le _), div_pow, hscalar]


/-! ## The averaging step

The other ingredient: the oscillation between `s` and `t` is dominated by the
*average* over the ball of common neighbours of the two oscillations along the
chain `s → z → t`. This is where a positive-measure set of intermediate points
is indispensable — with the single point of Lemma 4.3 the left-hand side would
be multiplied by zero. -/

/-- **The averaging step.** `(f(t) − f(s))²` times the volume of the ball of
common cone-neighbours is at most the integral over that ball of
`2(f(z) − f(s))² + 2(f(t) − f(z))²`. -/
theorem osc_mul_volume_le {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (ϑ : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (s t : EuclideanSpace ℝ (Fin d)) :
    ENNReal.ofReal ((f t - f s) ^ 2) * volume (closedBall (midCentre v ϑ s t) ‖s - t‖)
      ≤ ∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖,
          ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2) := by
  rw [← setLIntegral_const (closedBall (midCentre v ϑ s t) ‖s - t‖)
    (ENNReal.ofReal ((f t - f s) ^ 2))]
  refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
  nlinarith [sq_nonneg (f z - f s - (f t - f z)), sq_nonneg (f z - f s + (f t - f z))]

/-- The averaging step in the form the chaining uses: dividing by the volume,
which is `c_d‖s − t‖^d`, converts the weight `‖s − t‖^{-d-α}` on the left into
the weight `‖s − t‖^{-2d-α}` that `lintegral_midBall_fibre_le` integrates. -/
theorem osc_weighted_le {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (ϑ : ℝ) {α : ℝ}
    (hα : 0 ≤ α) (f : EuclideanSpace ℝ (Fin d) → ℝ) (s t : EuclideanSpace ℝ (Fin d)) :
    ENNReal.ofReal ((f t - f s) ^ 2) * ENNReal.ofReal (‖s - t‖ ^ (-(d : ℝ) - α)) *
        unitBallVol d
      ≤ ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)) *
        ∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖,
          ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2) := by
  -- the weights combine: `‖s−t‖^{-d-α} = ‖s−t‖^{-2d-α} · ‖s−t‖^d`
  have hw : ‖s - t‖ ^ (-(d : ℝ) - α)
      = ‖s - t‖ ^ (-(2 * (d : ℝ)) - α) * ‖s - t‖ ^ d := by
    rcases eq_or_lt_of_le (norm_nonneg (s - t)) with h | h
    · rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp
      · have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
        have hne : -(d : ℝ) - α ≠ 0 := by intro hc; linarith
        rw [← h, zero_pow (Nat.ne_of_gt hd), mul_zero, Real.zero_rpow hne]
    · rw [← Real.rpow_natCast ‖s - t‖ d, ← Real.rpow_add h]
      congr 1
      ring
  refine le_trans (le_of_eq ?_)
    (mul_le_mul' (le_refl (ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α))))
      (osc_mul_volume_le v ϑ f s t))
  rw [volume_closedBall_eq _ (norm_nonneg _), hw, ENNReal.ofReal_mul (by positivity)]
  ring


/-- Off the cone the fibre is a single point: if `z − s` does not lie in
`Ṽ(v,ϑ)` then no `t ≠ s` has `z` among the common neighbours of `s` and `t`.
This is what lets the exchange keep the cone membership, without which the lower
bound of (1.4) could not be applied to the resulting pair `(s,z)`. -/
theorem fibre_subset_singleton_of_notMem_cone {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ π / 2) {s z : E} (hz : z - s ∉ cone v ϑ) :
    {t | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖} ⊆ {s} := by
  intro t ht
  by_contra hne
  exact hz (mem_two_cones_of_mem_midBall hv hϑ hϑ' (fun h => hne h.symm) ht).1

/-! ## The exchange

With the averaging step and the fibre estimate in hand, the chaining argument is
one application of Tonelli: exchange the average over the ball of common
neighbours with the integration in `t`, and the fibre estimate converts the
weight into the one carried by the pair `(s,z)`. -/

/-- **The exchange, abstractly.** All the chaining argument asks of the family of
averaging sets is that its graph be measurable and that the weight integrate
over each fibre to something summable. Both exchanges below are instances, and
so is any future construction of averaging sets — for cross-type pairs, say,
where the balls of `exists_ball_in_two_cones` are unavailable. -/
theorem lintegral_swap_of_fibre_bound {d : ℕ}
    {W : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d))}
    (hWm : ∀ t, MeasurableSet (W t))
    (hgraph : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      p.2 ∈ W p.1})
    {w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hwm : Measurable w)
    {G : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hG : Measurable G)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hfibm : ∀ z, MeasurableSet {t | z ∈ W t})
    (hfib : ∀ z, ∫⁻ t in {t | z ∈ W t}, w t ≤ Ψ z) :
    ∫⁻ t, w t * ∫⁻ z in W t, G z ≤ ∫⁻ z, G z * Ψ z := by
  have hstep : ∀ t, w t * ∫⁻ z in W t, G z = ∫⁻ z, w t * (W t).indicator G z := by
    intro t
    rw [lintegral_const_mul _ (hG.indicator (hWm t)), lintegral_indicator (hWm t)]
  have hunc : AEMeasurable (Function.uncurry fun t z => w t * (W t).indicator G z) volume := by
    refine Measurable.aemeasurable ?_
    have heq : (Function.uncurry fun t z => w t * (W t).indicator G z)
        = fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
          w p.1 * {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
            p.2 ∈ W p.1}.indicator (fun q => G q.2) p := by
      funext p
      obtain ⟨t, z⟩ := p
      simp only [Function.uncurry]
      by_cases hp : z ∈ W t
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem
          (show (t, z) ∈ {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
            p.2 ∈ W p.1} from hp)]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem
          (show (t, z) ∉ {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
            p.2 ∈ W p.1} from hp)]
    rw [heq]
    exact (hwm.comp measurable_fst).mul ((hG.comp measurable_snd).indicator hgraph)
  calc ∫⁻ t, w t * ∫⁻ z in W t, G z
      = ∫⁻ t, ∫⁻ z, w t * (W t).indicator G z := lintegral_congr hstep
    _ = ∫⁻ z, ∫⁻ t, w t * (W t).indicator G z := lintegral_lintegral_swap hunc
    _ ≤ ∫⁻ z, G z * Ψ z := by
        refine lintegral_mono fun z => ?_
        have hpw : ∀ t, w t * (W t).indicator G z
            = {t | z ∈ W t}.indicator (fun t => G z * w t) t := by
          intro t
          by_cases hp : z ∈ W t
          · rw [Set.indicator_of_mem hp,
              Set.indicator_of_mem (show t ∈ {t | z ∈ W t} from hp)]
            ring
          · rw [Set.indicator_of_notMem hp,
              Set.indicator_of_notMem (show t ∉ {t | z ∈ W t} from hp)]
            simp
        calc ∫⁻ t, w t * (W t).indicator G z
            = ∫⁻ t, {t | z ∈ W t}.indicator (fun t => G z * w t) t := lintegral_congr hpw
          _ = ∫⁻ t in {t | z ∈ W t}, G z * w t := lintegral_indicator (hfibm z) _
          _ = G z * ∫⁻ t in {t | z ∈ W t}, w t := lintegral_const_mul _ hwm
          _ ≤ G z * Ψ z := mul_le_mul' le_rfl (hfib z)

/-- **The exchange, at fixed `s`.** Integrating the chaining average over `t` and
swapping gives back an integral in `z` against the weight `‖z − s‖^{-d-α}` — the
weight of the `H_k` form on the pair `(s,z)`, which the lower bound of (1.4)
turns into `k(s,z)`. -/
theorem lintegral_swap_fibre {d : ℕ} {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α) (hd : 0 < d)
    (s : EuclideanSpace ℝ (Fin d)) {G : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ t, ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)) *
        ∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖, G z
      ≤ ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
        ∫⁻ z in {z | z - s ∈ cone v ϑ}, G z * ENNReal.ofReal (‖z - s‖ ^ (-(d : ℝ) - α)) := by
  have hconeMeas : MeasurableSet {z : EuclideanSpace ℝ (Fin d) | z - s ∈ cone v ϑ} :=
    ((isOpen_cone v ϑ).preimage (by fun_prop)).measurableSet
  have hsinP : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have h3P : (3 : ℝ) ≤ 3 / Real.sin ϑ := by
    have hnn : (0 : ℝ) ≤ 3 * (1 - Real.sin ϑ) / Real.sin ϑ :=
      div_nonneg (by linarith [Real.sin_le_one ϑ]) hsinP.le
    have heq : 3 + 3 * (1 - Real.sin ϑ) / Real.sin ϑ = 3 / Real.sin ϑ := by field_simp; ring
    linarith [heq]
  have hcc : 0 ≤ chainConst d ϑ α := by
    unfold chainConst
    exact div_nonneg (Real.rpow_nonneg (by linarith) _) (pow_nonneg (by linarith) d)
  have hwm : Measurable fun t : EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)) := by fun_prop
  have hgraph : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      p.2 ∈ closedBall (midCentre v ϑ s p.1) ‖s - p.1‖} := by
    have h1 : Continuous fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        dist p.2 (midCentre v ϑ s p.1) := by unfold midCentre; fun_prop
    have h2 : Continuous fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ‖s - p.1‖ := by fun_prop
    simpa [Metric.mem_closedBall] using (isClosed_le h1 h2).measurableSet
  have hfibm : ∀ z : EuclideanSpace ℝ (Fin d),
      MeasurableSet {t | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖} := by
    intro z
    have h1 : Continuous fun t : EuclideanSpace ℝ (Fin d) =>
        dist z (midCentre v ϑ s t) := by unfold midCentre; fun_prop
    have h2 : Continuous fun t : EuclideanSpace ℝ (Fin d) => ‖s - t‖ := by fun_prop
    simpa [Metric.mem_closedBall] using (isClosed_le h1 h2).measurableSet
  set Ψ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun z =>
    {z : EuclideanSpace ℝ (Fin d) | z - s ∈ cone v ϑ}.indicator
      (fun z => ENNReal.ofReal (chainConst d ϑ α * ‖z - s‖ ^ (-(d : ℝ) - α)) *
        unitBallVol d) z with hΨ
  have hfib : ∀ z, ∫⁻ t in {t | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖},
      ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)) ≤ Ψ z := by
    intro z
    simp only [hΨ]
    by_cases hzc : z - s ∈ cone v ϑ
    · rw [Set.indicator_of_mem (show z ∈ {z : EuclideanSpace ℝ (Fin d) |
        z - s ∈ cone v ϑ} from hzc)]
      exact lintegral_midBall_fibre_le hv hϑ hϑ' hα hd s z
    · rw [Set.indicator_of_notMem (show z ∉ {z : EuclideanSpace ℝ (Fin d) |
        z - s ∈ cone v ϑ} from hzc)]
      have hball0 : volume (closedBall s (0 : ℝ)) = 0 := by
        rw [volume_closedBall_eq _ le_rfl, zero_pow (Nat.ne_of_gt hd), ENNReal.ofReal_zero,
          zero_mul]
      have hnull : volume {t | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖} = 0 :=
        measure_mono_null
          (le_trans (fibre_subset_singleton_of_notMem_cone hv hϑ hϑ' hzc) (by simp)) hball0
      rw [setLIntegral_measure_zero _ _ hnull]
  refine le_trans (lintegral_swap_of_fibre_bound
    (W := fun t => closedBall (midCentre v ϑ s t) ‖s - t‖)
    (w := fun t => ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)))
    (fun _ => measurableSet_closedBall) hgraph hwm hG hfibm hfib) ?_
  have hprod : ∀ z, G z * Ψ z = {z : EuclideanSpace ℝ (Fin d) | z - s ∈ cone v ϑ}.indicator
      (fun z => G z * (ENNReal.ofReal (chainConst d ϑ α * ‖z - s‖ ^ (-(d : ℝ) - α)) *
        unitBallVol d)) z := by
    intro z
    simp only [hΨ]
    by_cases hzc : z - s ∈ cone v ϑ
    · rw [Set.indicator_of_mem (show z ∈ {z : EuclideanSpace ℝ (Fin d) |
        z - s ∈ cone v ϑ} from hzc), Set.indicator_of_mem
        (show z ∈ {z : EuclideanSpace ℝ (Fin d) | z - s ∈ cone v ϑ} from hzc)]
    · rw [Set.indicator_of_notMem (show z ∉ {z : EuclideanSpace ℝ (Fin d) |
        z - s ∈ cone v ϑ} from hzc), Set.indicator_of_notMem
        (show z ∉ {z : EuclideanSpace ℝ (Fin d) | z - s ∈ cone v ϑ} from hzc), mul_zero]
  rw [lintegral_congr hprod, lintegral_indicator hconeMeas,
    ← lintegral_const_mul' _ _
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top unitBallVol_ne_top)]
  refine le_of_eq (lintegral_congr fun z => ?_)
  rw [ENNReal.ofReal_mul hcc]
  ring
/-! ## The mirror image, on the `t` side

The chained integrand `2(f(z) − f(s))² + 2(f(t) − f(z))²` has two terms. The
first is handled by the lemmas above; the second needs the same statements with
the roles of `s` and `t` exchanged. The displacement from `s` to `t` costs one
extra unit in the estimates — `3/sin ϑ ∓ 2` in place of `3/sin ϑ ∓ 1` — but
nothing else changes. -/

/-- The `t`-side of `inner_mem_Icc_of_mem_midBall`. -/
theorem inner_mem_Icc_of_mem_midBall' {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ}
    {s t z : E} (hz : z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖) :
    ‖s - t‖ * (3 / Real.sin ϑ - 2) ≤ ⟪v, z - t⟫_ℝ ∧
      ⟪v, z - t⟫_ℝ ≤ ‖s - t‖ * (3 / Real.sin ϑ + 2) := by
  rw [Metric.mem_closedBall, dist_eq_norm, midCentre] at hz
  set q : E := z - (s + (3 * ‖s - t‖ / Real.sin ϑ) • v) with hqdef
  have hq' : ‖q + (s - t)‖ ≤ 2 * ‖s - t‖ := le_trans (norm_add_le _ _) (by linarith)
  have hzt : z - t = (q + (s - t)) + (3 * ‖s - t‖ / Real.sin ϑ) • v := by rw [hqdef]; abel
  have hinner : ⟪v, z - t⟫_ℝ = ⟪v, q + (s - t)⟫_ℝ + 3 * ‖s - t‖ / Real.sin ϑ := by
    rw [hzt, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hv]
    ring
  have hcs : |⟪v, q + (s - t)⟫_ℝ| ≤ ‖q + (s - t)‖ := by
    have := abs_real_inner_le_norm v (q + (s - t))
    rwa [hv, one_mul] at this
  rw [abs_le] at hcs
  have heq : 3 * ‖s - t‖ / Real.sin ϑ = ‖s - t‖ * (3 / Real.sin ϑ) := by ring
  rw [hinner, heq]
  constructor <;> [linarith [hcs.1, hq']; linarith [hcs.2, hq']]

/-- The `t`-side of `midBall_fibre_subset_closedBall`. -/
theorem midBall_fibre_subset_closedBall' {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ π / 2) (t z : E) :
    {s | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖}
      ⊆ closedBall t (‖z - t‖ / (3 / Real.sin ϑ - 2)) := by
  intro s hs
  have hsin : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hsin1 : Real.sin ϑ ≤ 1 := Real.sin_le_one ϑ
  have h3 : (3 : ℝ) ≤ 3 / Real.sin ϑ := by
    have hnn : (0 : ℝ) ≤ 3 * (1 - Real.sin ϑ) / Real.sin ϑ := div_nonneg (by linarith) hsin.le
    have heq : 3 + 3 * (1 - Real.sin ϑ) / Real.sin ϑ = 3 / Real.sin ϑ := by field_simp; ring
    linarith [heq]
  have hden : 0 < 3 / Real.sin ϑ - 2 := by linarith
  obtain ⟨hlow, -⟩ := inner_mem_Icc_of_mem_midBall' (s := s) hv hs
  have hcs : ⟪v, z - t⟫_ℝ ≤ ‖z - t‖ := by
    have := real_inner_le_norm v (z - t)
    rwa [hv, one_mul] at this
  have hdist : dist s t = ‖s - t‖ := dist_eq_norm _ _
  rw [Metric.mem_closedBall, hdist, le_div_iff₀ hden]
  linarith

/-- Off the cone at `t` the `s`-fibre is a single point. -/
theorem fibre_subset_singleton_of_notMem_cone' {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ π / 2) {t z : E} (hz : z - t ∉ cone v ϑ) :
    {s | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖} ⊆ {t} := by
  intro s hs
  by_contra hne
  refine hz (mem_two_cones_of_mem_midBall hv hϑ hϑ'
    (fun h => hne (Set.mem_singleton_iff.mpr h)) hs).2.1

/-- The constant in the `t`-side fibre estimate. -/
noncomputable def chainConst' (d : ℕ) (ϑ α : ℝ) : ℝ :=
  (2 + 3 / Real.sin ϑ) ^ (2 * (d : ℝ) + α) / (3 / Real.sin ϑ - 2) ^ d

/-- The `t`-side of `lintegral_midBall_fibre_le`. -/
theorem lintegral_midBall_fibre_le' {d : ℕ} {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α) (hd : 0 < d)
    (t z : EuclideanSpace ℝ (Fin d)) :
    ∫⁻ s in {s | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖},
        ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α))
      ≤ ENNReal.ofReal (chainConst' d ϑ α * ‖z - t‖ ^ (-(d : ℝ) - α)) * unitBallVol d := by
  have hsin : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hsin1 : Real.sin ϑ ≤ 1 := Real.sin_le_one ϑ
  have h3 : (3 : ℝ) ≤ 3 / Real.sin ϑ := by
    have hnn : (0 : ℝ) ≤ 3 * (1 - Real.sin ϑ) / Real.sin ϑ := div_nonneg (by linarith) hsin.le
    have heq : 3 + 3 * (1 - Real.sin ϑ) / Real.sin ϑ = 3 / Real.sin ϑ := by field_simp; ring
    linarith [heq]
  have hA : (0 : ℝ) < 2 + 3 / Real.sin ϑ := by linarith
  have hB : (0 : ℝ) < 3 / Real.sin ϑ - 2 := by linarith
  have hsub := midBall_fibre_subset_closedBall' hv hϑ hϑ' t z
  have hmeas : MeasurableSet {s : EuclideanSpace ℝ (Fin d) |
      z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖} := by
    have h1 : Continuous fun s : EuclideanSpace ℝ (Fin d) => dist z (midCentre v ϑ s t) := by
      unfold midCentre; fun_prop
    have h2 : Continuous fun s : EuclideanSpace ℝ (Fin d) => ‖s - t‖ := by fun_prop
    simpa [Metric.mem_closedBall] using (isClosed_le h1 h2).measurableSet
  rcases eq_or_ne z t with rfl | hzt
  · have hball0 : volume (closedBall z (0 : ℝ)) = 0 := by
      rw [volume_closedBall_eq _ le_rfl, zero_pow (Nat.ne_of_gt hd), ENNReal.ofReal_zero, zero_mul]
    have hnull : volume {s : EuclideanSpace ℝ (Fin d) |
        z ∈ closedBall (midCentre v ϑ s z) ‖s - z‖} = 0 := by
      refine measure_mono_null (le_trans hsub (le_of_eq ?_)) hball0
      simp
    rw [setLIntegral_measure_zero _ _ hnull]
    simp
  · have hn : 0 < ‖z - t‖ := by rw [norm_pos_iff]; exact sub_ne_zero_of_ne hzt
    have hexp : -(2 * (d : ℝ)) - α ≤ 0 := by
      have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith
    have hquot : 0 < ‖z - t‖ / (2 + 3 / Real.sin ϑ) := by positivity
    have hAe : (2 + 3 / Real.sin ϑ) ^ (-(2 * (d : ℝ)) - α)
        = ((2 + 3 / Real.sin ϑ) ^ (2 * (d : ℝ) + α))⁻¹ := by
      rw [show -(2 * (d : ℝ)) - α = -(2 * (d : ℝ) + α) from by ring, Real.rpow_neg hA.le]
    have hxe : ‖z - t‖ ^ (-(2 * (d : ℝ)) - α) * ‖z - t‖ ^ ((d : ℕ) : ℝ)
        = ‖z - t‖ ^ (-(d : ℝ) - α) := by
      rw [← Real.rpow_add hn]; congr 1; ring
    have hscalar : (‖z - t‖ / (2 + 3 / Real.sin ϑ)) ^ (-(2 * (d : ℝ)) - α) *
        (‖z - t‖ ^ d / (3 / Real.sin ϑ - 2) ^ d)
        = chainConst' d ϑ α * ‖z - t‖ ^ (-(d : ℝ) - α) := by
      have e1 : (‖z - t‖ / (2 + 3 / Real.sin ϑ)) ^ (-(2 * (d : ℝ)) - α)
          = ‖z - t‖ ^ (-(2 * (d : ℝ)) - α) * (2 + 3 / Real.sin ϑ) ^ (2 * (d : ℝ) + α) := by
        rw [Real.div_rpow hn.le hA.le, hAe, div_eq_mul_inv, inv_inv]
      rw [e1, ← Real.rpow_natCast ‖z - t‖ d, chainConst']
      rw [show ‖z - t‖ ^ (-(2 * (d : ℝ)) - α) * (2 + 3 / Real.sin ϑ) ^ (2 * (d : ℝ) + α) *
            (‖z - t‖ ^ ((d : ℕ) : ℝ) / (3 / Real.sin ϑ - 2) ^ d)
          = (‖z - t‖ ^ (-(2 * (d : ℝ)) - α) * ‖z - t‖ ^ ((d : ℕ) : ℝ)) *
            ((2 + 3 / Real.sin ϑ) ^ (2 * (d : ℝ) + α) / (3 / Real.sin ϑ - 2) ^ d) from by ring,
        hxe]
      ring
    calc ∫⁻ s in {s | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖},
            ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α))
        ≤ ∫⁻ _ in {s | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖},
            ENNReal.ofReal ((‖z - t‖ / (2 + 3 / Real.sin ϑ)) ^ (-(2 * (d : ℝ)) - α)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hmeas] with s hs
          obtain ⟨-, h1⟩ := norm_sub_le_of_mem_midBall hv hϑ hϑ' hs
          refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hquot ?_ hexp)
          rw [div_le_iff₀ hA]
          linarith [h1]
      _ = ENNReal.ofReal ((‖z - t‖ / (2 + 3 / Real.sin ϑ)) ^ (-(2 * (d : ℝ)) - α)) *
            volume {s | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖} := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal ((‖z - t‖ / (2 + 3 / Real.sin ϑ)) ^ (-(2 * (d : ℝ)) - α)) *
            volume (closedBall t (‖z - t‖ / (3 / Real.sin ϑ - 2))) :=
          mul_le_mul' le_rfl (measure_mono hsub)
      _ = ENNReal.ofReal (chainConst' d ϑ α * ‖z - t‖ ^ (-(d : ℝ) - α)) * unitBallVol d := by
          rw [volume_closedBall_eq _ (by positivity), ← mul_assoc,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hquot.le _), div_pow, hscalar]


/-- The `t`-side of `lintegral_swap_fibre`. -/
theorem lintegral_swap_fibre' {d : ℕ} {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α) (hd : 0 < d)
    (t : EuclideanSpace ℝ (Fin d)) {G : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ s, ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)) *
        ∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖, G z
      ≤ ENNReal.ofReal (chainConst' d ϑ α) * unitBallVol d *
        ∫⁻ z in {z | z - t ∈ cone v ϑ}, G z * ENNReal.ofReal (‖z - t‖ ^ (-(d : ℝ) - α)) := by
  have hconeMeas : MeasurableSet {z : EuclideanSpace ℝ (Fin d) | z - t ∈ cone v ϑ} :=
    ((isOpen_cone v ϑ).preimage (by fun_prop)).measurableSet
  have hsinP : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have h3P : (3 : ℝ) ≤ 3 / Real.sin ϑ := by
    have hnn : (0 : ℝ) ≤ 3 * (1 - Real.sin ϑ) / Real.sin ϑ :=
      div_nonneg (by linarith [Real.sin_le_one ϑ]) hsinP.le
    have heq : 3 + 3 * (1 - Real.sin ϑ) / Real.sin ϑ = 3 / Real.sin ϑ := by field_simp; ring
    linarith [heq]
  have hcc : 0 ≤ chainConst' d ϑ α := by
    unfold chainConst'
    exact div_nonneg (Real.rpow_nonneg (by linarith) _) (pow_nonneg (by linarith) d)
  have hwm : Measurable fun s : EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)) := by fun_prop
  have hgraph : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      p.2 ∈ closedBall (midCentre v ϑ p.1 t) ‖p.1 - t‖} := by
    have h1 : Continuous fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        dist p.2 (midCentre v ϑ p.1 t) := by unfold midCentre; fun_prop
    have h2 : Continuous fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ‖p.1 - t‖ := by fun_prop
    simpa [Metric.mem_closedBall] using (isClosed_le h1 h2).measurableSet
  have hfibm : ∀ z : EuclideanSpace ℝ (Fin d),
      MeasurableSet {s | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖} := by
    intro z
    have h1 : Continuous fun s : EuclideanSpace ℝ (Fin d) =>
        dist z (midCentre v ϑ s t) := by unfold midCentre; fun_prop
    have h2 : Continuous fun s : EuclideanSpace ℝ (Fin d) => ‖s - t‖ := by fun_prop
    simpa [Metric.mem_closedBall] using (isClosed_le h1 h2).measurableSet
  set Ψ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun z =>
    {z : EuclideanSpace ℝ (Fin d) | z - t ∈ cone v ϑ}.indicator
      (fun z => ENNReal.ofReal (chainConst' d ϑ α * ‖z - t‖ ^ (-(d : ℝ) - α)) *
        unitBallVol d) z with hΨ
  have hfib : ∀ z, ∫⁻ s in {s | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖},
      ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)) ≤ Ψ z := by
    intro z
    simp only [hΨ]
    by_cases hzc : z - t ∈ cone v ϑ
    · rw [Set.indicator_of_mem (show z ∈ {z : EuclideanSpace ℝ (Fin d) |
        z - t ∈ cone v ϑ} from hzc)]
      exact lintegral_midBall_fibre_le' hv hϑ hϑ' hα hd t z
    · rw [Set.indicator_of_notMem (show z ∉ {z : EuclideanSpace ℝ (Fin d) |
        z - t ∈ cone v ϑ} from hzc)]
      have hball0 : volume (closedBall t (0 : ℝ)) = 0 := by
        rw [volume_closedBall_eq _ le_rfl, zero_pow (Nat.ne_of_gt hd), ENNReal.ofReal_zero,
          zero_mul]
      have hnull : volume {s | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖} = 0 :=
        measure_mono_null
          (le_trans (fibre_subset_singleton_of_notMem_cone' hv hϑ hϑ' hzc) (by simp)) hball0
      rw [setLIntegral_measure_zero _ _ hnull]
  refine le_trans (lintegral_swap_of_fibre_bound
    (W := fun s => closedBall (midCentre v ϑ s t) ‖s - t‖)
    (w := fun s => ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)))
    (fun _ => measurableSet_closedBall) hgraph hwm hG hfibm hfib) ?_
  have hprod : ∀ z, G z * Ψ z = {z : EuclideanSpace ℝ (Fin d) | z - t ∈ cone v ϑ}.indicator
      (fun z => G z * (ENNReal.ofReal (chainConst' d ϑ α * ‖z - t‖ ^ (-(d : ℝ) - α)) *
        unitBallVol d)) z := by
    intro z
    simp only [hΨ]
    by_cases hzc : z - t ∈ cone v ϑ
    · rw [Set.indicator_of_mem (show z ∈ {z : EuclideanSpace ℝ (Fin d) |
        z - t ∈ cone v ϑ} from hzc), Set.indicator_of_mem
        (show z ∈ {z : EuclideanSpace ℝ (Fin d) | z - t ∈ cone v ϑ} from hzc)]
    · rw [Set.indicator_of_notMem (show z ∉ {z : EuclideanSpace ℝ (Fin d) |
        z - t ∈ cone v ϑ} from hzc), Set.indicator_of_notMem
        (show z ∉ {z : EuclideanSpace ℝ (Fin d) | z - t ∈ cone v ϑ} from hzc), mul_zero]
  rw [lintegral_congr hprod, lintegral_indicator hconeMeas,
    ← lintegral_const_mul' _ _
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top unitBallVol_ne_top)]
  refine le_of_eq (lintegral_congr fun z => ?_)
  rw [ENNReal.ofReal_mul hcc]
  ring
/-! ## Assembling the local Poincaré inequality

Averaging bounds the oscillation pointwise; the two exchanges dispose of the two
terms of the chained integrand. Tonelli in the outer pair, once in each order,
puts each term in front of the exchange that handles it. -/

/-- The averaging integral is measurable in the pair, so Tonelli applies to it. -/
theorem measurable_param_midBall {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (ϑ : ℝ)
    {H : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hH : Measurable H) :
    Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ∫⁻ z in closedBall (midCentre v ϑ p.1 p.2) ‖p.1 - p.2‖, H (p, z) := by
  have hset : MeasurableSet {q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      EuclideanSpace ℝ (Fin d) | q.2 ∈ closedBall (midCentre v ϑ q.1.1 q.1.2) ‖q.1.1 - q.1.2‖} := by
    have h1 : Continuous fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
        EuclideanSpace ℝ (Fin d) => dist q.2 (midCentre v ϑ q.1.1 q.1.2) := by
      unfold midCentre; fun_prop
    have h2 : Continuous fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
        EuclideanSpace ℝ (Fin d) => ‖q.1.1 - q.1.2‖ := by fun_prop
    simpa [Metric.mem_closedBall] using (isClosed_le h1 h2).measurableSet
  have heq : (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ∫⁻ z in closedBall (midCentre v ϑ p.1 p.2) ‖p.1 - p.2‖, H (p, z))
      = fun p => ∫⁻ z, {q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
          EuclideanSpace ℝ (Fin d) |
          q.2 ∈ closedBall (midCentre v ϑ q.1.1 q.1.2) ‖q.1.1 - q.1.2‖}.indicator H (p, z) := by
    funext p
    rw [← lintegral_indicator measurableSet_closedBall]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ closedBall (midCentre v ϑ p.1 p.2) ‖p.1 - p.2‖
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (show (p, z) ∈ {q :
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) |
      q.2 ∈ closedBall (midCentre v ϑ q.1.1 q.1.2) ‖q.1.1 - q.1.2‖} from hz)]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (show (p, z) ∉ {q :
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) |
        q.2 ∈ closedBall (midCentre v ϑ q.1.1 q.1.2) ‖q.1.1 - q.1.2‖} from hz)]
  rw [heq]
  exact (hH.indicator hset).lintegral_prod_right'

/-- **The local Poincaré inequality, for pairs sharing a cone direction.**

The flat oscillation of `f` against the weight `‖s − t‖^{-d-α}`, over *all* pairs,
is bounded by the same quantity restricted to pairs that see the cone `Ṽ(v,ϑ)`.
Since the lower bound of (1.4) turns the cone-restricted weight into `k`, this is
`(★)` for a set of points all of whose cones contain a common direction. -/
theorem localPoincare_sameDirection {d : ℕ} {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α) (hd : 0 < d)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) :
    unitBallVol d * ∫⁻ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
        ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α))
      ≤ ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
          (∫⁻ s, ∫⁻ z in {z | z - s ∈ cone v ϑ},
            ENNReal.ofReal (2 * (f z - f s) ^ 2) *
              ENNReal.ofReal (‖z - s‖ ^ (-(d : ℝ) - α)))
        + ENNReal.ofReal (chainConst' d ϑ α) * unitBallVol d *
          (∫⁻ t, ∫⁻ z in {z | z - t ∈ cone v ϑ},
            ENNReal.ofReal (2 * (f t - f z) ^ 2) *
              ENNReal.ofReal (‖z - t‖ ^ (-(d : ℝ) - α))) := by
  set A : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 * (d : ℝ)) - α)) *
      ∫⁻ z in closedBall (midCentre v ϑ p.1 p.2) ‖p.1 - p.2‖,
        ENNReal.ofReal (2 * (f z - f p.1) ^ 2) with hAdef
  set B : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 * (d : ℝ)) - α)) *
      ∫⁻ z in closedBall (midCentre v ϑ p.1 p.2) ‖p.1 - p.2‖,
        ENNReal.ofReal (2 * (f p.2 - f z) ^ 2) with hBdef
  have hw2m : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 * (d : ℝ)) - α)) := by fun_prop
  have hHA : Measurable fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (2 * (f q.2 - f q.1.1) ^ 2) := by fun_prop
  have hHB : Measurable fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (2 * (f q.1.2 - f q.2) ^ 2) := by fun_prop
  have hGs : ∀ s : EuclideanSpace ℝ (Fin d),
      Measurable fun z => ENNReal.ofReal (2 * (f z - f s) ^ 2) := by intro s; fun_prop
  have hGt : ∀ t : EuclideanSpace ℝ (Fin d),
      Measurable fun z => ENNReal.ofReal (2 * (f t - f z) ^ 2) := by intro t; fun_prop
  have hAm : Measurable A := by
    rw [hAdef]; exact hw2m.mul (measurable_param_midBall v ϑ hHA)
  have hBm : Measurable B := by
    rw [hBdef]; exact hw2m.mul (measurable_param_midBall v ϑ hHB)
  -- the pointwise bound
  have hptwise : ∀ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
        ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α)) * unitBallVol d ≤ A p + B p := by
    rintro ⟨s, t⟩
    refine le_trans (osc_weighted_le v ϑ hα f s t) (le_of_eq ?_)
    rw [hAdef, hBdef, ← mul_add]
    congr 1
    rw [← lintegral_add_left (by fun_prop)]
    refine setLIntegral_congr_fun measurableSet_closedBall fun z _ => ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  calc unitBallVol d * ∫⁻ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α))
      = ∫⁻ p, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α)) * unitBallVol d := by
        rw [← lintegral_const_mul' _ _ unitBallVol_ne_top]
        exact lintegral_congr fun p => by ring
    _ ≤ ∫⁻ p, (A p + B p) := lintegral_mono hptwise
    _ = (∫⁻ p, A p) + ∫⁻ p, B p := lintegral_add_left hAm _
    _ ≤ ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
          (∫⁻ s, ∫⁻ z in {z | z - s ∈ cone v ϑ},
            ENNReal.ofReal (2 * (f z - f s) ^ 2) *
              ENNReal.ofReal (‖z - s‖ ^ (-(d : ℝ) - α)))
        + ENNReal.ofReal (chainConst' d ϑ α) * unitBallVol d *
          (∫⁻ t, ∫⁻ z in {z | z - t ∈ cone v ϑ},
            ENNReal.ofReal (2 * (f t - f z) ^ 2) *
              ENNReal.ofReal (‖z - t‖ ^ (-(d : ℝ) - α))) := by
        refine add_le_add ?_ ?_
        · rw [Measure.volume_eq_prod, lintegral_prod _ hAm.aemeasurable,
            ← lintegral_const_mul' _ _
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top unitBallVol_ne_top)]
          exact lintegral_mono fun s => lintegral_swap_fibre hv hϑ hϑ' hα hd s (hGs s)
        · rw [Measure.volume_eq_prod, lintegral_prod_symm _ hBm.aemeasurable,
            ← lintegral_const_mul' _ _
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top unitBallVol_ne_top)]
          exact lintegral_mono fun t => lintegral_swap_fibre' hv hϑ hϑ' hα hd t (hGt t)


/-! ## The open statement, for configurations with a common cone direction

The lower bound of (1.4) turns the cone-restricted weight into `k`, so the local
Poincaré inequality above becomes exactly the statement §3.2 is missing —
restricted to configurations all of whose cones share a direction. -/

/-- On a cone pair the jump kernel is dominated by `Λ k`: the lower bound of
(1.4), read in the direction that gives information. -/
theorem jumpKernel_le_of_mem_coneAt {d : ℕ} {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {α Λ : ℝ} {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) {x y : EuclideanSpace ℝ (Fin d)} (hxy : y ∈ coneAt Γ x) :
    jumpKernel d α x y ≤ ENNReal.ofReal Λ * k x y := by
  have hΛ : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hk.one_le
  have hind : (1 : ℝ≥0∞) ≤ indE (coneAt Γ x) y + indE (coneAt Γ y) x := by
    have h1 : indE (coneAt Γ x) y = 1 := by simp [indE, Set.indicator_of_mem hxy]
    rw [h1]; exact le_self_add
  have hlow : ENNReal.ofReal Λ⁻¹ * jumpKernel d α x y ≤ k x y := by
    refine le_trans (mul_le_mul' le_rfl ?_) (hk.lower x y)
    calc jumpKernel d α x y = 1 * jumpKernel d α x y := (one_mul _).symm
      _ ≤ (indE (coneAt Γ x) y + indE (coneAt Γ y) x) * jumpKernel d α x y :=
          mul_le_mul' hind le_rfl
  calc jumpKernel d α x y
      = ENNReal.ofReal Λ * (ENNReal.ofReal Λ⁻¹ * jumpKernel d α x y) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hΛ),
          mul_inv_cancel₀ (ne_of_gt hΛ), ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal Λ * k x y := mul_le_mul' le_rfl hlow

/-- **The open statement of §3.2, for configurations with a common cone
direction.** If every cone of `Γ` contains a fixed `Ṽ(v,ϑ)`, then finiteness of
the `H_k` form forces finiteness of the `H^{α/2}` form, with an explicit
constant.

This is the model case of what §3.2 needs. The general case — points whose cones
share no direction — remains open; see the header of this file. -/
theorem formHs_le_form_of_commonDirection {d : ℕ} {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α) (hd : 0 < d)
    {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {Λ : ℝ}
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (hcommon : ∀ x, cone v ϑ ⊆ (Γ x).carrier)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    unitBallVol d * formHs Set.univ α f
      ≤ ENNReal.ofReal (2 * Λ) *
          (ENNReal.ofReal (chainConst d ϑ α) + ENNReal.ofReal (chainConst' d ϑ α)) *
          unitBallVol d * form Set.univ k f := by
  have hΛ : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hk.one_le
  -- the `H_k` form as an iterated integral
  have hform : form Set.univ k f
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((f y - f x) ^ 2) * k x y := by
    rw [form, Set.univ_prod_univ, setLIntegral_univ, Measure.volume_eq_prod,
      lintegral_prod _ hkm.aemeasurable]
  -- each cone-restricted term is dominated by the `H_k` form
  have hconeMeas : ∀ x : EuclideanSpace ℝ (Fin d),
      MeasurableSet {y : EuclideanSpace ℝ (Fin d) | y - x ∈ cone v ϑ} := fun x =>
    ((isOpen_cone v ϑ).preimage (by fun_prop)).measurableSet
  have hterm : ∀ (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ),
      (∀ x y, (g x y) ^ 2 = (f y - f x) ^ 2) →
      (∫⁻ x, ∫⁻ y in {y | y - x ∈ cone v ϑ},
          ENNReal.ofReal (2 * (g x y) ^ 2) * ENNReal.ofReal (‖y - x‖ ^ (-(d : ℝ) - α)))
        ≤ ENNReal.ofReal (2 * Λ) * form Set.univ k f := by
    intro g hg
    rw [hform, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ∫⁻ y in {y | y - x ∈ cone v ϑ},
          ENNReal.ofReal (2 * (g x y) ^ 2) * ENNReal.ofReal (‖y - x‖ ^ (-(d : ℝ) - α))
        ≤ ∫⁻ y in {y | y - x ∈ cone v ϑ},
            ENNReal.ofReal (2 * Λ) * (ENNReal.ofReal ((f y - f x) ^ 2) * k x y) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem (hconeMeas x)] with y hyc
          have hmem : y ∈ coneAt Γ x := hcommon x hyc
          have hjk : ENNReal.ofReal (‖y - x‖ ^ (-(d : ℝ) - α)) ≤ ENNReal.ofReal Λ * k x y := by
            have h0 : ENNReal.ofReal (‖y - x‖ ^ (-(d : ℝ) - α)) = jumpKernel d α x y := by
              rw [jumpKernel, norm_sub_rev]
            rw [h0]; exact jumpKernel_le_of_mem_coneAt hk hmem
          calc ENNReal.ofReal (2 * (g x y) ^ 2) * ENNReal.ofReal (‖y - x‖ ^ (-(d : ℝ) - α))
              ≤ ENNReal.ofReal (2 * (f y - f x) ^ 2) * (ENNReal.ofReal Λ * k x y) := by
                rw [hg]; exact mul_le_mul' le_rfl hjk
            _ = ENNReal.ofReal (2 * Λ) * (ENNReal.ofReal ((f y - f x) ^ 2) * k x y) := by
                rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
                  ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
                ring
      _ ≤ ∫⁻ y, ENNReal.ofReal (2 * Λ) * (ENNReal.ofReal ((f y - f x) ^ 2) * k x y) := by
          exact lintegral_mono' Measure.restrict_le_self le_rfl
  -- assemble
  have hlhs : unitBallVol d * formHs Set.univ α f
      = unitBallVol d * ∫⁻ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
            ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α)) := by
    rw [formHs, form, Set.univ_prod_univ, setLIntegral_univ]
    rfl
  rw [hlhs]
  refine le_trans (localPoincare_sameDirection hv hϑ hϑ' hα hd hf) ?_
  have hA := hterm (fun x y => f y - f x) (fun x y => rfl)
  have hB := hterm (fun x y => f x - f y) (fun x y => by ring)
  calc ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
        (∫⁻ s, ∫⁻ z in {z | z - s ∈ cone v ϑ},
          ENNReal.ofReal (2 * (f z - f s) ^ 2) * ENNReal.ofReal (‖z - s‖ ^ (-(d : ℝ) - α)))
      + ENNReal.ofReal (chainConst' d ϑ α) * unitBallVol d *
        (∫⁻ t, ∫⁻ z in {z | z - t ∈ cone v ϑ},
          ENNReal.ofReal (2 * (f t - f z) ^ 2) * ENNReal.ofReal (‖z - t‖ ^ (-(d : ℝ) - α)))
      ≤ ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
          (ENNReal.ofReal (2 * Λ) * form Set.univ k f)
        + ENNReal.ofReal (chainConst' d ϑ α) * unitBallVol d *
          (ENNReal.ofReal (2 * Λ) * form Set.univ k f) :=
        add_le_add (mul_le_mul' le_rfl hA) (mul_le_mul' le_rfl hB)
    _ = ENNReal.ofReal (2 * Λ) *
          (ENNReal.ofReal (chainConst d ϑ α) + ENNReal.ofReal (chainConst' d ϑ α)) *
          unitBallVol d * form Set.univ k f := by ring


/-! ## Localising to a set

Corollary 2.4 reduces a configuration to finitely many cone types, so `ℝ^d`
splits into finitely many measurable pieces `U_m` on which a common direction is
available. To exploit that, the chaining estimate must hold with the *endpoints*
confined to a set — the intermediate point `z` may still range freely, since the
conversion to `k` only ever uses the cone at an endpoint. Restricting the outer
integrals is all that is required; the exchange lemmas apply unchanged. -/

/-- `localPoincare_sameDirection` with both endpoints confined to `U`. -/
theorem localPoincare_sameDirection_on {d : ℕ} {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α) (hd : 0 < d)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    (U : Set (EuclideanSpace ℝ (Fin d))) :
    unitBallVol d * ∫⁻ p in U ×ˢ U,
        ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α))
      ≤ ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
          (∫⁻ s in U, ∫⁻ z in {z | z - s ∈ cone v ϑ},
            ENNReal.ofReal (2 * (f z - f s) ^ 2) *
              ENNReal.ofReal (‖z - s‖ ^ (-(d : ℝ) - α)))
        + ENNReal.ofReal (chainConst' d ϑ α) * unitBallVol d *
          (∫⁻ t in U, ∫⁻ z in {z | z - t ∈ cone v ϑ},
            ENNReal.ofReal (2 * (f t - f z) ^ 2) *
              ENNReal.ofReal (‖z - t‖ ^ (-(d : ℝ) - α))) := by
  set A : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 * (d : ℝ)) - α)) *
      ∫⁻ z in closedBall (midCentre v ϑ p.1 p.2) ‖p.1 - p.2‖,
        ENNReal.ofReal (2 * (f z - f p.1) ^ 2) with hAdef
  set B : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 * (d : ℝ)) - α)) *
      ∫⁻ z in closedBall (midCentre v ϑ p.1 p.2) ‖p.1 - p.2‖,
        ENNReal.ofReal (2 * (f p.2 - f z) ^ 2) with hBdef
  have hw2m : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 * (d : ℝ)) - α)) := by fun_prop
  have hHA : Measurable fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (2 * (f q.2 - f q.1.1) ^ 2) := by fun_prop
  have hHB : Measurable fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (2 * (f q.1.2 - f q.2) ^ 2) := by fun_prop
  have hGs : ∀ s : EuclideanSpace ℝ (Fin d),
      Measurable fun z => ENNReal.ofReal (2 * (f z - f s) ^ 2) := by intro s; fun_prop
  have hGt : ∀ t : EuclideanSpace ℝ (Fin d),
      Measurable fun z => ENNReal.ofReal (2 * (f t - f z) ^ 2) := by intro t; fun_prop
  have hAm : Measurable A := by
    rw [hAdef]; exact hw2m.mul (measurable_param_midBall v ϑ hHA)
  have hBm : Measurable B := by
    rw [hBdef]; exact hw2m.mul (measurable_param_midBall v ϑ hHB)
  have hptwise : ∀ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
        ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α)) * unitBallVol d ≤ A p + B p := by
    rintro ⟨s, t⟩
    refine le_trans (osc_weighted_le v ϑ hα f s t) (le_of_eq ?_)
    rw [hAdef, hBdef, ← mul_add]
    congr 1
    rw [← lintegral_add_left (by fun_prop)]
    refine setLIntegral_congr_fun measurableSet_closedBall fun z _ => ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  calc unitBallVol d * ∫⁻ p in U ×ˢ U,
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α))
      = ∫⁻ p in U ×ˢ U, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α)) * unitBallVol d := by
        rw [← lintegral_const_mul' _ _ unitBallVol_ne_top]
        exact lintegral_congr fun p => by ring
    _ ≤ ∫⁻ p in U ×ˢ U, (A p + B p) := lintegral_mono hptwise
    _ = (∫⁻ p in U ×ˢ U, A p) + ∫⁻ p in U ×ˢ U, B p := lintegral_add_left hAm _
    _ ≤ ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
          (∫⁻ s in U, ∫⁻ z in {z | z - s ∈ cone v ϑ},
            ENNReal.ofReal (2 * (f z - f s) ^ 2) *
              ENNReal.ofReal (‖z - s‖ ^ (-(d : ℝ) - α)))
        + ENNReal.ofReal (chainConst' d ϑ α) * unitBallVol d *
          (∫⁻ t in U, ∫⁻ z in {z | z - t ∈ cone v ϑ},
            ENNReal.ofReal (2 * (f t - f z) ^ 2) *
              ENNReal.ofReal (‖z - t‖ ^ (-(d : ℝ) - α))) := by
        refine add_le_add ?_ ?_
        · rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
            lintegral_prod _ hAm.aemeasurable,
            ← lintegral_const_mul' _ _
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top unitBallVol_ne_top)]
          refine lintegral_mono fun s => ?_
          exact le_trans (lintegral_mono' Measure.restrict_le_self le_rfl)
            (lintegral_swap_fibre hv hϑ hϑ' hα hd s (hGs s))
        · rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
            lintegral_prod_symm _ hBm.aemeasurable,
            ← lintegral_const_mul' _ _
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top unitBallVol_ne_top)]
          refine lintegral_mono fun t => ?_
          exact le_trans (lintegral_mono' Measure.restrict_le_self le_rfl)
            (lintegral_swap_fibre' hv hϑ hϑ' hα hd t (hGt t))


/-- **The diagonal blocks of the type decomposition.** If the points of `U` all
admit the cone direction `v`, then the `H^{α/2}` energy of the pairs *inside* `U`
is controlled by the `H_k` form.

Corollary 2.4 (`QFS.ref_config`) writes `ℝ^d` as finitely many such pieces, so
this settles every diagonal block `U_m × U_m` of the decomposition. What the open
statement still needs are the **cross blocks** `U_m × U_{m'}`, `m ≠ m'`, where the
two endpoints admit no common direction. -/
theorem formHs_le_form_of_commonDirection_on {d : ℕ} {v : EuclideanSpace ℝ (Fin d)}
    (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α) (hd : 0 < d)
    {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {Λ : ℝ}
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hUm : MeasurableSet U)
    (hcommon : ∀ x ∈ U, cone v ϑ ⊆ (Γ x).carrier)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    unitBallVol d * ∫⁻ p in U ×ˢ U,
        ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2
      ≤ ENNReal.ofReal (2 * Λ) *
          (ENNReal.ofReal (chainConst d ϑ α) + ENNReal.ofReal (chainConst' d ϑ α)) *
          unitBallVol d * form Set.univ k f := by
  have hΛ : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hk.one_le
  have hform : form Set.univ k f
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((f y - f x) ^ 2) * k x y := by
    rw [form, Set.univ_prod_univ, setLIntegral_univ, Measure.volume_eq_prod,
      lintegral_prod _ hkm.aemeasurable]
  have hconeMeas : ∀ x : EuclideanSpace ℝ (Fin d),
      MeasurableSet {y : EuclideanSpace ℝ (Fin d) | y - x ∈ cone v ϑ} := fun x =>
    ((isOpen_cone v ϑ).preimage (by fun_prop)).measurableSet
  have hterm : ∀ (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ),
      (∀ x y, (g x y) ^ 2 = (f y - f x) ^ 2) →
      (∫⁻ x in U, ∫⁻ y in {y | y - x ∈ cone v ϑ},
          ENNReal.ofReal (2 * (g x y) ^ 2) * ENNReal.ofReal (‖y - x‖ ^ (-(d : ℝ) - α)))
        ≤ ENNReal.ofReal (2 * Λ) * form Set.univ k f := by
    intro g hg
    rw [hform, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_trans (lintegral_mono_ae ?_) (lintegral_mono' Measure.restrict_le_self le_rfl)
    filter_upwards [ae_restrict_mem hUm] with x hxU
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ∫⁻ y in {y | y - x ∈ cone v ϑ},
          ENNReal.ofReal (2 * (g x y) ^ 2) * ENNReal.ofReal (‖y - x‖ ^ (-(d : ℝ) - α))
        ≤ ∫⁻ y in {y | y - x ∈ cone v ϑ},
            ENNReal.ofReal (2 * Λ) * (ENNReal.ofReal ((f y - f x) ^ 2) * k x y) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem (hconeMeas x)] with y hyc
          have hmem : y ∈ coneAt Γ x := hcommon x hxU hyc
          have hjk : ENNReal.ofReal (‖y - x‖ ^ (-(d : ℝ) - α)) ≤ ENNReal.ofReal Λ * k x y := by
            have h0 : ENNReal.ofReal (‖y - x‖ ^ (-(d : ℝ) - α)) = jumpKernel d α x y := by
              rw [jumpKernel, norm_sub_rev]
            rw [h0]; exact jumpKernel_le_of_mem_coneAt hk hmem
          calc ENNReal.ofReal (2 * (g x y) ^ 2) * ENNReal.ofReal (‖y - x‖ ^ (-(d : ℝ) - α))
              ≤ ENNReal.ofReal (2 * (f y - f x) ^ 2) * (ENNReal.ofReal Λ * k x y) := by
                rw [hg]; exact mul_le_mul' le_rfl hjk
            _ = ENNReal.ofReal (2 * Λ) * (ENNReal.ofReal ((f y - f x) ^ 2) * k x y) := by
                rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
                  ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
                ring
      _ ≤ ∫⁻ y, ENNReal.ofReal (2 * Λ) * (ENNReal.ofReal ((f y - f x) ^ 2) * k x y) :=
          lintegral_mono' Measure.restrict_le_self le_rfl
  have hlhs : ∀ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2
        = ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α)) := fun p => rfl
  rw [lintegral_congr hlhs]
  refine le_trans (localPoincare_sameDirection_on hv hϑ hϑ' hα hd hf U) ?_
  have hA := hterm (fun x y => f y - f x) (fun x y => rfl)
  have hB := hterm (fun x y => f x - f y) (fun x y => by ring)
  calc ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
        (∫⁻ s in U, ∫⁻ z in {z | z - s ∈ cone v ϑ},
          ENNReal.ofReal (2 * (f z - f s) ^ 2) * ENNReal.ofReal (‖z - s‖ ^ (-(d : ℝ) - α)))
      + ENNReal.ofReal (chainConst' d ϑ α) * unitBallVol d *
        (∫⁻ t in U, ∫⁻ z in {z | z - t ∈ cone v ϑ},
          ENNReal.ofReal (2 * (f t - f z) ^ 2) * ENNReal.ofReal (‖z - t‖ ^ (-(d : ℝ) - α)))
      ≤ ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
          (ENNReal.ofReal (2 * Λ) * form Set.univ k f)
        + ENNReal.ofReal (chainConst' d ϑ α) * unitBallVol d *
          (ENNReal.ofReal (2 * Λ) * form Set.univ k f) :=
        add_le_add (mul_le_mul' le_rfl hA) (mul_le_mul' le_rfl hB)
    _ = ENNReal.ofReal (2 * Λ) *
          (ENNReal.ofReal (chainConst d ϑ α) + ENNReal.ofReal (chainConst' d ϑ α)) *
          unitBallVol d * form Set.univ k f := by ring


/-! ## The obstruction to the cross blocks, as a theorem

The cross blocks are not merely harder — one intermediate point provably cannot
handle them. In dimension three, two double cones of aperture `ϑ < π/4` whose
axes are orthogonal and skew are **disjoint**, so no `z` at all lies in both,
let alone a set of positive measure. Chains of length two are therefore
unavoidable, and their middle edge runs between two points whose cones the
configuration assigns arbitrarily — which is exactly the difficulty §§5–6
address, in the discrete setting. -/

/-- Membership of a double cone gives a lower bound on the absolute inner
product with the axis. -/
lemma abs_inner_gt_of_mem_doubleCone {v z : E} {ϑ : ℝ} (hz : z ∈ doubleCone v ϑ) :
    z ≠ 0 ∧ Real.cos ϑ * ‖z‖ < |⟪v, z⟫_ℝ| := by
  rw [mem_doubleCone_iff] at hz
  rcases hz with h | h
  · obtain ⟨hne, hgt⟩ := mem_cone_iff_mul.mp h
    exact ⟨hne, lt_of_lt_of_le hgt (le_abs_self _)⟩
  · obtain ⟨hne, hgt⟩ := mem_cone_iff_mul.mp h
    refine ⟨fun hc => hne (by rw [hc, neg_zero]), ?_⟩
    rw [norm_neg, inner_neg_right] at hgt
    exact lt_of_lt_of_le hgt (neg_le_abs _)

/-- **Two intermediate points are genuinely necessary.** In `ℝ³`, for `ϑ < π/4`,
the double cone of aperture `ϑ` about `e₁` at the origin and the one about `e₂`
at `e₃` have no point in common.

So for two points whose cones point along skew axes there is *no* common
cone-neighbour — the positive-measure ball of `exists_ball_in_two_cones` is not
merely unavailable, the set it would live in is empty. This is why the cross
blocks need chains of length at least two, and why the argument cannot be closed
by the methods of this file. -/
theorem no_common_neighbour_of_skew_axes {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ < π / 4)
    {z : EuclideanSpace ℝ (Fin 3)}
    (h1 : z ∈ doubleCone (EuclideanSpace.single 0 (1 : ℝ)) ϑ)
    (h2 : z - EuclideanSpace.single 2 (1 : ℝ) ∈
      doubleCone (EuclideanSpace.single 1 (1 : ℝ)) ϑ) : False := by
  have hpi := Real.pi_pos
  have hc : 0 < Real.cos ϑ := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith)
  have hsc : Real.sin ϑ ^ 2 + Real.cos ϑ ^ 2 = 1 := Real.sin_sq_add_cos_sq ϑ
  -- `ϑ < π/4` gives `sin ϑ < cos ϑ`
  have hlt : Real.sin ϑ < Real.cos ϑ := by
    have h := Real.cos_pos_of_mem_Ioo (x := ϑ + π / 4) ⟨by linarith, by linarith⟩
    rw [Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four] at h
    have h2' : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    nlinarith [h, h2']
  have hlt2 : Real.sin ϑ ^ 2 < Real.cos ϑ ^ 2 := by nlinarith [hs, hc, hlt]
  -- coordinates
  have hnormsq : ∀ w : EuclideanSpace ℝ (Fin 3),
      ‖w‖ ^ 2 = (w 0) ^ 2 + (w 1) ^ 2 + (w 2) ^ 2 := by
    intro w
    have hsum : ‖w‖ ^ 2 = ∑ i : Fin 3, (w i) ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]
    rw [hsum, Fin.sum_univ_three]
  obtain ⟨-, hA0⟩ := abs_inner_gt_of_mem_doubleCone h1
  obtain ⟨-, hB0⟩ := abs_inner_gt_of_mem_doubleCone h2
  rw [EuclideanSpace.inner_single_left] at hA0 hB0
  simp only [map_one, one_mul] at hA0 hB0
  set w : EuclideanSpace ℝ (Fin 3) := z - EuclideanSpace.single 2 (1 : ℝ) with hwdef
  have hw0 : w 0 = z 0 := by rw [hwdef]; simp
  have hw1 : w 1 = z 1 := by rw [hwdef]; simp
  have hw2 : w 2 = z 2 - 1 := by rw [hwdef]; simp
  -- square both estimates
  have hA : Real.cos ϑ ^ 2 * ((z 0) ^ 2 + (z 1) ^ 2 + (z 2) ^ 2) < (z 0) ^ 2 := by
    have hsq := mul_self_lt_mul_self (by positivity : (0:ℝ) ≤ Real.cos ϑ * ‖z‖) hA0
    have hz2 : Real.cos ϑ ^ 2 * ‖z‖ ^ 2
        = Real.cos ϑ ^ 2 * ((z 0) ^ 2 + (z 1) ^ 2 + (z 2) ^ 2) := by rw [hnormsq z]
    nlinarith [hsq, abs_mul_abs_self (z 0), hz2]
  have hB : Real.cos ϑ ^ 2 * ((z 0) ^ 2 + (z 1) ^ 2 + (z 2 - 1) ^ 2) < (z 1) ^ 2 := by
    have hsq := mul_self_lt_mul_self (by positivity : (0:ℝ) ≤ Real.cos ϑ * ‖w‖) hB0
    rw [hw1] at hsq
    have hn := hnormsq w
    rw [hw0, hw1, hw2] at hn
    have hz2 : Real.cos ϑ ^ 2 * ‖w‖ ^ 2
        = Real.cos ϑ ^ 2 * ((z 0) ^ 2 + (z 1) ^ 2 + (z 2 - 1) ^ 2) := by rw [hn]
    nlinarith [hsq, abs_mul_abs_self (z 1), hz2]
  -- and conclude
  rcases eq_or_ne (z 0) 0 with h0 | h0
  · rw [h0] at hA; nlinarith [sq_nonneg (z 1), sq_nonneg (z 2), hc]
  rcases eq_or_ne (z 1) 0 with h1' | h1'
  · rw [h1'] at hB; nlinarith [sq_nonneg (z 0), sq_nonneg (z 2 - 1), hc]
  have hz0 : 0 < (z 0) ^ 2 := by positivity
  have hz1 : 0 < (z 1) ^ 2 := by positivity
  nlinarith [hA, hB, hz0, hz1, hlt2, hsc, sq_nonneg (z 2), sq_nonneg (z 2 - 1),
    mul_pos hz0 hz1]


/-! ## The diagonal blocks of the canonical decomposition

Corollary 2.4 supplies, for any `ϑ`-bounded configuration, a finite family of
reference cones of aperture `ϑ/3` covering it pointwise. The sets
`U_V = {x | V ⊆ Γ(x)}` are measurable by Debreu's condition (carried, as
elsewhere in this repository, as the explicit hypothesis `QFS.CondMeas`), they
cover `ℝ^d`, and on each of them a common cone direction is available. So every
diagonal block is controlled, with **one constant** for all of them: `chainConst`
depends on the aperture, which is `ϑ/3` throughout, and not on the axis. -/

/-- **Every diagonal block of the canonical finite decomposition is controlled.**

The residue of the open statement is therefore exactly the cross blocks
`U_V × U_W` with `V ≠ W`, on which `no_common_neighbour_of_skew_axes` shows the
method of this file cannot work. -/
theorem diagonal_blocks_of_bounded {d : ℕ} (hd : 0 < d) {ϑ α Λ : ℝ}
    (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) (hα : 0 ≤ α)
    {Γ : Configuration (EuclideanSpace ℝ (Fin d))} (hΓ : IsBounded Γ ϑ) (hmeas : CondMeas Γ)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    ∃ 𝒱 : Set (DCone (EuclideanSpace ℝ (Fin d))), 𝒱.Finite ∧
      (∀ x, ∃ V ∈ 𝒱, V.carrier ⊆ (Γ x).carrier) ∧
      (∀ V ∈ 𝒱, V.apex = ϑ / 3) ∧
      ∀ V ∈ 𝒱, unitBallVol d *
          ∫⁻ p in {x | V.carrier ⊆ (Γ x).carrier} ×ˢ {x | V.carrier ⊆ (Γ x).carrier},
            ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2
        ≤ ENNReal.ofReal (2 * Λ) *
            (ENNReal.ofReal (chainConst d (ϑ / 3) α) +
              ENNReal.ofReal (chainConst' d (ϑ / 3) α)) *
            unitBallVol d * form Set.univ k f := by
  obtain ⟨Γ', hfin, hsub, hapex, -⟩ := ref_config hϑ hϑ' Γ hΓ
  refine ⟨Set.range Γ', hfin, fun x => ⟨Γ' x, ⟨x, rfl⟩, hsub x⟩, ?_, ?_⟩
  · rintro V ⟨x, rfl⟩
    exact hapex x
  · rintro V ⟨x, rfl⟩
    have hv : ‖(Γ' x).axis‖ = 1 := (Γ' x).norm_axis
    have hθ : 0 < ϑ / 3 := by positivity
    have hθ' : ϑ / 3 ≤ π / 2 := by linarith [Real.pi_pos]
    have hcommon : ∀ y ∈ {x' | (Γ' x).carrier ⊆ (Γ x').carrier},
        cone (Γ' x).axis (ϑ / 3) ⊆ (Γ y).carrier := by
      intro y hy
      refine le_trans ?_ hy
      rw [← hapex x]
      exact Set.subset_union_left
    have := formHs_le_form_of_commonDirection_on (v := (Γ' x).axis) hv hθ hθ' hα hd hk
      (U := {x' | (Γ' x).carrier ⊆ (Γ x').carrier}) (hmeas _) hcommon hf hkm
    simpa [hapex x] using this


/-! ## Dimension two: the toolkit

In the plane the cross blocks *are* reachable: two double cones whose axes are
not parallel have intersecting axis-lines, and the "not already a cone pair"
condition supplies exactly the quantitative separation the chaining needs. The
first step is a concrete orthogonal complement. -/

/-- The rotation of `w` by a quarter turn, in coordinates. -/
noncomputable def perp2 (w : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![-(w 1), w 0]

@[simp] lemma perp2_apply_zero (w : EuclideanSpace ℝ (Fin 2)) : perp2 w 0 = -(w 1) := rfl

@[simp] lemma perp2_apply_one (w : EuclideanSpace ℝ (Fin 2)) : perp2 w 1 = w 0 := rfl

lemma real_inner_eq_two (x y : EuclideanSpace ℝ (Fin 2)) :
    ⟪x, y⟫_ℝ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

lemma norm_sq_eq_two (x : EuclideanSpace ℝ (Fin 2)) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, real_inner_eq_two]
  ring

@[simp] lemma inner_perp2_self (w : EuclideanSpace ℝ (Fin 2)) : ⟪w, perp2 w⟫_ℝ = 0 := by
  rw [real_inner_eq_two]; simp; ring

lemma norm_perp2 (w : EuclideanSpace ℝ (Fin 2)) : ‖perp2 w‖ = ‖w‖ := by
  have h : ‖perp2 w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [norm_sq_eq_two, norm_sq_eq_two]; simp; ring
  have h1 : (0:ℝ) ≤ ‖perp2 w‖ := norm_nonneg _
  have h2 : (0:ℝ) ≤ ‖w‖ := norm_nonneg _
  nlinarith [h, h1, h2]

/-- The plane decomposes along `w` and its quarter turn. -/
lemma decomp_two {w : EuclideanSpace ℝ (Fin 2)} (hw : ‖w‖ = 1)
    (x : EuclideanSpace ℝ (Fin 2)) :
    x = ⟪w, x⟫_ℝ • w + ⟪perp2 w, x⟫_ℝ • perp2 w := by
  have hw2 : (w 0) ^ 2 + (w 1) ^ 2 = 1 := by
    rw [← norm_sq_eq_two, hw]; norm_num
  refine euclidean_ext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · simp only [real_inner_eq_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      perp2_apply_zero, perp2_apply_one]
    linear_combination (-(x 0)) * hw2
  · simp only [real_inner_eq_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      perp2_apply_zero, perp2_apply_one]
    linear_combination (-(x 1)) * hw2

/-- The component of `x` across the axis `w` is measured by the quarter turn. -/
lemma norm_across_two {w : EuclideanSpace ℝ (Fin 2)} (hw : ‖w‖ = 1)
    (x : EuclideanSpace ℝ (Fin 2)) : ‖across w x‖ = |⟪perp2 w, x⟫_ℝ| := by
  have hd := decomp_two hw x
  have hacross : across w x = ⟪perp2 w, x⟫_ℝ • perp2 w := by
    rw [across]
    nth_rewrite 1 [hd]
    abel
  rw [hacross, norm_smul, Real.norm_eq_abs, norm_perp2, hw, mul_one]


/-- The two-dimensional cross product. -/
def cross2 (x y : EuclideanSpace ℝ (Fin 2)) : ℝ := x 0 * y 1 - x 1 * y 0

lemma inner_perp2_eq_neg_cross (u x : EuclideanSpace ℝ (Fin 2)) :
    ⟪perp2 u, x⟫_ℝ = -cross2 x u := by
  rw [real_inner_eq_two, cross2]
  simp
  ring

lemma norm_across_eq_abs_cross {u : EuclideanSpace ℝ (Fin 2)} (hu : ‖u‖ = 1)
    (x : EuclideanSpace ℝ (Fin 2)) : ‖across u x‖ = |cross2 x u| := by
  rw [norm_across_two hu, inner_perp2_eq_neg_cross, abs_neg]

/-- Cramer's rule in the plane. -/
lemma cramer2 (x a b : EuclideanSpace ℝ (Fin 2)) :
    cross2 x b • a - cross2 x a • b = cross2 a b • x := by
  refine euclidean_ext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;>
    · simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, cross2]
      ring

/-- **The separation supplied by "not already a cone pair".** If `x` does not lie
in the double cone about `u`, then its component across `u` is at least
`‖x‖ sin ϑ`. This is what makes the planar construction quantitative: exactly the
pairs that need chaining are the ones whose geometry is non-degenerate. -/
lemma abs_cross_ge_of_notMem_doubleCone {u : EuclideanSpace ℝ (Fin 2)} (hu : ‖u‖ = 1)
    {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∉ doubleCone u ϑ) : ‖x‖ * Real.sin ϑ ≤ |cross2 x u| := by
  have hs : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos ϑ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hϑ'⟩
  have hsc : Real.sin ϑ ^ 2 + Real.cos ϑ ^ 2 = 1 := Real.sin_sq_add_cos_sq ϑ
  rw [mem_doubleCone_iff] at hx
  simp only [not_or] at hx
  obtain ⟨h1, h2⟩ := hx
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [cross2]
  have hg1 : coneGap u ϑ x ≤ 0 := by
    by_contra hcon
    exact h1 ((mem_cone_iff_coneGap_pos hu hϑ hϑ' x).mpr (not_le.mp hcon))
  have hg2 : coneGap u ϑ (-x) ≤ 0 := by
    by_contra hcon
    exact h2 ((mem_cone_iff_coneGap_pos hu hϑ hϑ' (-x)).mpr (not_le.mp hcon))
  have hacross : across u (-x) = -across u x := by
    simp [across, inner_neg_right, neg_smul]
    abel
  rw [coneGap, hacross, norm_neg, inner_neg_right] at hg2
  rw [coneGap] at hg1
  -- `A := ⟪u,x⟫`, `B := ‖across u x‖`
  have hpy := norm_sq_eq_inner_sq_add hu x
  have hB : ‖across u x‖ = |cross2 x u| := norm_across_eq_abs_cross hu x
  have hBnn : 0 ≤ ‖across u x‖ := norm_nonneg _
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  rw [← hB]
  nlinarith [hg1, hg2, hpy, hBnn, hxn, hs, hc, hsc, sq_nonneg (⟪u, x⟫_ℝ)]


lemma cone_neg_subset_doubleCone (v : E) (ϑ : ℝ) : cone (-v) ϑ ⊆ doubleCone v ϑ := by
  intro h hh
  rw [mem_doubleCone_iff]
  refine Or.inr ⟨neg_ne_zero.mpr hh.1, ?_⟩
  have h2 := hh.2
  rw [inner_neg_left] at h2
  rwa [inner_neg_right, norm_neg]

lemma abs_cross_le (u w : EuclideanSpace ℝ (Fin 2)) : |cross2 u w| ≤ ‖u‖ * ‖w‖ := by
  have hinner : ⟪perp2 u, w⟫_ℝ = cross2 u w := by
    rw [inner_perp2_eq_neg_cross, cross2, cross2]; ring
  have := abs_real_inner_le_norm (perp2 u) w
  rw [hinner, norm_perp2] at this
  exact this

/-- The coefficient placing the intersection point on the axis through `s`. -/
noncomputable def planarA (vs vt s t : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  cross2 (t - s) vt / cross2 vs vt

/-- The coefficient placing the intersection point on the axis through `t`. -/
noncomputable def planarB (vs vt s t : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  cross2 (t - s) vs / cross2 vs vt

/-- The intersection point of the two axis-lines: the centre of the planar
averaging ball. -/
noncomputable def planarCtr (vs vt s t : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) := s + planarA vs vt s t • vs

/-- **The planar construction.** In the plane, two points whose cone axes are not
parallel and which are *not already a cone pair* admit a ball of common
cone-neighbours, of radius proportional to their distance.

The two hypotheses are exactly right: if the axes were parallel a common
direction would exist and `exists_ball_in_two_cones` would apply, while if the
pair were already a cone pair no chaining would be needed. What makes the
construction quantitative is that "not already a cone pair" forces the component
of `t − s` across each axis to be at least `‖t − s‖ sin ϑ`
(`abs_cross_ge_of_notMem_doubleCone`) — precisely the separation that keeps the
intersection point of the two axis-lines away from both `s` and `t`. -/
theorem mem_two_cones_of_mem_planarBall {vs vt : EuclideanSpace ℝ (Fin 2)}
    (hvs : ‖vs‖ = 1) (hvt : ‖vt‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    {s t : EuclideanSpace ℝ (Fin 2)} (hst : s ≠ t) (hD : cross2 vs vt ≠ 0)
    (hns : t - s ∉ doubleCone vs ϑ) (hnt : t - s ∉ doubleCone vt ϑ)
    {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ closedBall (planarCtr vs vt s t) (‖t - s‖ * Real.sin ϑ ^ 2 / 2)) :
    y - s ∈ doubleCone vs ϑ ∧ y - t ∈ doubleCone vt ϑ := by
  have hs : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hδ : 0 < ‖t - s‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero_of_ne (Ne.symm hst)
  have hDpos : 0 < |cross2 vs vt| := abs_pos.mpr hD
  have hD1 : |cross2 vs vt| ≤ 1 := by
    have := abs_cross_le vs vt
    rwa [hvs, hvt, mul_one] at this
  set ρ : ℝ := ‖t - s‖ * Real.sin ϑ ^ 2 / 2 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; positivity
  -- a point on an axis, far enough out, carries a ball inside the double cone
  have key : ∀ (u : EuclideanSpace ℝ (Fin 2)), ‖u‖ = 1 → ∀ c : ℝ,
      ‖t - s‖ * Real.sin ϑ ≤ |c| → ∀ y : EuclideanSpace ℝ (Fin 2),
      ‖y - c • u‖ ≤ ρ → y ∈ doubleCone u ϑ := by
    intro u hu c hc y hy
    have hgap : ρ < |c| * Real.sin ϑ := by
      have h1 : ‖t - s‖ * Real.sin ϑ * Real.sin ϑ ≤ |c| * Real.sin ϑ :=
        mul_le_mul_of_nonneg_right hc hs.le
      rw [hρdef]
      nlinarith [h1, hδ, hs]
    rcases lt_or_gt_of_ne (show c ≠ 0 by
      intro hc0
      rw [hc0, abs_zero] at hc
      nlinarith [hδ, hs]) with hneg | hpos
    · refine cone_neg_subset_doubleCone u ϑ ?_
      have hun : ‖-u‖ = 1 := by rw [norm_neg, hu]
      have hcc : c • u = (-c) • (-u) := by rw [smul_neg, neg_smul, neg_neg]
      refine closedBall_subset_cone hun hϑ hϑ' (p := (-c) • (-u)) (ρ := ρ) ?_ ?_
      · rw [coneGap_smul_axis hun ϑ (-c)]
        rw [abs_of_neg hneg] at hgap
        exact hgap
      · rw [Metric.mem_closedBall, dist_eq_norm, ← hcc]
        exact hy
    · refine Set.mem_union_left _ ?_
      refine closedBall_subset_cone hu hϑ hϑ' (p := c • u) (ρ := ρ) ?_ ?_
      · rw [coneGap_smul_axis hu ϑ c]
        rw [abs_of_pos hpos] at hgap
        exact hgap
      · rw [Metric.mem_closedBall, dist_eq_norm]
        exact hy
  -- the intersection point of the two axis-lines
  set a : ℝ := cross2 (t - s) vt / cross2 vs vt with hadef
  set b : ℝ := cross2 (t - s) vs / cross2 vs vt with hbdef
  have hzs : (s + a • vs) - s = a • vs := by abel
  have hzt : (s + a • vs) - t = b • vt := by
    have hcr := cramer2 (t - s) vs vt
    have hsm : a • vs - b • vt = t - s := by
      have h1 : a • vs = (cross2 vs vt)⁻¹ • (cross2 (t - s) vt • vs) := by
        rw [hadef, smul_smul, div_eq_inv_mul]
      have h2 : b • vt = (cross2 vs vt)⁻¹ • (cross2 (t - s) vs • vt) := by
        rw [hbdef, smul_smul, div_eq_inv_mul]
      rw [h1, h2, ← smul_sub, hcr, smul_smul, inv_mul_cancel₀ hD, one_smul]
    have : (s + a • vs) - t = (a • vs - b • vt) - (t - s) + b • vt := by abel
    rw [this, hsm, sub_self, zero_add]
  -- the two lower bounds, from "not already a cone pair"
  have hlowa : ‖t - s‖ * Real.sin ϑ ≤ |a| := by
    have h1 := abs_cross_ge_of_notMem_doubleCone hvt hϑ hϑ' hnt
    rw [hadef, abs_div]
    rw [le_div_iff₀ hDpos]
    nlinarith [h1, hD1, hδ, hs, abs_nonneg (cross2 (t - s) vt)]
  have hlowb : ‖t - s‖ * Real.sin ϑ ≤ |b| := by
    have h1 := abs_cross_ge_of_notMem_doubleCone hvs hϑ hϑ' hns
    rw [hbdef, abs_div]
    rw [le_div_iff₀ hDpos]
    nlinarith [h1, hD1, hδ, hs, abs_nonneg (cross2 (t - s) vs)]
  have hctr : planarCtr vs vt s t = s + a • vs := by
    rw [planarCtr, planarA, ← hadef]
  rw [Metric.mem_closedBall, dist_eq_norm, hctr] at hy
  constructor
  · refine key vs hvs a hlowa (y - s) ?_
    have h : (y - s) - a • vs = y - (s + a • vs) := by abel
    rw [h]; exact hy
  · refine key vt hvt b hlowb (y - t) ?_
    have h : (y - t) - b • vt = y - (s + a • vs) := by rw [← hzt]; abel
    rw [h]; exact hy


/-! ## The planar averaging family, named

To feed the planar balls through `lintegral_swap_of_fibre_bound` they must be an
explicit function of the pair, and the fibre estimate needs the comparability of
`‖z − s‖`, `‖z − t‖` and `‖s − t‖` in **both** directions. -/

lemma planarCtr_sub_left (vs vt s t : EuclideanSpace ℝ (Fin 2)) :
    planarCtr vs vt s t - s = planarA vs vt s t • vs := by
  rw [planarCtr]; abel

lemma planarCtr_sub_right {vs vt : EuclideanSpace ℝ (Fin 2)} (hD : cross2 vs vt ≠ 0)
    (s t : EuclideanSpace ℝ (Fin 2)) :
    planarCtr vs vt s t - t = planarB vs vt s t • vt := by
  have hcr := cramer2 (t - s) vs vt
  have hsm : planarA vs vt s t • vs - planarB vs vt s t • vt = t - s := by
    have h1 : planarA vs vt s t • vs
        = (cross2 vs vt)⁻¹ • (cross2 (t - s) vt • vs) := by
      rw [planarA, smul_smul, div_eq_inv_mul]
    have h2 : planarB vs vt s t • vt
        = (cross2 vs vt)⁻¹ • (cross2 (t - s) vs • vt) := by
      rw [planarB, smul_smul, div_eq_inv_mul]
    rw [h1, h2, ← smul_sub, hcr, smul_smul, inv_mul_cancel₀ hD, one_smul]
  have hrw : planarCtr vs vt s t - t
      = (planarA vs vt s t • vs - planarB vs vt s t • vt) - (t - s)
        + planarB vs vt s t • vt := by
    rw [planarCtr]; abel
  rw [hrw, hsm, sub_self, zero_add]

lemma norm_planarCtr_sub_left (vs vt s t : EuclideanSpace ℝ (Fin 2)) (hvs : ‖vs‖ = 1) :
    ‖planarCtr vs vt s t - s‖ = |planarA vs vt s t| := by
  rw [planarCtr_sub_left, norm_smul, Real.norm_eq_abs, hvs, mul_one]

lemma norm_planarCtr_sub_right {vs vt : EuclideanSpace ℝ (Fin 2)} (hD : cross2 vs vt ≠ 0)
    (s t : EuclideanSpace ℝ (Fin 2)) (hvt : ‖vt‖ = 1) :
    ‖planarCtr vs vt s t - t‖ = |planarB vs vt s t| := by
  rw [planarCtr_sub_right hD, norm_smul, Real.norm_eq_abs, hvt, mul_one]

/-- The coefficients are comparable to `‖t − s‖`, in both directions. -/
lemma planarA_bounds {vs vt : EuclideanSpace ℝ (Fin 2)} (hvs : ‖vs‖ = 1) (hvt : ‖vt‖ = 1)
    {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {s t : EuclideanSpace ℝ (Fin 2)}
    (hD : cross2 vs vt ≠ 0) (hnt : t - s ∉ doubleCone vt ϑ) :
    ‖t - s‖ * Real.sin ϑ ≤ |planarA vs vt s t| ∧
      |planarA vs vt s t| ≤ ‖t - s‖ / |cross2 vs vt| := by
  have hDpos : 0 < |cross2 vs vt| := abs_pos.mpr hD
  have hD1 : |cross2 vs vt| ≤ 1 := by
    have h := abs_cross_le vs vt
    rwa [hvs, hvt, mul_one] at h
  have hlow := abs_cross_ge_of_notMem_doubleCone hvt hϑ hϑ' hnt
  have hup : |cross2 (t - s) vt| ≤ ‖t - s‖ := by
    have h := abs_cross_le (t - s) vt
    rwa [hvt, mul_one] at h
  have habs : |planarA vs vt s t| = |cross2 (t - s) vt| / |cross2 vs vt| := by
    rw [planarA, abs_div]
  have hsinnn : 0 ≤ Real.sin ϑ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hϑ.le (by linarith [Real.pi_pos])
  constructor
  · rw [habs, le_div_iff₀ hDpos]
    calc ‖t - s‖ * Real.sin ϑ * |cross2 vs vt|
        ≤ ‖t - s‖ * Real.sin ϑ * 1 :=
          mul_le_mul_of_nonneg_left hD1 (by positivity)
      _ = ‖t - s‖ * Real.sin ϑ := mul_one _
      _ ≤ |cross2 (t - s) vt| := hlow
  · rw [habs]
    gcongr

lemma planarB_bounds {vs vt : EuclideanSpace ℝ (Fin 2)} (hvs : ‖vs‖ = 1) (hvt : ‖vt‖ = 1)
    {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {s t : EuclideanSpace ℝ (Fin 2)}
    (hD : cross2 vs vt ≠ 0) (hns : t - s ∉ doubleCone vs ϑ) :
    ‖t - s‖ * Real.sin ϑ ≤ |planarB vs vt s t| ∧
      |planarB vs vt s t| ≤ ‖t - s‖ / |cross2 vs vt| := by
  have hDpos : 0 < |cross2 vs vt| := abs_pos.mpr hD
  have hD1 : |cross2 vs vt| ≤ 1 := by
    have h := abs_cross_le vs vt
    rwa [hvs, hvt, mul_one] at h
  have hlow := abs_cross_ge_of_notMem_doubleCone hvs hϑ hϑ' hns
  have hup : |cross2 (t - s) vs| ≤ ‖t - s‖ := by
    have h := abs_cross_le (t - s) vs
    rwa [hvs, mul_one] at h
  have habs : |planarB vs vt s t| = |cross2 (t - s) vs| / |cross2 vs vt| := by
    rw [planarB, abs_div]
  have hsinnn : 0 ≤ Real.sin ϑ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hϑ.le (by linarith [Real.pi_pos])
  constructor
  · rw [habs, le_div_iff₀ hDpos]
    calc ‖t - s‖ * Real.sin ϑ * |cross2 vs vt|
        ≤ ‖t - s‖ * Real.sin ϑ * 1 :=
          mul_le_mul_of_nonneg_left hD1 (by positivity)
      _ = ‖t - s‖ * Real.sin ϑ := mul_one _
      _ ≤ |cross2 (t - s) vs| := hlow
  · rw [habs]
    gcongr

/-- **Two-sided comparability on the planar averaging ball**, the input the fibre
estimate needs: every point of the ball is at distance comparable to `‖t − s‖`
from both `s` and `t`, in both directions. -/
theorem planarBall_comparable {vs vt : EuclideanSpace ℝ (Fin 2)} (hvs : ‖vs‖ = 1)
    (hvt : ‖vt‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    {s t : EuclideanSpace ℝ (Fin 2)} (hD : cross2 vs vt ≠ 0)
    (hns : t - s ∉ doubleCone vs ϑ) (hnt : t - s ∉ doubleCone vt ϑ)
    {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ closedBall (planarCtr vs vt s t) (‖t - s‖ * Real.sin ϑ ^ 2 / 2)) :
    ‖t - s‖ * Real.sin ϑ / 2 ≤ ‖z - s‖ ∧
      ‖z - s‖ ≤ ‖t - s‖ * (1 / |cross2 vs vt| + 1) ∧
      ‖t - s‖ * Real.sin ϑ / 2 ≤ ‖z - t‖ ∧
      ‖z - t‖ ≤ ‖t - s‖ * (1 / |cross2 vs vt| + 1) := by
  have hDpos : 0 < |cross2 vs vt| := abs_pos.mpr hD
  have hs0 : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hs1 : Real.sin ϑ ≤ 1 := Real.sin_le_one ϑ
  have hδ : 0 ≤ ‖t - s‖ := norm_nonneg _
  obtain ⟨hAlow, hAup⟩ := planarA_bounds hvs hvt hϑ hϑ' hD hnt
  obtain ⟨hBlow, hBup⟩ := planarB_bounds hvs hvt hϑ hϑ' hD hns
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have hAeq := norm_planarCtr_sub_left vs vt s t hvs
  have hBeq := norm_planarCtr_sub_right hD s t hvt
  have hsplit : ∀ c : EuclideanSpace ℝ (Fin 2),
      ‖planarCtr vs vt s t - c‖ - ‖t - s‖ * Real.sin ϑ ^ 2 / 2 ≤ ‖z - c‖ ∧
      ‖z - c‖ ≤ ‖planarCtr vs vt s t - c‖ + ‖t - s‖ * Real.sin ϑ ^ 2 / 2 := by
    intro c
    have h1 : ‖z - c‖ ≤ ‖z - planarCtr vs vt s t‖ + ‖planarCtr vs vt s t - c‖ := by
      have : z - c = (z - planarCtr vs vt s t) + (planarCtr vs vt s t - c) := by abel
      rw [this]; exact norm_add_le _ _
    have h2 : ‖planarCtr vs vt s t - c‖ ≤ ‖planarCtr vs vt s t - z‖ + ‖z - c‖ := by
      have : planarCtr vs vt s t - c = (planarCtr vs vt s t - z) + (z - c) := by abel
      rw [this]; exact norm_add_le _ _
    rw [norm_sub_rev (planarCtr vs vt s t) z] at h2
    constructor <;> linarith
  obtain ⟨hL1, hU1⟩ := hsplit s
  obtain ⟨hL2, hU2⟩ := hsplit t
  rw [hAeq] at hL1 hU1
  rw [hBeq] at hL2 hU2
  have hdiv : ‖t - s‖ / |cross2 vs vt| = ‖t - s‖ * (1 / |cross2 vs vt|) := by ring
  have hsq : Real.sin ϑ ^ 2 ≤ 1 := by nlinarith [hs0, hs1]
  have hprod : ‖t - s‖ * Real.sin ϑ ^ 2 ≤ ‖t - s‖ * 1 := mul_le_mul_of_nonneg_left hsq hδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [hAlow, hL1, hδ, hs0, hs1]
  · rw [hdiv] at hAup; nlinarith [hAup, hU1, hδ, hprod]
  · nlinarith [hBlow, hL2, hδ, hs0, hs1]
  · rw [hdiv] at hBup; nlinarith [hBup, hU2, hδ, hprod]


/-! ## The planar fibre estimate

The averaging family, packaged as a set-valued function with the side conditions
folded in, and the estimate that lets `lintegral_swap_of_fibre_bound` apply to
it. Pairs that are already cone pairs, and the diagonal, get the empty ball —
they need no chaining. -/

/-- The planar averaging ball, with its side conditions folded in. -/
def planarBall (vs vt : EuclideanSpace ℝ (Fin 2)) (ϑ : ℝ)
    (s t : EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {z | s ≠ t ∧ t - s ∉ doubleCone vs ϑ ∧ t - s ∉ doubleCone vt ϑ ∧
    z ∈ closedBall (planarCtr vs vt s t) (‖t - s‖ * Real.sin ϑ ^ 2 / 2)}

/-- Every point of the planar ball sees both cones. -/
theorem mem_two_cones_of_mem_planarBall' {vs vt : EuclideanSpace ℝ (Fin 2)}
    (hvs : ‖vs‖ = 1) (hvt : ‖vt‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    (hD : cross2 vs vt ≠ 0) {s t z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ planarBall vs vt ϑ s t) :
    z - s ∈ doubleCone vs ϑ ∧ z - t ∈ doubleCone vt ϑ :=
  mem_two_cones_of_mem_planarBall hvs hvt hϑ hϑ' hz.1 hD hz.2.1 hz.2.2.1 hz.2.2.2

/-- Two-sided comparability, on the packaged family. -/
theorem planarBall_comparable' {vs vt : EuclideanSpace ℝ (Fin 2)} (hvs : ‖vs‖ = 1)
    (hvt : ‖vt‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) (hD : cross2 vs vt ≠ 0)
    {s t z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ planarBall vs vt ϑ s t) :
    ‖t - s‖ * Real.sin ϑ / 2 ≤ ‖z - s‖ ∧
      ‖z - s‖ ≤ ‖t - s‖ * (1 / |cross2 vs vt| + 1) :=
  let h := planarBall_comparable hvs hvt hϑ hϑ' hD hz.2.1 hz.2.2.1 hz.2.2.2
  ⟨h.1, h.2.1⟩

/-- The constant in the planar fibre estimate. -/
noncomputable def planarConst (vs vt : EuclideanSpace ℝ (Fin 2)) (ϑ α : ℝ) : ℝ :=
  (1 / |cross2 vs vt| + 1) ^ (4 + α) * 4 / Real.sin ϑ ^ 2

/-- **The planar fibre estimate.** The exact analogue of
`lintegral_midBall_fibre_le` for the planar family: the weight `‖s − t‖^{-4-α}`
integrated over the `t`-fibre above `z` returns `‖z − s‖^{-2-α}`. -/
theorem lintegral_planarBall_fibre_le {vs vt : EuclideanSpace ℝ (Fin 2)} (hvs : ‖vs‖ = 1)
    (hvt : ‖vt‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α)
    (hD : cross2 vs vt ≠ 0) (s z : EuclideanSpace ℝ (Fin 2)) :
    ∫⁻ t in {t | z ∈ planarBall vs vt ϑ s t},
        ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α))
      ≤ ENNReal.ofReal (planarConst vs vt ϑ α * ‖z - s‖ ^ (-(2 : ℝ) - α)) * unitBallVol 2 := by
  have hs0 : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hDpos : 0 < |cross2 vs vt| := abs_pos.mpr hD
  have hA : (0 : ℝ) < 1 / |cross2 vs vt| + 1 := by positivity
  -- the fibre sits in a ball of radius comparable to `‖z − s‖`
  have hsub : {t | z ∈ planarBall vs vt ϑ s t}
      ⊆ closedBall s (2 * ‖z - s‖ / Real.sin ϑ) := by
    intro t ht
    obtain ⟨hlow, -⟩ := planarBall_comparable' hvs hvt hϑ hϑ' hD ht
    rw [Metric.mem_closedBall, dist_eq_norm, le_div_iff₀ hs0]
    linarith
  have hmeas : MeasurableSet {t : EuclideanSpace ℝ (Fin 2) | z ∈ planarBall vs vt ϑ s t} := by
    have h1 : MeasurableSet {t : EuclideanSpace ℝ (Fin 2) | s ≠ t} :=
      (measurableSet_singleton s).compl.congr (by ext t; simp [eq_comm, Set.mem_compl_iff])
    have h2 : MeasurableSet {t : EuclideanSpace ℝ (Fin 2) | t - s ∉ doubleCone vs ϑ} :=
      ((isOpen_doubleCone vs ϑ).preimage (by fun_prop)).measurableSet.compl
    have h3 : MeasurableSet {t : EuclideanSpace ℝ (Fin 2) | t - s ∉ doubleCone vt ϑ} :=
      ((isOpen_doubleCone vt ϑ).preimage (by fun_prop)).measurableSet.compl
    have h4 : MeasurableSet {t : EuclideanSpace ℝ (Fin 2) |
        z ∈ closedBall (planarCtr vs vt s t) (‖t - s‖ * Real.sin ϑ ^ 2 / 2)} := by
      have hc1 : Continuous fun t : EuclideanSpace ℝ (Fin 2) =>
          dist z (planarCtr vs vt s t) := by
        unfold planarCtr planarA cross2; fun_prop
      have hc2 : Continuous fun t : EuclideanSpace ℝ (Fin 2) =>
          ‖t - s‖ * Real.sin ϑ ^ 2 / 2 := by fun_prop
      simpa [Metric.mem_closedBall] using (isClosed_le hc1 hc2).measurableSet
    have hEq : {t : EuclideanSpace ℝ (Fin 2) | z ∈ planarBall vs vt ϑ s t}
        = ({t : EuclideanSpace ℝ (Fin 2) | s ≠ t} ∩
            {t : EuclideanSpace ℝ (Fin 2) | t - s ∉ doubleCone vs ϑ} ∩
            {t : EuclideanSpace ℝ (Fin 2) | t - s ∉ doubleCone vt ϑ}) ∩
          {t : EuclideanSpace ℝ (Fin 2) |
            z ∈ closedBall (planarCtr vs vt s t) (‖t - s‖ * Real.sin ϑ ^ 2 / 2)} := by
      ext t
      simp only [planarBall, Set.mem_ofPred_eq, Set.mem_inter_iff]
      tauto
    rw [hEq]
    exact ((h1.inter h2).inter h3).inter h4
  rcases eq_or_ne z s with rfl | hzs
  · have hball0 : volume (closedBall z (0 : ℝ)) = 0 := by
      rw [volume_closedBall_eq _ le_rfl]; norm_num
    have hnull : volume {t : EuclideanSpace ℝ (Fin 2) | z ∈ planarBall vs vt ϑ z t} = 0 := by
      refine measure_mono_null (le_trans hsub (le_of_eq ?_)) hball0
      simp
    rw [setLIntegral_measure_zero _ _ hnull]
    simp
  · have hn : 0 < ‖z - s‖ := by rw [norm_pos_iff]; exact sub_ne_zero_of_ne hzs
    have hexp : -(4 : ℝ) - α ≤ 0 := by linarith
    have hquot : 0 < ‖z - s‖ / (1 / |cross2 vs vt| + 1) := by positivity
    have hpt : ∀ t ∈ {t | z ∈ planarBall vs vt ϑ s t},
        ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α))
          ≤ ENNReal.ofReal ((‖z - s‖ / (1 / |cross2 vs vt| + 1)) ^ (-(4 : ℝ) - α)) := by
      intro t ht
      obtain ⟨-, hup⟩ := planarBall_comparable' hvs hvt hϑ hϑ' hD ht
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hquot ?_ hexp)
      rw [div_le_iff₀ hA, norm_sub_rev s t]
      linarith
    calc ∫⁻ t in {t | z ∈ planarBall vs vt ϑ s t},
            ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α))
        ≤ ∫⁻ _ in {t | z ∈ planarBall vs vt ϑ s t},
            ENNReal.ofReal ((‖z - s‖ / (1 / |cross2 vs vt| + 1)) ^ (-(4 : ℝ) - α)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hmeas] with t ht using hpt t ht
      _ = ENNReal.ofReal ((‖z - s‖ / (1 / |cross2 vs vt| + 1)) ^ (-(4 : ℝ) - α)) *
            volume {t | z ∈ planarBall vs vt ϑ s t} := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal ((‖z - s‖ / (1 / |cross2 vs vt| + 1)) ^ (-(4 : ℝ) - α)) *
            volume (closedBall s (2 * ‖z - s‖ / Real.sin ϑ)) :=
          mul_le_mul' le_rfl (measure_mono hsub)
      _ = ENNReal.ofReal (planarConst vs vt ϑ α * ‖z - s‖ ^ (-(2 : ℝ) - α)) *
            unitBallVol 2 := by
          rw [volume_closedBall_eq _ (by positivity), ← mul_assoc,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hquot.le _)]
          congr 2
          have e1 : (‖z - s‖ / (1 / |cross2 vs vt| + 1)) ^ (-(4 : ℝ) - α)
              = ‖z - s‖ ^ (-(4 : ℝ) - α) * (1 / |cross2 vs vt| + 1) ^ (4 + α) := by
            rw [Real.div_rpow hn.le hA.le,
              show -(4 : ℝ) - α = -(4 + α) from by ring, Real.rpow_neg hA.le,
              div_eq_mul_inv, inv_inv]
          have e2 : (2 * ‖z - s‖ / Real.sin ϑ) ^ 2
              = ‖z - s‖ ^ ((2 : ℕ) : ℝ) * (4 / Real.sin ϑ ^ 2) := by
            rw [Real.rpow_natCast]
            field_simp
            ring
          have e3 : ‖z - s‖ ^ (-(4 : ℝ) - α) * ‖z - s‖ ^ ((2 : ℕ) : ℝ)
              = ‖z - s‖ ^ (-(2 : ℝ) - α) := by
            rw [← Real.rpow_add hn]; congr 1; push_cast; ring
          rw [e1, e2, planarConst]
          rw [show ‖z - s‖ ^ (-(4 : ℝ) - α) * (1 / |cross2 vs vt| + 1) ^ (4 + α) *
                (‖z - s‖ ^ ((2 : ℕ) : ℝ) * (4 / Real.sin ϑ ^ 2))
              = (‖z - s‖ ^ (-(4 : ℝ) - α) * ‖z - s‖ ^ ((2 : ℕ) : ℝ)) *
                ((1 / |cross2 vs vt| + 1) ^ (4 + α) * 4 / Real.sin ϑ ^ 2) from by ring, e3]
          ring


/-- Measurability of the planar family and of its fibres. -/
lemma measurableSet_planarBall {vs vt : EuclideanSpace ℝ (Fin 2)} (ϑ : ℝ)
    (s t : EuclideanSpace ℝ (Fin 2)) : MeasurableSet (planarBall vs vt ϑ s t) := by
  by_cases hP : s ≠ t ∧ t - s ∉ doubleCone vs ϑ ∧ t - s ∉ doubleCone vt ϑ
  · have he : planarBall vs vt ϑ s t
        = closedBall (planarCtr vs vt s t) (‖t - s‖ * Real.sin ϑ ^ 2 / 2) := by
      ext z
      simp only [planarBall, Set.mem_ofPred_eq]
      exact ⟨fun h => h.2.2.2, fun h => ⟨hP.1, hP.2.1, hP.2.2, h⟩⟩
    rw [he]; exact measurableSet_closedBall
  · have he : planarBall vs vt ϑ s t = ∅ := by
      ext z
      simp only [planarBall, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hP ⟨h.1, h.2.1, h.2.2.1⟩
    rw [he]; exact MeasurableSet.empty

lemma measurableSet_planarBall_fibre {vs vt : EuclideanSpace ℝ (Fin 2)} (ϑ : ℝ)
    (s z : EuclideanSpace ℝ (Fin 2)) :
    MeasurableSet {t : EuclideanSpace ℝ (Fin 2) | z ∈ planarBall vs vt ϑ s t} := by
  have h1 : MeasurableSet {t : EuclideanSpace ℝ (Fin 2) | s ≠ t} :=
    (measurableSet_singleton s).compl.congr (by ext t; simp [eq_comm, Set.mem_compl_iff])
  have h2 : MeasurableSet {t : EuclideanSpace ℝ (Fin 2) | t - s ∉ doubleCone vs ϑ} :=
    ((isOpen_doubleCone vs ϑ).preimage (by fun_prop)).measurableSet.compl
  have h3 : MeasurableSet {t : EuclideanSpace ℝ (Fin 2) | t - s ∉ doubleCone vt ϑ} :=
    ((isOpen_doubleCone vt ϑ).preimage (by fun_prop)).measurableSet.compl
  have h4 : MeasurableSet {t : EuclideanSpace ℝ (Fin 2) |
      z ∈ closedBall (planarCtr vs vt s t) (‖t - s‖ * Real.sin ϑ ^ 2 / 2)} := by
    have hc1 : Continuous fun t : EuclideanSpace ℝ (Fin 2) =>
        dist z (planarCtr vs vt s t) := by unfold planarCtr planarA cross2; fun_prop
    have hc2 : Continuous fun t : EuclideanSpace ℝ (Fin 2) =>
        ‖t - s‖ * Real.sin ϑ ^ 2 / 2 := by fun_prop
    simpa [Metric.mem_closedBall] using (isClosed_le hc1 hc2).measurableSet
  have hEq : {t : EuclideanSpace ℝ (Fin 2) | z ∈ planarBall vs vt ϑ s t}
      = ({t : EuclideanSpace ℝ (Fin 2) | s ≠ t} ∩
          {t : EuclideanSpace ℝ (Fin 2) | t - s ∉ doubleCone vs ϑ} ∩
          {t : EuclideanSpace ℝ (Fin 2) | t - s ∉ doubleCone vt ϑ}) ∩
        {t : EuclideanSpace ℝ (Fin 2) |
          z ∈ closedBall (planarCtr vs vt s t) (‖t - s‖ * Real.sin ϑ ^ 2 / 2)} := by
    ext t
    simp only [planarBall, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [hEq]
  exact ((h1.inter h2).inter h3).inter h4

/-- **The exchange, for the planar family.** -/
theorem lintegral_swap_planar {vs vt : EuclideanSpace ℝ (Fin 2)} (hvs : ‖vs‖ = 1)
    (hvt : ‖vt‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α)
    (hD : cross2 vs vt ≠ 0) (s : EuclideanSpace ℝ (Fin 2))
    {G : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ t, ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)) *
        ∫⁻ z in planarBall vs vt ϑ s t, G z
      ≤ ENNReal.ofReal (planarConst vs vt ϑ α) * unitBallVol 2 *
        ∫⁻ z in {z | z - s ∈ doubleCone vs ϑ},
          G z * ENNReal.ofReal (‖z - s‖ ^ (-(2 : ℝ) - α)) := by
  have hs0 : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hDpos : 0 < |cross2 vs vt| := abs_pos.mpr hD
  have hconeMeas : MeasurableSet {z : EuclideanSpace ℝ (Fin 2) | z - s ∈ doubleCone vs ϑ} :=
    ((isOpen_doubleCone vs ϑ).preimage (by fun_prop)).measurableSet
  have hcc : 0 ≤ planarConst vs vt ϑ α := by
    unfold planarConst
    positivity
  have hwm : Measurable fun t : EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)) := by fun_prop
  have hgraph : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
      p.2 ∈ planarBall vs vt ϑ s p.1} := by
    have hne : MeasurableSet {t : EuclideanSpace ℝ (Fin 2) | s ≠ t} := by
      have he : {t : EuclideanSpace ℝ (Fin 2) | s ≠ t}
          = ({s} : Set (EuclideanSpace ℝ (Fin 2)))ᶜ := by
        ext t
        simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff, ne_eq]
        exact ⟨fun h hc => h hc.symm, fun h hc => h hc.symm⟩
      rw [he]
      exact (measurableSet_singleton s).compl
    have h1 : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        s ≠ p.1} := measurable_fst hne
    have h2 : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        p.1 - s ∉ doubleCone vs ϑ} :=
      ((isOpen_doubleCone vs ϑ).preimage (by fun_prop)).measurableSet.compl
    have h3 : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        p.1 - s ∉ doubleCone vt ϑ} :=
      ((isOpen_doubleCone vt ϑ).preimage (by fun_prop)).measurableSet.compl
    have h4 : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        p.2 ∈ closedBall (planarCtr vs vt s p.1) (‖p.1 - s‖ * Real.sin ϑ ^ 2 / 2)} := by
      have hc1 : Continuous fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
          dist p.2 (planarCtr vs vt s p.1) := by unfold planarCtr planarA cross2; fun_prop
      have hc2 : Continuous fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
          ‖p.1 - s‖ * Real.sin ϑ ^ 2 / 2 := by fun_prop
      simpa [Metric.mem_closedBall] using (isClosed_le hc1 hc2).measurableSet
    have hEq : {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        p.2 ∈ planarBall vs vt ϑ s p.1}
        = ({p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) | s ≠ p.1} ∩
            {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
              p.1 - s ∉ doubleCone vs ϑ} ∩
            {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
              p.1 - s ∉ doubleCone vt ϑ}) ∩
          {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
            p.2 ∈ closedBall (planarCtr vs vt s p.1) (‖p.1 - s‖ * Real.sin ϑ ^ 2 / 2)} := by
      ext p
      simp only [planarBall, Set.mem_ofPred_eq, Set.mem_inter_iff]
      tauto
    rw [hEq]
    exact ((h1.inter h2).inter h3).inter h4
  set Ψ : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ := fun z =>
    {z : EuclideanSpace ℝ (Fin 2) | z - s ∈ doubleCone vs ϑ}.indicator
      (fun z => ENNReal.ofReal (planarConst vs vt ϑ α * ‖z - s‖ ^ (-(2 : ℝ) - α)) *
        unitBallVol 2) z with hΨ
  have hfib : ∀ z, ∫⁻ t in {t | z ∈ planarBall vs vt ϑ s t},
      ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)) ≤ Ψ z := by
    intro z
    simp only [hΨ]
    by_cases hzc : z - s ∈ doubleCone vs ϑ
    · rw [Set.indicator_of_mem (show z ∈ {z : EuclideanSpace ℝ (Fin 2) |
        z - s ∈ doubleCone vs ϑ} from hzc)]
      exact lintegral_planarBall_fibre_le hvs hvt hϑ hϑ' hα hD s z
    · rw [Set.indicator_of_notMem (show z ∉ {z : EuclideanSpace ℝ (Fin 2) |
        z - s ∈ doubleCone vs ϑ} from hzc)]
      have hempty : {t : EuclideanSpace ℝ (Fin 2) | z ∈ planarBall vs vt ϑ s t} = ∅ := by
        ext t
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hz
        exact hzc (mem_two_cones_of_mem_planarBall' hvs hvt hϑ hϑ' hD hz).1
      rw [hempty, MeasureTheory.setLIntegral_empty]
  refine le_trans (lintegral_swap_of_fibre_bound
    (W := fun t => planarBall vs vt ϑ s t)
    (w := fun t => ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)))
    (fun t => measurableSet_planarBall ϑ s t) hgraph hwm hG
    (fun z => measurableSet_planarBall_fibre ϑ s z) hfib) ?_
  have hprod : ∀ z, G z * Ψ z
      = {z : EuclideanSpace ℝ (Fin 2) | z - s ∈ doubleCone vs ϑ}.indicator
        (fun z => G z * (ENNReal.ofReal (planarConst vs vt ϑ α * ‖z - s‖ ^ (-(2 : ℝ) - α)) *
          unitBallVol 2)) z := by
    intro z
    simp only [hΨ]
    by_cases hzc : z - s ∈ doubleCone vs ϑ
    · rw [Set.indicator_of_mem (show z ∈ {z : EuclideanSpace ℝ (Fin 2) |
        z - s ∈ doubleCone vs ϑ} from hzc), Set.indicator_of_mem
        (show z ∈ {z : EuclideanSpace ℝ (Fin 2) | z - s ∈ doubleCone vs ϑ} from hzc)]
    · rw [Set.indicator_of_notMem (show z ∉ {z : EuclideanSpace ℝ (Fin 2) |
        z - s ∈ doubleCone vs ϑ} from hzc), Set.indicator_of_notMem
        (show z ∉ {z : EuclideanSpace ℝ (Fin 2) | z - s ∈ doubleCone vs ϑ} from hzc), mul_zero]
  rw [lintegral_congr hprod, lintegral_indicator hconeMeas,
    ← lintegral_const_mul' _ _
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top unitBallVol_ne_top)]
  refine le_of_eq (lintegral_congr fun z => ?_)
  rw [ENNReal.ofReal_mul hcc]
  ring


/-! ### The `t` side of the planar family -/

/-- Two-sided comparability at `t`. -/
theorem planarBall_comparable'' {vs vt : EuclideanSpace ℝ (Fin 2)} (hvs : ‖vs‖ = 1)
    (hvt : ‖vt‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) (hD : cross2 vs vt ≠ 0)
    {s t z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ planarBall vs vt ϑ s t) :
    ‖t - s‖ * Real.sin ϑ / 2 ≤ ‖z - t‖ ∧
      ‖z - t‖ ≤ ‖t - s‖ * (1 / |cross2 vs vt| + 1) :=
  let h := planarBall_comparable hvs hvt hϑ hϑ' hD hz.2.1 hz.2.2.1 hz.2.2.2
  ⟨h.2.2.1, h.2.2.2⟩

lemma measurableSet_planarBall_fibre' {vs vt : EuclideanSpace ℝ (Fin 2)} (ϑ : ℝ)
    (t z : EuclideanSpace ℝ (Fin 2)) :
    MeasurableSet {s : EuclideanSpace ℝ (Fin 2) | z ∈ planarBall vs vt ϑ s t} := by
  have h1 : MeasurableSet {s : EuclideanSpace ℝ (Fin 2) | s ≠ t} := by
    have he : {s : EuclideanSpace ℝ (Fin 2) | s ≠ t}
        = ({t} : Set (EuclideanSpace ℝ (Fin 2)))ᶜ := by
      ext s; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff, ne_eq]
    rw [he]; exact (measurableSet_singleton t).compl
  have h2 : MeasurableSet {s : EuclideanSpace ℝ (Fin 2) | t - s ∉ doubleCone vs ϑ} :=
    ((isOpen_doubleCone vs ϑ).preimage (by fun_prop)).measurableSet.compl
  have h3 : MeasurableSet {s : EuclideanSpace ℝ (Fin 2) | t - s ∉ doubleCone vt ϑ} :=
    ((isOpen_doubleCone vt ϑ).preimage (by fun_prop)).measurableSet.compl
  have h4 : MeasurableSet {s : EuclideanSpace ℝ (Fin 2) |
      z ∈ closedBall (planarCtr vs vt s t) (‖t - s‖ * Real.sin ϑ ^ 2 / 2)} := by
    have hc1 : Continuous fun s : EuclideanSpace ℝ (Fin 2) =>
        dist z (planarCtr vs vt s t) := by unfold planarCtr planarA cross2; fun_prop
    have hc2 : Continuous fun s : EuclideanSpace ℝ (Fin 2) =>
        ‖t - s‖ * Real.sin ϑ ^ 2 / 2 := by fun_prop
    simpa [Metric.mem_closedBall] using (isClosed_le hc1 hc2).measurableSet
  have hEq : {s : EuclideanSpace ℝ (Fin 2) | z ∈ planarBall vs vt ϑ s t}
      = ({s : EuclideanSpace ℝ (Fin 2) | s ≠ t} ∩
          {s : EuclideanSpace ℝ (Fin 2) | t - s ∉ doubleCone vs ϑ} ∩
          {s : EuclideanSpace ℝ (Fin 2) | t - s ∉ doubleCone vt ϑ}) ∩
        {s : EuclideanSpace ℝ (Fin 2) |
          z ∈ closedBall (planarCtr vs vt s t) (‖t - s‖ * Real.sin ϑ ^ 2 / 2)} := by
    ext s
    simp only [planarBall, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [hEq]
  exact ((h1.inter h2).inter h3).inter h4

/-- The `t`-side planar fibre estimate. -/
theorem lintegral_planarBall_fibre_le' {vs vt : EuclideanSpace ℝ (Fin 2)} (hvs : ‖vs‖ = 1)
    (hvt : ‖vt‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α)
    (hD : cross2 vs vt ≠ 0) (t z : EuclideanSpace ℝ (Fin 2)) :
    ∫⁻ s in {s | z ∈ planarBall vs vt ϑ s t},
        ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α))
      ≤ ENNReal.ofReal (planarConst vs vt ϑ α * ‖z - t‖ ^ (-(2 : ℝ) - α)) * unitBallVol 2 := by
  have hs0 : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hDpos : 0 < |cross2 vs vt| := abs_pos.mpr hD
  have hA : (0 : ℝ) < 1 / |cross2 vs vt| + 1 := by positivity
  have hmeas := measurableSet_planarBall_fibre' (vs := vs) (vt := vt) ϑ t z
  have hsub : {s | z ∈ planarBall vs vt ϑ s t} ⊆ closedBall t (2 * ‖z - t‖ / Real.sin ϑ) := by
    intro s hs
    obtain ⟨hlow, -⟩ := planarBall_comparable'' hvs hvt hϑ hϑ' hD hs
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev s t, le_div_iff₀ hs0]
    linarith
  rcases eq_or_ne z t with rfl | hzt
  · have hball0 : volume (closedBall z (0 : ℝ)) = 0 := by
      rw [volume_closedBall_eq _ le_rfl]; norm_num
    have hnull : volume {s : EuclideanSpace ℝ (Fin 2) | z ∈ planarBall vs vt ϑ s z} = 0 := by
      refine measure_mono_null (le_trans hsub (le_of_eq ?_)) hball0
      simp
    rw [setLIntegral_measure_zero _ _ hnull]
    simp
  · have hn : 0 < ‖z - t‖ := by rw [norm_pos_iff]; exact sub_ne_zero_of_ne hzt
    have hexp : -(4 : ℝ) - α ≤ 0 := by linarith
    have hquot : 0 < ‖z - t‖ / (1 / |cross2 vs vt| + 1) := by positivity
    have hpt : ∀ s ∈ {s | z ∈ planarBall vs vt ϑ s t},
        ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α))
          ≤ ENNReal.ofReal ((‖z - t‖ / (1 / |cross2 vs vt| + 1)) ^ (-(4 : ℝ) - α)) := by
      intro s hs
      obtain ⟨-, hup⟩ := planarBall_comparable'' hvs hvt hϑ hϑ' hD hs
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hquot ?_ hexp)
      rw [div_le_iff₀ hA, norm_sub_rev s t]
      linarith
    calc ∫⁻ s in {s | z ∈ planarBall vs vt ϑ s t},
            ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α))
        ≤ ∫⁻ _ in {s | z ∈ planarBall vs vt ϑ s t},
            ENNReal.ofReal ((‖z - t‖ / (1 / |cross2 vs vt| + 1)) ^ (-(4 : ℝ) - α)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hmeas] with s hs using hpt s hs
      _ = ENNReal.ofReal ((‖z - t‖ / (1 / |cross2 vs vt| + 1)) ^ (-(4 : ℝ) - α)) *
            volume {s | z ∈ planarBall vs vt ϑ s t} := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal ((‖z - t‖ / (1 / |cross2 vs vt| + 1)) ^ (-(4 : ℝ) - α)) *
            volume (closedBall t (2 * ‖z - t‖ / Real.sin ϑ)) :=
          mul_le_mul' le_rfl (measure_mono hsub)
      _ = ENNReal.ofReal (planarConst vs vt ϑ α * ‖z - t‖ ^ (-(2 : ℝ) - α)) *
            unitBallVol 2 := by
          rw [volume_closedBall_eq _ (by positivity), ← mul_assoc,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hquot.le _)]
          congr 2
          have e1 : (‖z - t‖ / (1 / |cross2 vs vt| + 1)) ^ (-(4 : ℝ) - α)
              = ‖z - t‖ ^ (-(4 : ℝ) - α) * (1 / |cross2 vs vt| + 1) ^ (4 + α) := by
            rw [Real.div_rpow hn.le hA.le,
              show -(4 : ℝ) - α = -(4 + α) from by ring, Real.rpow_neg hA.le,
              div_eq_mul_inv, inv_inv]
          have e2 : (2 * ‖z - t‖ / Real.sin ϑ) ^ 2
              = ‖z - t‖ ^ ((2 : ℕ) : ℝ) * (4 / Real.sin ϑ ^ 2) := by
            rw [Real.rpow_natCast]
            field_simp
            ring
          have e3 : ‖z - t‖ ^ (-(4 : ℝ) - α) * ‖z - t‖ ^ ((2 : ℕ) : ℝ)
              = ‖z - t‖ ^ (-(2 : ℝ) - α) := by
            rw [← Real.rpow_add hn]; congr 1; push_cast; ring
          rw [e1, e2, planarConst]
          rw [show ‖z - t‖ ^ (-(4 : ℝ) - α) * (1 / |cross2 vs vt| + 1) ^ (4 + α) *
                (‖z - t‖ ^ ((2 : ℕ) : ℝ) * (4 / Real.sin ϑ ^ 2))
              = (‖z - t‖ ^ (-(4 : ℝ) - α) * ‖z - t‖ ^ ((2 : ℕ) : ℝ)) *
                ((1 / |cross2 vs vt| + 1) ^ (4 + α) * 4 / Real.sin ϑ ^ 2) from by ring, e3]
          ring


/-- **The exchange for the planar family, at fixed `t`.** -/
theorem lintegral_swap_planar' {vs vt : EuclideanSpace ℝ (Fin 2)} (hvs : ‖vs‖ = 1)
    (hvt : ‖vt‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α)
    (hD : cross2 vs vt ≠ 0) (t : EuclideanSpace ℝ (Fin 2))
    {G : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ s, ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)) *
        ∫⁻ z in planarBall vs vt ϑ s t, G z
      ≤ ENNReal.ofReal (planarConst vs vt ϑ α) * unitBallVol 2 *
        ∫⁻ z in {z | z - t ∈ doubleCone vt ϑ},
          G z * ENNReal.ofReal (‖z - t‖ ^ (-(2 : ℝ) - α)) := by
  have hs0 : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hDpos : 0 < |cross2 vs vt| := abs_pos.mpr hD
  have hconeMeas : MeasurableSet {z : EuclideanSpace ℝ (Fin 2) | z - t ∈ doubleCone vt ϑ} :=
    ((isOpen_doubleCone vt ϑ).preimage (by fun_prop)).measurableSet
  have hcc : 0 ≤ planarConst vs vt ϑ α := by unfold planarConst; positivity
  have hwm : Measurable fun s : EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)) := by fun_prop
  have hgraph : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
      p.2 ∈ planarBall vs vt ϑ p.1 t} := by
    have hne : MeasurableSet {s : EuclideanSpace ℝ (Fin 2) | s ≠ t} := by
      have he : {s : EuclideanSpace ℝ (Fin 2) | s ≠ t}
          = ({t} : Set (EuclideanSpace ℝ (Fin 2)))ᶜ := by
        ext s; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff, ne_eq]
      rw [he]; exact (measurableSet_singleton t).compl
    have h1 : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        p.1 ≠ t} := measurable_fst hne
    have h2 : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        t - p.1 ∉ doubleCone vs ϑ} :=
      ((isOpen_doubleCone vs ϑ).preimage (by fun_prop)).measurableSet.compl
    have h3 : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        t - p.1 ∉ doubleCone vt ϑ} :=
      ((isOpen_doubleCone vt ϑ).preimage (by fun_prop)).measurableSet.compl
    have h4 : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        p.2 ∈ closedBall (planarCtr vs vt p.1 t) (‖t - p.1‖ * Real.sin ϑ ^ 2 / 2)} := by
      have hc1 : Continuous fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
          dist p.2 (planarCtr vs vt p.1 t) := by unfold planarCtr planarA cross2; fun_prop
      have hc2 : Continuous fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
          ‖t - p.1‖ * Real.sin ϑ ^ 2 / 2 := by fun_prop
      simpa [Metric.mem_closedBall] using (isClosed_le hc1 hc2).measurableSet
    have hEq : {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        p.2 ∈ planarBall vs vt ϑ p.1 t}
        = ({p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) | p.1 ≠ t} ∩
            {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
              t - p.1 ∉ doubleCone vs ϑ} ∩
            {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
              t - p.1 ∉ doubleCone vt ϑ}) ∩
          {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
            p.2 ∈ closedBall (planarCtr vs vt p.1 t) (‖t - p.1‖ * Real.sin ϑ ^ 2 / 2)} := by
      ext p
      simp only [planarBall, Set.mem_ofPred_eq, Set.mem_inter_iff]
      tauto
    rw [hEq]
    exact ((h1.inter h2).inter h3).inter h4
  set Ψ : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ := fun z =>
    {z : EuclideanSpace ℝ (Fin 2) | z - t ∈ doubleCone vt ϑ}.indicator
      (fun z => ENNReal.ofReal (planarConst vs vt ϑ α * ‖z - t‖ ^ (-(2 : ℝ) - α)) *
        unitBallVol 2) z with hΨ
  have hfib : ∀ z, ∫⁻ s in {s | z ∈ planarBall vs vt ϑ s t},
      ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)) ≤ Ψ z := by
    intro z
    simp only [hΨ]
    by_cases hzc : z - t ∈ doubleCone vt ϑ
    · rw [Set.indicator_of_mem (show z ∈ {z : EuclideanSpace ℝ (Fin 2) |
        z - t ∈ doubleCone vt ϑ} from hzc)]
      exact lintegral_planarBall_fibre_le' hvs hvt hϑ hϑ' hα hD t z
    · rw [Set.indicator_of_notMem (show z ∉ {z : EuclideanSpace ℝ (Fin 2) |
        z - t ∈ doubleCone vt ϑ} from hzc)]
      have hempty : {s : EuclideanSpace ℝ (Fin 2) | z ∈ planarBall vs vt ϑ s t} = ∅ := by
        ext s
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hz
        exact hzc (mem_two_cones_of_mem_planarBall' hvs hvt hϑ hϑ' hD hz).2
      rw [hempty, MeasureTheory.setLIntegral_empty]
  refine le_trans (lintegral_swap_of_fibre_bound
    (W := fun s => planarBall vs vt ϑ s t)
    (w := fun s => ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)))
    (fun s => measurableSet_planarBall ϑ s t) hgraph hwm hG
    (fun z => measurableSet_planarBall_fibre' ϑ t z) hfib) ?_
  have hprod : ∀ z, G z * Ψ z
      = {z : EuclideanSpace ℝ (Fin 2) | z - t ∈ doubleCone vt ϑ}.indicator
        (fun z => G z * (ENNReal.ofReal (planarConst vs vt ϑ α * ‖z - t‖ ^ (-(2 : ℝ) - α)) *
          unitBallVol 2)) z := by
    intro z
    simp only [hΨ]
    by_cases hzc : z - t ∈ doubleCone vt ϑ
    · rw [Set.indicator_of_mem (show z ∈ {z : EuclideanSpace ℝ (Fin 2) |
        z - t ∈ doubleCone vt ϑ} from hzc), Set.indicator_of_mem
        (show z ∈ {z : EuclideanSpace ℝ (Fin 2) | z - t ∈ doubleCone vt ϑ} from hzc)]
    · rw [Set.indicator_of_notMem (show z ∉ {z : EuclideanSpace ℝ (Fin 2) |
        z - t ∈ doubleCone vt ϑ} from hzc), Set.indicator_of_notMem
        (show z ∉ {z : EuclideanSpace ℝ (Fin 2) | z - t ∈ doubleCone vt ϑ} from hzc), mul_zero]
  rw [lintegral_congr hprod, lintegral_indicator hconeMeas,
    ← lintegral_const_mul' _ _
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top unitBallVol_ne_top)]
  refine le_of_eq (lintegral_congr fun z => ?_)
  rw [ENNReal.ofReal_mul hcc]
  ring


/-- The volume of a planar ball, when its side conditions hold. -/
lemma volume_planarBall {vs vt : EuclideanSpace ℝ (Fin 2)} {ϑ : ℝ}
    {s t : EuclideanSpace ℝ (Fin 2)} (hne : s ≠ t)
    (h1 : t - s ∉ doubleCone vs ϑ) (h2 : t - s ∉ doubleCone vt ϑ) :
    volume (planarBall vs vt ϑ s t)
      = ENNReal.ofReal ((‖t - s‖ * Real.sin ϑ ^ 2 / 2) ^ 2) * unitBallVol 2 := by
  have he : planarBall vs vt ϑ s t
      = closedBall (planarCtr vs vt s t) (‖t - s‖ * Real.sin ϑ ^ 2 / 2) := by
    ext z
    simp only [planarBall, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2.2.2, fun h => ⟨hne, h1, h2, h⟩⟩
  rw [he, volume_closedBall_eq _ (by positivity)]

/-- **The averaging step for the planar family.** -/
theorem osc_weighted_le_planar {vs vt : EuclideanSpace ℝ (Fin 2)} {ϑ : ℝ}
    {α : ℝ} (f : EuclideanSpace ℝ (Fin 2) → ℝ) {s t : EuclideanSpace ℝ (Fin 2)}
    (hne : s ≠ t) (h1 : t - s ∉ doubleCone vs ϑ) (h2 : t - s ∉ doubleCone vt ϑ) :
    ENNReal.ofReal ((f t - f s) ^ 2) * ENNReal.ofReal (‖s - t‖ ^ (-(2 : ℝ) - α)) *
        (ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2)
      ≤ ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)) *
        ∫⁻ z in planarBall vs vt ϑ s t,
          ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2) := by
  have hδ : 0 < ‖s - t‖ := by rw [norm_pos_iff]; exact sub_ne_zero_of_ne hne
  have hrev : ‖t - s‖ = ‖s - t‖ := norm_sub_rev t s
  -- the flat averaging inequality
  have hflat : ENNReal.ofReal ((f t - f s) ^ 2) * volume (planarBall vs vt ϑ s t)
      ≤ ∫⁻ z in planarBall vs vt ϑ s t,
        ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2) := by
    rw [← setLIntegral_const (planarBall vs vt ϑ s t) (ENNReal.ofReal ((f t - f s) ^ 2))]
    refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
    nlinarith [sq_nonneg (f z - f s - (f t - f z)), sq_nonneg (f z - f s + (f t - f z))]
  -- and the weights match
  have hw : ENNReal.ofReal (‖s - t‖ ^ (-(2 : ℝ) - α)) * ENNReal.ofReal (Real.sin ϑ ^ 4 / 4)
      = ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)) *
        ENNReal.ofReal ((‖t - s‖ * Real.sin ϑ ^ 2 / 2) ^ 2) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), hrev]
    congr 1
    have e : (‖s - t‖ * Real.sin ϑ ^ 2 / 2) ^ 2
        = ‖s - t‖ ^ ((2 : ℕ) : ℝ) * (Real.sin ϑ ^ 4 / 4) := by
      rw [Real.rpow_natCast]; ring
    rw [e, ← mul_assoc, ← Real.rpow_add hδ]
    congr 2
    push_cast
    ring
  calc ENNReal.ofReal ((f t - f s) ^ 2) * ENNReal.ofReal (‖s - t‖ ^ (-(2 : ℝ) - α)) *
        (ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2)
      = ENNReal.ofReal ((f t - f s) ^ 2) *
          (ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)) *
            (ENNReal.ofReal ((‖t - s‖ * Real.sin ϑ ^ 2 / 2) ^ 2) * unitBallVol 2)) := by
        rw [show ENNReal.ofReal ((f t - f s) ^ 2) * ENNReal.ofReal (‖s - t‖ ^ (-(2 : ℝ) - α)) *
              (ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2)
            = ENNReal.ofReal ((f t - f s) ^ 2) *
              ((ENNReal.ofReal (‖s - t‖ ^ (-(2 : ℝ) - α)) *
                ENNReal.ofReal (Real.sin ϑ ^ 4 / 4)) * unitBallVol 2) from by ring, hw]
        ring
    _ = ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)) *
          (ENNReal.ofReal ((f t - f s) ^ 2) * volume (planarBall vs vt ϑ s t)) := by
        rw [volume_planarBall hne h1 h2]; ring
    _ ≤ ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)) *
          ∫⁻ z in planarBall vs vt ϑ s t,
            ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2) :=
        mul_le_mul' le_rfl hflat


/-! ### Assembling the planar cross blocks -/

/-- The graph of the planar family over the pair. -/
lemma measurableSet_planarBall_graph (vs vt : EuclideanSpace ℝ (Fin 2)) (ϑ : ℝ) :
    MeasurableSet {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      EuclideanSpace ℝ (Fin 2) | q.2 ∈ planarBall vs vt ϑ q.1.1 q.1.2} := by
  have hne : MeasurableSet {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      EuclideanSpace ℝ (Fin 2) | q.1.1 ≠ q.1.2} := by
    have h : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        p.1 ≠ p.2} := by
      have he : {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) | p.1 ≠ p.2}
          = {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) | p.1 = p.2}ᶜ := rfl
      rw [he]
      exact (measurableSet_eq_fun measurable_fst measurable_snd).compl
    exact measurable_fst h
  have h2 : MeasurableSet {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      EuclideanSpace ℝ (Fin 2) | q.1.2 - q.1.1 ∉ doubleCone vs ϑ} :=
    ((isOpen_doubleCone vs ϑ).preimage (by fun_prop)).measurableSet.compl
  have h3 : MeasurableSet {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      EuclideanSpace ℝ (Fin 2) | q.1.2 - q.1.1 ∉ doubleCone vt ϑ} :=
    ((isOpen_doubleCone vt ϑ).preimage (by fun_prop)).measurableSet.compl
  have h4 : MeasurableSet {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      EuclideanSpace ℝ (Fin 2) | q.2 ∈ closedBall (planarCtr vs vt q.1.1 q.1.2)
        (‖q.1.2 - q.1.1‖ * Real.sin ϑ ^ 2 / 2)} := by
    have hc1 : Continuous fun q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
        EuclideanSpace ℝ (Fin 2) => dist q.2 (planarCtr vs vt q.1.1 q.1.2) := by
      unfold planarCtr planarA cross2; fun_prop
    have hc2 : Continuous fun q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
        EuclideanSpace ℝ (Fin 2) => ‖q.1.2 - q.1.1‖ * Real.sin ϑ ^ 2 / 2 := by fun_prop
    simpa [Metric.mem_closedBall] using (isClosed_le hc1 hc2).measurableSet
  have hEq : {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      EuclideanSpace ℝ (Fin 2) | q.2 ∈ planarBall vs vt ϑ q.1.1 q.1.2}
      = ({q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
            EuclideanSpace ℝ (Fin 2) | q.1.1 ≠ q.1.2} ∩
          {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
            EuclideanSpace ℝ (Fin 2) | q.1.2 - q.1.1 ∉ doubleCone vs ϑ} ∩
          {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
            EuclideanSpace ℝ (Fin 2) | q.1.2 - q.1.1 ∉ doubleCone vt ϑ}) ∩
        {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
          EuclideanSpace ℝ (Fin 2) | q.2 ∈ closedBall (planarCtr vs vt q.1.1 q.1.2)
            (‖q.1.2 - q.1.1‖ * Real.sin ϑ ^ 2 / 2)} := by
    ext q
    simp only [planarBall, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [hEq]
  exact ((hne.inter h2).inter h3).inter h4

/-- The planar averaging integral is measurable in the pair. -/
theorem measurable_param_planarBall (vs vt : EuclideanSpace ℝ (Fin 2)) (ϑ : ℝ)
    {H : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hH : Measurable H) :
    Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      ∫⁻ z in planarBall vs vt ϑ p.1 p.2, H (p, z) := by
  have hset := measurableSet_planarBall_graph vs vt ϑ
  have heq : (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      ∫⁻ z in planarBall vs vt ϑ p.1 p.2, H (p, z))
      = fun p => ∫⁻ z, {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
          EuclideanSpace ℝ (Fin 2) | q.2 ∈ planarBall vs vt ϑ q.1.1 q.1.2}.indicator H (p, z) := by
    funext p
    rw [← lintegral_indicator (measurableSet_planarBall ϑ p.1 p.2)]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ planarBall vs vt ϑ p.1 p.2
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem
        (show (p, z) ∈ {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
          EuclideanSpace ℝ (Fin 2) | q.2 ∈ planarBall vs vt ϑ q.1.1 q.1.2} from hz)]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem
        (show (p, z) ∉ {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
          EuclideanSpace ℝ (Fin 2) | q.2 ∈ planarBall vs vt ϑ q.1.1 q.1.2} from hz)]
  rw [heq]
  exact (hH.indicator hset).lintegral_prod_right'


/-- **The local Poincaré inequality for planar cross pairs.** On any set `P` of
pairs that are *not* already cone pairs, with the first coordinate in `U` and the
second in `U'`, the flat weighted oscillation is controlled by the cone-restricted
oscillations at the two endpoints. -/
theorem localPoincare_planar {vs vt : EuclideanSpace ℝ (Fin 2)} (hvs : ‖vs‖ = 1)
    (hvt : ‖vt‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α)
    (hD : cross2 vs vt ≠ 0) {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : Measurable f)
    (U U' : Set (EuclideanSpace ℝ (Fin 2))) {P : Set (EuclideanSpace ℝ (Fin 2) ×
      EuclideanSpace ℝ (Fin 2))} (hPm : MeasurableSet P) (hPsub : P ⊆ U ×ˢ U')
    (hP : ∀ p ∈ P, p.1 ≠ p.2 ∧ p.2 - p.1 ∉ doubleCone vs ϑ ∧
      p.2 - p.1 ∉ doubleCone vt ϑ) :
    ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2 *
        ∫⁻ p in P, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α))
      ≤ ENNReal.ofReal (planarConst vs vt ϑ α) * unitBallVol 2 *
          (∫⁻ s in U, ∫⁻ z in {z | z - s ∈ doubleCone vs ϑ},
            ENNReal.ofReal (2 * (f z - f s) ^ 2) *
              ENNReal.ofReal (‖z - s‖ ^ (-(2 : ℝ) - α)))
        + ENNReal.ofReal (planarConst vs vt ϑ α) * unitBallVol 2 *
          (∫⁻ t in U', ∫⁻ z in {z | z - t ∈ doubleCone vt ϑ},
            ENNReal.ofReal (2 * (f t - f z) ^ 2) *
              ENNReal.ofReal (‖z - t‖ ^ (-(2 : ℝ) - α))) := by
  set A : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(4 : ℝ) - α)) *
      ∫⁻ z in planarBall vs vt ϑ p.1 p.2, ENNReal.ofReal (2 * (f z - f p.1) ^ 2) with hAdef
  set B : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(4 : ℝ) - α)) *
      ∫⁻ z in planarBall vs vt ϑ p.1 p.2, ENNReal.ofReal (2 * (f p.2 - f z) ^ 2) with hBdef
  have hw2m : Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(4 : ℝ) - α)) := by fun_prop
  have hHA : Measurable fun q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      EuclideanSpace ℝ (Fin 2) => ENNReal.ofReal (2 * (f q.2 - f q.1.1) ^ 2) := by fun_prop
  have hHB : Measurable fun q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      EuclideanSpace ℝ (Fin 2) => ENNReal.ofReal (2 * (f q.1.2 - f q.2) ^ 2) := by fun_prop
  have hGs : ∀ s : EuclideanSpace ℝ (Fin 2),
      Measurable fun z => ENNReal.ofReal (2 * (f z - f s) ^ 2) := by intro s; fun_prop
  have hGt : ∀ t : EuclideanSpace ℝ (Fin 2),
      Measurable fun z => ENNReal.ofReal (2 * (f t - f z) ^ 2) := by intro t; fun_prop
  have hAm : Measurable A := by
    rw [hAdef]; exact hw2m.mul (measurable_param_planarBall vs vt ϑ hHA)
  have hBm : Measurable B := by
    rw [hBdef]; exact hw2m.mul (measurable_param_planarBall vs vt ϑ hHB)
  have hptwise : ∀ p ∈ P, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
      ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α)) *
        (ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2) ≤ A p + B p := by
    rintro ⟨s, t⟩ hp
    obtain ⟨hne, h1, h2⟩ := hP _ hp
    refine le_trans (osc_weighted_le_planar f hne h1 h2) (le_of_eq ?_)
    rw [hAdef, hBdef, ← mul_add]
    congr 1
    rw [← lintegral_add_left (by fun_prop)]
    refine setLIntegral_congr_fun (measurableSet_planarBall ϑ s t) fun z _ => ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  calc ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2 *
        ∫⁻ p in P, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α))
      = ∫⁻ p in P, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α)) *
          (ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2) := by
        rw [← lintegral_const_mul' _ _
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top unitBallVol_ne_top)]
        exact lintegral_congr fun p => by ring
    _ ≤ ∫⁻ p in P, (A p + B p) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hPm] with p hp using hptwise p hp
    _ ≤ ∫⁻ p in U ×ˢ U', (A p + B p) := lintegral_mono_set hPsub
    _ = (∫⁻ p in U ×ˢ U', A p) + ∫⁻ p in U ×ˢ U', B p := lintegral_add_left hAm _
    _ ≤ ENNReal.ofReal (planarConst vs vt ϑ α) * unitBallVol 2 *
          (∫⁻ s in U, ∫⁻ z in {z | z - s ∈ doubleCone vs ϑ},
            ENNReal.ofReal (2 * (f z - f s) ^ 2) *
              ENNReal.ofReal (‖z - s‖ ^ (-(2 : ℝ) - α)))
        + ENNReal.ofReal (planarConst vs vt ϑ α) * unitBallVol 2 *
          (∫⁻ t in U', ∫⁻ z in {z | z - t ∈ doubleCone vt ϑ},
            ENNReal.ofReal (2 * (f t - f z) ^ 2) *
              ENNReal.ofReal (‖z - t‖ ^ (-(2 : ℝ) - α))) := by
        refine add_le_add ?_ ?_
        · rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
            lintegral_prod _ hAm.aemeasurable,
            ← lintegral_const_mul' _ _
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top unitBallVol_ne_top)]
          refine lintegral_mono fun s => ?_
          exact le_trans (lintegral_mono' Measure.restrict_le_self le_rfl)
            (lintegral_swap_planar hvs hvt hϑ hϑ' hα hD s (hGs s))
        · rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
            lintegral_prod_symm _ hBm.aemeasurable,
            ← lintegral_const_mul' _ _
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top unitBallVol_ne_top)]
          refine lintegral_mono fun t => ?_
          exact le_trans (lintegral_mono' Measure.restrict_le_self le_rfl)
            (lintegral_swap_planar' hvs hvt hϑ hϑ' hα hD t (hGt t))


/-- **The planar cross blocks are controlled.** If the points of `U` all admit the
double cone about `v_s`, those of `U'` the one about `v_t`, and the two axes are
not parallel, then the `H^{α/2}` energy of the pairs in `U × U'` is bounded by the
`H_k` form.

The block splits in two. The pairs that are *already* cone pairs go into the
`H_k` form directly by the lower bound of (1.4); the rest are exactly the pairs
`localPoincare_planar` handles, and its two cone-restricted terms convert by the
same lower bound. -/
theorem formHs_le_form_planar_cross {vs vt : EuclideanSpace ℝ (Fin 2)} (hvs : ‖vs‖ = 1)
    (hvt : ‖vt‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α)
    (hD : cross2 vs vt ≠ 0)
    {Γ : Configuration (EuclideanSpace ℝ (Fin 2))} {Λ : ℝ}
    {k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k)
    {U U' : Set (EuclideanSpace ℝ (Fin 2))} (hUm : MeasurableSet U) (hU'm : MeasurableSet U')
    (hUs : ∀ x ∈ U, doubleCone vs ϑ ⊆ (Γ x).carrier)
    (hUt : ∀ y ∈ U', doubleCone vt ϑ ⊆ (Γ y).carrier)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : Measurable f)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2 *
        ∫⁻ p in U ×ˢ U', ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α))
      ≤ ENNReal.ofReal (planarConst vs vt ϑ α) * unitBallVol 2 *
            (ENNReal.ofReal (2 * Λ) * form Set.univ k f)
        + ENNReal.ofReal (planarConst vs vt ϑ α) * unitBallVol 2 *
            (ENNReal.ofReal (2 * Λ) * form Set.univ k f)
        + ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2 * ENNReal.ofReal Λ *
            form Set.univ k f := by
  have hΛ : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hk.one_le
  have hform : form Set.univ k f
      = ∫⁻ p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2 := by
    rw [form, Set.univ_prod_univ, setLIntegral_univ]
  -- the bad pairs
  set Bad : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
    (U ×ˢ U') ∩ {p | p.1 ≠ p.2 ∧ p.2 - p.1 ∉ doubleCone vs ϑ ∧
      p.2 - p.1 ∉ doubleCone vt ϑ} with hBaddef
  have hBadm : MeasurableSet Bad := by
    rw [hBaddef]
    refine (hUm.prod hU'm).inter ?_
    have h1 : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        p.1 ≠ p.2} := (measurableSet_eq_fun measurable_fst measurable_snd).compl
    have h2 : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        p.2 - p.1 ∉ doubleCone vs ϑ} :=
      ((isOpen_doubleCone vs ϑ).preimage (by fun_prop)).measurableSet.compl
    have h3 : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        p.2 - p.1 ∉ doubleCone vt ϑ} :=
      ((isOpen_doubleCone vt ϑ).preimage (by fun_prop)).measurableSet.compl
    have hEq : {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) | p.1 ≠ p.2 ∧
        p.2 - p.1 ∉ doubleCone vs ϑ ∧ p.2 - p.1 ∉ doubleCone vt ϑ}
        = {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) | p.1 ≠ p.2} ∩
          ({p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
            p.2 - p.1 ∉ doubleCone vs ϑ} ∩
           {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
            p.2 - p.1 ∉ doubleCone vt ϑ}) := rfl
    rw [hEq]
    exact h1.inter (h2.inter h3)
  -- on the good pairs the jump kernel is already dominated by `Λ k`
  have hgood : ∀ p ∈ (U ×ˢ U') \ Bad,
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α))
        ≤ ENNReal.ofReal Λ * (ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) := by
    rintro ⟨s, t⟩ ⟨hmem, hnb⟩
    have hcases : s = t ∨ t - s ∈ doubleCone vs ϑ ∨ t - s ∈ doubleCone vt ϑ := by
      by_contra hc
      simp only [not_or] at hc
      exact hnb ⟨hmem, hc.1, hc.2.1, hc.2.2⟩
    have hjkeq : ENNReal.ofReal (‖s - t‖ ^ (-(2 : ℝ) - α)) = jumpKernel 2 α s t := by
      rw [jumpKernel]; norm_num
    rcases hcases with rfl | hc | hc
    · simp
    · have hmem2 : t ∈ coneAt Γ s := hUs s hmem.1 hc
      rw [hjkeq]
      calc ENNReal.ofReal ((f t - f s) ^ 2) * jumpKernel 2 α s t
          ≤ ENNReal.ofReal ((f t - f s) ^ 2) * (ENNReal.ofReal Λ * k s t) :=
            mul_le_mul' le_rfl (jumpKernel_le_of_mem_coneAt hk hmem2)
        _ = ENNReal.ofReal Λ * (ENNReal.ofReal ((f t - f s) ^ 2) * k s t) := by ring
    · have hneg : s - t ∈ doubleCone vt ϑ := by
        rw [mem_doubleCone_iff] at hc ⊢
        rw [show s - t = -(t - s) from by abel, neg_neg]
        exact hc.symm
      have hmem2 : s ∈ coneAt Γ t := hUt t hmem.2 hneg
      have hjk : jumpKernel 2 α s t ≤ ENNReal.ofReal Λ * k s t := by
        have h0 : jumpKernel 2 α s t = jumpKernel 2 α t s := by
          rw [jumpKernel, jumpKernel, norm_sub_rev]
        rw [h0, hk.symm s t]
        exact jumpKernel_le_of_mem_coneAt hk hmem2
      rw [hjkeq]
      calc ENNReal.ofReal ((f t - f s) ^ 2) * jumpKernel 2 α s t
          ≤ ENNReal.ofReal ((f t - f s) ^ 2) * (ENNReal.ofReal Λ * k s t) :=
            mul_le_mul' le_rfl hjk
        _ = ENNReal.ofReal Λ * (ENNReal.ofReal ((f t - f s) ^ 2) * k s t) := by ring
  -- the cone-restricted terms convert by the same lower bound
  have hterm : ∀ (V : Set (EuclideanSpace ℝ (Fin 2))) (W : Set (EuclideanSpace ℝ (Fin 2))),
      MeasurableSet V → (∀ x ∈ V, W ⊆ (Γ x).carrier) → IsOpen W →
      ∀ (g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ),
      (∀ x y, (g x y) ^ 2 = (f y - f x) ^ 2) →
      (∫⁻ x in V, ∫⁻ y in {y | y - x ∈ W},
          ENNReal.ofReal (2 * (g x y) ^ 2) * ENNReal.ofReal (‖y - x‖ ^ (-(2 : ℝ) - α)))
        ≤ ENNReal.ofReal (2 * Λ) * form Set.univ k f := by
    intro V W hVm hcommon hWopen g hg
    rw [hform, Measure.volume_eq_prod, lintegral_prod _ hkm.aemeasurable,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_trans (lintegral_mono_ae ?_) (lintegral_mono' Measure.restrict_le_self le_rfl)
    filter_upwards [ae_restrict_mem hVm] with x hxV
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hWm : MeasurableSet {y : EuclideanSpace ℝ (Fin 2) | y - x ∈ W} :=
      (hWopen.preimage (by fun_prop)).measurableSet
    calc ∫⁻ y in {y | y - x ∈ W},
          ENNReal.ofReal (2 * (g x y) ^ 2) * ENNReal.ofReal (‖y - x‖ ^ (-(2 : ℝ) - α))
        ≤ ∫⁻ y in {y | y - x ∈ W},
            ENNReal.ofReal (2 * Λ) * (ENNReal.ofReal ((f y - f x) ^ 2) * k x y) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hWm] with y hyc
          have hmem : y ∈ coneAt Γ x := hcommon x hxV hyc
          have hjk : ENNReal.ofReal (‖y - x‖ ^ (-(2 : ℝ) - α)) ≤ ENNReal.ofReal Λ * k x y := by
            have h0 : ENNReal.ofReal (‖y - x‖ ^ (-(2 : ℝ) - α)) = jumpKernel 2 α x y := by
              rw [jumpKernel, norm_sub_rev]
              norm_num
            rw [h0]; exact jumpKernel_le_of_mem_coneAt hk hmem
          calc ENNReal.ofReal (2 * (g x y) ^ 2) *
                ENNReal.ofReal (‖y - x‖ ^ (-(2 : ℝ) - α))
              ≤ ENNReal.ofReal (2 * (f y - f x) ^ 2) * (ENNReal.ofReal Λ * k x y) := by
                rw [hg]; exact mul_le_mul' le_rfl hjk
            _ = ENNReal.ofReal (2 * Λ) * (ENNReal.ofReal ((f y - f x) ^ 2) * k x y) := by
                rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
                  ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
                ring
      _ ≤ ∫⁻ y, ENNReal.ofReal (2 * Λ) * (ENNReal.ofReal ((f y - f x) ^ 2) * k x y) :=
          lintegral_mono' Measure.restrict_le_self le_rfl
  -- split and combine
  set F : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
      ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α)) with hFdef
  have hsplit : ∫⁻ p in U ×ˢ U', F p
      = (∫⁻ p in Bad, F p) + ∫⁻ p in (U ×ˢ U') \ Bad, F p := by
    have hdisj : Disjoint Bad ((U ×ˢ U') \ Bad) := Set.disjoint_sdiff_right
    have hunion : Bad ∪ ((U ×ˢ U') \ Bad) = U ×ˢ U' := by
      rw [Set.union_sdiff_cancel]
      rw [hBaddef]
      exact Set.inter_subset_left
    calc ∫⁻ p in U ×ˢ U', F p
        = ∫⁻ p in Bad ∪ ((U ×ˢ U') \ Bad), F p := by rw [hunion]
      _ = (∫⁻ p in Bad, F p) + ∫⁻ p in (U ×ˢ U') \ Bad, F p :=
          lintegral_union ((hUm.prod hU'm).diff hBadm) hdisj
  rw [hsplit, mul_add]
  refine add_le_add ?_ ?_
  · refine le_trans (localPoincare_planar hvs hvt hϑ hϑ' hα hD hf U U' hBadm
      (by rw [hBaddef]; exact Set.inter_subset_left) (fun p hp => hp.2)) ?_
    exact add_le_add
      (mul_le_mul' le_rfl (hterm U (doubleCone vs ϑ) hUm hUs (isOpen_doubleCone vs ϑ)
        (fun x y => f y - f x) (fun x y => rfl)))
      (mul_le_mul' le_rfl (hterm U' (doubleCone vt ϑ) hU'm hUt (isOpen_doubleCone vt ϑ)
        (fun x y => f x - f y) (fun x y => by ring)))
  · have hg : ∫⁻ p in (U ×ˢ U') \ Bad, F p
        ≤ ENNReal.ofReal Λ * form Set.univ k f := by
      rw [hform, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine le_trans (lintegral_mono_ae ?_) (lintegral_mono' Measure.restrict_le_self le_rfl)
      filter_upwards [ae_restrict_mem ((hUm.prod hU'm).diff hBadm)] with p hp
      exact hgood p hp
    calc ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2 * ∫⁻ p in (U ×ˢ U') \ Bad, F p
        ≤ ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2 *
            (ENNReal.ofReal Λ * form Set.univ k f) := mul_le_mul' le_rfl hg
      _ = ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2 * ENNReal.ofReal Λ *
            form Set.univ k f := by ring


/-! ### The dichotomy in the plane

Two reference cones of the same aperture either have non-parallel axes — and then
`formHs_le_form_planar_cross` applies — or they are the *same* double cone, and
then the block is diagonal and `formHs_le_form_of_commonDirection_on` applies. In
the plane there is no third possibility, which is exactly why the argument
closes here and not in higher dimensions. -/

/-- **Parallel unit vectors in the plane.** If the cross product vanishes, the
two axes agree up to sign — and then the double cones coincide. -/
lemma eq_or_eq_neg_of_cross2_eq_zero {v w : EuclideanSpace ℝ (Fin 2)} (hv : ‖v‖ = 1)
    (hw : ‖w‖ = 1) (h : cross2 v w = 0) : w = v ∨ w = -v := by
  have hperp : ⟪perp2 v, w⟫_ℝ = 0 := by
    rw [inner_perp2_eq_neg_cross]
    have hswap : cross2 w v = -cross2 v w := by rw [cross2, cross2]; ring
    rw [hswap, h, neg_zero, neg_zero]
  have hdec := decomp_two hv w
  rw [hperp, zero_smul, add_zero] at hdec
  have hnorm : |⟪v, w⟫_ℝ| = 1 := by
    have h1 : ‖w‖ = |⟪v, w⟫_ℝ| * ‖v‖ := by
      conv_lhs => rw [hdec]
      rw [norm_smul, Real.norm_eq_abs]
    rw [hv, hw, mul_one] at h1
    exact h1.symm
  rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp hnorm with h1 | h1
  · left; rw [hdec, h1, one_smul]
  · right; rw [hdec, h1, neg_one_smul]

/-- The dichotomy, in the form the assembly uses. -/
theorem cross2_ne_zero_or_carrier_eq {v w : EuclideanSpace ℝ (Fin 2)} (hv : ‖v‖ = 1)
    (hw : ‖w‖ = 1) (ϑ : ℝ) :
    cross2 v w ≠ 0 ∨ doubleCone w ϑ = doubleCone v ϑ := by
  by_cases h : cross2 v w = 0
  · refine Or.inr ?_
    rcases eq_or_eq_neg_of_cross2_eq_zero hv hw h with rfl | rfl
    · rfl
    · exact doubleCone_neg v ϑ
  · exact Or.inl h


/-! ### One block of the planar decomposition -/

lemma unitBallVol_ne_zero (d : ℕ) : unitBallVol d ≠ 0 := by
  rw [unitBallVol]
  exact (measure_closedBall_pos volume (0 : EuclideanSpace ℝ (Fin d)) one_pos).ne'

/-- **Every block of the planar decomposition is controlled**, diagonal or cross.
The dichotomy `cross2_ne_zero_or_carrier_eq` decides which theorem applies. -/
theorem planar_block_le {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α)
    {Γ : Configuration (EuclideanSpace ℝ (Fin 2))} {Λ : ℝ}
    {k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (hmeas : CondMeas Γ)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : Measurable f)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2)
    (V W : DCone (EuclideanSpace ℝ (Fin 2))) (hVW : V.apex = W.apex) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∫⁻ p in {x | V.carrier ⊆ (Γ x).carrier} ×ˢ {x | W.carrier ⊆ (Γ x).carrier},
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
            ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α))
        ≤ C * form Set.univ k f := by
  have hVpos : 0 < V.apex := V.apex_pos
  have hVle : V.apex ≤ π / 2 := V.apex_le
  have hUVm : MeasurableSet {x | V.carrier ⊆ (Γ x).carrier} := hmeas _
  have hUWm : MeasurableSet {x | W.carrier ⊆ (Γ x).carrier} := hmeas _
  have hsin : 0 < Real.sin V.apex :=
    Real.sin_pos_of_pos_of_lt_pi hVpos (by linarith [Real.pi_pos])
  rcases cross2_ne_zero_or_carrier_eq V.norm_axis W.norm_axis V.apex with hD | hcar
  · -- the axes are not parallel: a cross block
    have hUs : ∀ x ∈ {x | V.carrier ⊆ (Γ x).carrier}, doubleCone V.axis V.apex ⊆ (Γ x).carrier :=
      fun x hx => hx
    have hUt : ∀ y ∈ {x | W.carrier ⊆ (Γ x).carrier}, doubleCone W.axis V.apex ⊆ (Γ y).carrier := by
      intro y hy
      rw [hVW]
      exact hy
    have hmain := formHs_le_form_planar_cross V.norm_axis W.norm_axis hVpos hVle hα hD hk
      hUVm hUWm hUs hUt hf hkm
    set κ : ℝ≥0∞ := ENNReal.ofReal (Real.sin V.apex ^ 4 / 4) * unitBallVol 2 with hκ
    have hκ0 : κ ≠ 0 := by
      rw [hκ]
      exact mul_ne_zero (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)
        (unitBallVol_ne_zero 2)
    have hκtop : κ ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top unitBallVol_ne_top
    refine ⟨κ⁻¹ * (ENNReal.ofReal (planarConst V.axis W.axis V.apex α) * unitBallVol 2 *
        ENNReal.ofReal (2 * Λ) + ENNReal.ofReal (planarConst V.axis W.axis V.apex α) *
        unitBallVol 2 * ENNReal.ofReal (2 * Λ) +
        ENNReal.ofReal (Real.sin V.apex ^ 4 / 4) * unitBallVol 2 * ENNReal.ofReal Λ), ?_, ?_⟩
    · refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hκ0) ?_
      refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨?_, ?_⟩, ?_⟩ <;>
        exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top unitBallVol_ne_top)
          ENNReal.ofReal_ne_top
    · calc ∫⁻ p in {x | V.carrier ⊆ (Γ x).carrier} ×ˢ {x | W.carrier ⊆ (Γ x).carrier},
            ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
              ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α))
          = κ⁻¹ * (κ * ∫⁻ p in {x | V.carrier ⊆ (Γ x).carrier} ×ˢ
              {x | W.carrier ⊆ (Γ x).carrier},
              ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
                ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α))) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hκ0 hκtop, one_mul]
        _ ≤ κ⁻¹ * (ENNReal.ofReal (planarConst V.axis W.axis V.apex α) * unitBallVol 2 *
              (ENNReal.ofReal (2 * Λ) * form Set.univ k f)
            + ENNReal.ofReal (planarConst V.axis W.axis V.apex α) * unitBallVol 2 *
              (ENNReal.ofReal (2 * Λ) * form Set.univ k f)
            + ENNReal.ofReal (Real.sin V.apex ^ 4 / 4) * unitBallVol 2 * ENNReal.ofReal Λ *
              form Set.univ k f) := mul_le_mul' le_rfl hmain
        _ = κ⁻¹ * (ENNReal.ofReal (planarConst V.axis W.axis V.apex α) * unitBallVol 2 *
              ENNReal.ofReal (2 * Λ) + ENNReal.ofReal (planarConst V.axis W.axis V.apex α) *
              unitBallVol 2 * ENNReal.ofReal (2 * Λ) +
              ENNReal.ofReal (Real.sin V.apex ^ 4 / 4) * unitBallVol 2 * ENNReal.ofReal Λ) *
            form Set.univ k f := by ring
  · -- the two cones coincide: a diagonal block
    have hcarrier : W.carrier = V.carrier := by
      rw [DCone.carrier, DCone.carrier, ← hVW]
      exact hcar
    have hsets : {x | W.carrier ⊆ (Γ x).carrier} = {x | V.carrier ⊆ (Γ x).carrier} := by
      rw [hcarrier]
    have hcommon : ∀ x ∈ {x | V.carrier ⊆ (Γ x).carrier},
        cone V.axis V.apex ⊆ (Γ x).carrier :=
      fun x hx => le_trans Set.subset_union_left hx
    have hmain := formHs_le_form_of_commonDirection_on V.norm_axis hVpos hVle hα two_pos hk
      hUVm hcommon hf hkm
    refine ⟨(unitBallVol 2)⁻¹ * (ENNReal.ofReal (2 * Λ) *
      (ENNReal.ofReal (chainConst 2 V.apex α) + ENNReal.ofReal (chainConst' 2 V.apex α)) *
      unitBallVol 2), ?_, ?_⟩
    · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (unitBallVol_ne_zero 2))
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩))
          unitBallVol_ne_top)
    · rw [hsets]
      have hconv : ∫⁻ p in {x | V.carrier ⊆ (Γ x).carrier} ×ˢ
          {x | V.carrier ⊆ (Γ x).carrier},
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
            ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α))
          = ∫⁻ p in {x | V.carrier ⊆ (Γ x).carrier} ×ˢ {x | V.carrier ⊆ (Γ x).carrier},
            ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel 2 α p.1 p.2 := by
        refine lintegral_congr fun p => ?_
        rw [jumpKernel]
        norm_num
      rw [hconv]
      calc ∫⁻ p in {x | V.carrier ⊆ (Γ x).carrier} ×ˢ {x | V.carrier ⊆ (Γ x).carrier},
            ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel 2 α p.1 p.2
          = (unitBallVol 2)⁻¹ * (unitBallVol 2 *
              ∫⁻ p in {x | V.carrier ⊆ (Γ x).carrier} ×ˢ {x | V.carrier ⊆ (Γ x).carrier},
                ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel 2 α p.1 p.2) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel (unitBallVol_ne_zero 2) unitBallVol_ne_top,
              one_mul]
        _ ≤ (unitBallVol 2)⁻¹ * (ENNReal.ofReal (2 * Λ) *
              (ENNReal.ofReal (chainConst 2 V.apex α) +
                ENNReal.ofReal (chainConst' 2 V.apex α)) *
              unitBallVol 2 * form Set.univ k f) := mul_le_mul' le_rfl hmain
        _ = (unitBallVol 2)⁻¹ * (ENNReal.ofReal (2 * Λ) *
              (ENNReal.ofReal (chainConst 2 V.apex α) +
                ENNReal.ofReal (chainConst' 2 V.apex α)) * unitBallVol 2) *
            form Set.univ k f := by ring


/-! ## The open statement, in dimension two

Corollary 2.4 covers `ℝ²` by finitely many pieces on each of which a reference
cone is available; the squares of that cover exhaust `ℝ² × ℝ²`; every block is
controlled by `planar_block_le`; and a finite sum of finite constants is
finite. -/

/-- **`H_k ⊆ H^{α/2}` in dimension two**, for every `ϑ`-bounded configuration
satisfying Debreu's measurability condition.

This is the statement §3.2 needs, proved in the plane for *all* admissible
configurations — not only those with a common cone direction. In dimension three
and above it remains open, and `no_common_neighbour_of_skew_axes` shows why the
method used here cannot reach it. -/
theorem sobolevInclusion_planar {ϑ α Λ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) (hα : 0 ≤ α)
    {Γ : Configuration (EuclideanSpace ℝ (Fin 2))} (hΓ : IsBounded Γ ϑ) (hmeas : CondMeas Γ)
    {k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : Measurable f)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ formHs Set.univ α f ≤ C * form Set.univ k f := by
  classical
  obtain ⟨Γ', hfin, hsub, hapex, -⟩ := ref_config hϑ hϑ' Γ hΓ
  have : Fintype ↥(Set.range Γ') := hfin.fintype
  have hap : ∀ V ∈ Set.range Γ', V.apex = ϑ / 3 := by
    rintro V ⟨x, rfl⟩
    exact hapex x
  set blk : ↥(Set.range Γ') × ↥(Set.range Γ') →
      Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) := fun i =>
    {x | (i.1 : DCone (EuclideanSpace ℝ (Fin 2))).carrier ⊆ (Γ x).carrier} ×ˢ
      {x | (i.2 : DCone (EuclideanSpace ℝ (Fin 2))).carrier ⊆ (Γ x).carrier} with hblk
  have hcover : (⋃ i, blk i) = Set.univ := by
    refine Set.eq_univ_of_forall fun p => ?_
    refine Set.mem_iUnion.mpr ⟨(⟨Γ' p.1, ⟨p.1, rfl⟩⟩, ⟨Γ' p.2, ⟨p.2, rfl⟩⟩), ?_⟩
    exact ⟨hsub p.1, hsub p.2⟩
  choose C hCtop hCle using fun i : ↥(Set.range Γ') × ↥(Set.range Γ') =>
    planar_block_le hϑ hϑ' hα hk hmeas hf hkm (i.1 : DCone (EuclideanSpace ℝ (Fin 2)))
      (i.2 : DCone (EuclideanSpace ℝ (Fin 2)))
      (by rw [hap _ i.1.2, hap _ i.2.2])
  refine ⟨∑' i, C i, ?_, ?_⟩
  · rw [tsum_fintype]
    exact (ENNReal.sum_lt_top.mpr fun i _ => (hCtop i).lt_top).ne
  · have hlhs : formHs Set.univ α f
        = ∫⁻ p in ⋃ i, blk i, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α)) := by
      rw [hcover, formHs, form, Set.univ_prod_univ]
      refine lintegral_congr fun p => ?_
      rw [jumpKernel]
      norm_num
    rw [hlhs]
    calc ∫⁻ p in ⋃ i, blk i, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α))
        ≤ ∑' i, ∫⁻ p in blk i, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
            ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α)) := lintegral_iUnion_le _ _
      _ ≤ ∑' i, C i * form Set.univ k f := ENNReal.tsum_le_tsum (fun i => hCle i)
      _ = (∑' i, C i) * form Set.univ k f := ENNReal.tsum_mul_right


/-! ## The ball-localised form, in dimension two

§3.2 consumes the inclusion on a ball, not on the whole plane. A Lipschitz
cutoff bridges the two: `χf` agrees with `f` on the inner ball and is supported
in the outer one, so the whole-space theorem applies to it, and
`form_cutoff_le` says the cost is the `H_k` form on the outer ball plus an `L²`
term. Both are finite for `f ∈ H_k(B*)`, which is exactly the hypothesis §3.2
has. -/

/-- **The inclusion §3.2 needs, in the plane.** If `f` has finite `L²` norm and
finite `H_k` form on the outer ball, then its `H^{α/2}` form on the inner ball is
finite: `f ∈ H_k(B*) ⟹ f ∈ H^{α/2}(B)`. -/
theorem formHs_ball_ne_top_of_planar {ϑ α Λ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    (hα : 0 < α) (hα2 : α < 2)
    {Γ : Configuration (EuclideanSpace ℝ (Fin 2))} (hΓ : IsBounded Γ ϑ) (hmeas : CondMeas Γ)
    {k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : Measurable f)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      k p.1 p.2)
    {x₀ : EuclideanSpace ℝ (Fin 2)} {R R' : ℝ} (hRR : R < R')
    (hL2 : ∫⁻ x in ball x₀ R', ENNReal.ofReal (f x ^ 2) ≠ ∞)
    (hHk : form (ball x₀ R') k f ≠ ∞) :
    formHs (ball x₀ R) α f ≠ ∞ := by
  have hδ : 0 < R' - R := by linarith
  have hcm : Measurable (cutoff x₀ R R') := by unfold cutoff; fun_prop
  set g : EuclideanSpace ℝ (Fin 2) → ℝ := fun x => cutoff x₀ R R' x * f x with hgdef
  have hgm : Measurable g := by rw [hgdef]; exact hcm.mul hf
  have hkmg : Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal ((g p.2 - g p.1) ^ 2) * k p.1 p.2 := by
    refine Measurable.mul (ENNReal.measurable_ofReal.comp ?_) hkm
    exact ((hgm.comp measurable_snd).sub (hgm.comp measurable_fst)).pow_const 2
  -- on the inner ball `g` agrees with `f`
  have hcongr : formHs (ball x₀ R) α f = formHs (ball x₀ R) α g := by
    refine setLIntegral_congr_fun (measurableSet_ball.prod measurableSet_ball) ?_
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have hu1 : cutoff x₀ R R' u = 1 := by
      refine cutoff_eq_one hRR ?_
      rw [Metric.mem_ball, dist_eq_norm] at hu
      linarith
    have hv1 : cutoff x₀ R R' v = 1 := by
      refine cutoff_eq_one hRR ?_
      rw [Metric.mem_ball, dist_eq_norm] at hv
      linarith
    simp only [hgdef, hu1, hv1, one_mul]
  -- the whole-space theorem, applied to `g`
  obtain ⟨C, hCtop, hC⟩ := sobolevInclusion_planar hϑ hϑ' hα.le hΓ hmeas hk hgm hkmg
  have hmono : formHs (ball x₀ R) α g ≤ formHs Set.univ α g := by
    refine lintegral_mono_set ?_
    exact Set.prod_mono (Set.subset_univ _) (Set.subset_univ _)
  have hCδ : (∫⁻ u : EuclideanSpace ℝ (Fin 2),
      ENNReal.ofReal (min (‖u‖ ^ 2 / (R' - R) ^ 2) 1 * ‖u‖ ^ (-(2 : ℝ) - α))) ≠ ∞ :=
    (lintegral_cutoff_kernel_lt_top two_pos hδ hα hα2).ne
  have hcost := form_cutoff_le (x₀ := x₀) hk two_pos hα hα2 hRR hf hkm
  have hbound : formHs (ball x₀ R) α f ≤ C * form Set.univ k g :=
    le_trans (le_of_eq hcongr) (le_trans hmono hC)
  refine ne_of_lt (lt_of_le_of_lt hbound ?_)
  refine ENNReal.mul_lt_top hCtop.lt_top (lt_of_le_of_lt hcost ?_)
  refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨?_, ?_⟩, ?_⟩
  · exact ENNReal.mul_lt_top (by norm_num) hHk.lt_top
  · exact ENNReal.mul_lt_top (by norm_num)
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCδ.lt_top) hL2.lt_top)
  · exact ENNReal.mul_lt_top (by norm_num)
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCδ.lt_top) hL2.lt_top)


/-! ## Theorem 1.1 on a ball, unconditionally, in the plane

Section 3.2 leaves one hypothesis undischarged: the `H^{α/2}` form of the
larger ball must be known to be finite before the dominated convergence step
can run (`QFS.formHs_ball_le_form_of_formHs_ne_top`).  In the plane
`formHs_ball_ne_top_of_planar` -- proved above, and *not* in the paper --
supplies exactly that for every `f ∈ H_k`, so the two combine into the paper's
statement with no hypothesis beyond `f ∈ L²` of the larger ball.

The mathematics closing the gap is new; the statement obtained is the paper's. -/

/-- **Theorem 1.1 on a ball, unconditionally, in dimension two.** For every
`ϑ`-bounded configuration satisfying Debreu's measurability condition and every
kernel satisfying (1.4) there are `κ, c ≥ 1` -- independent of the ball and of
`f` -- with

  `|f|²_{H^{α/2}(B_R)} ≤ c |f|²_{H_k(B_{κR})}`

for every measurable `f` that is locally integrable and square integrable on
`B_{κR}`. This is the shape of `QFS.TheoremOneOneBall`, with the paper's
scale-invariant enlargement of the ball. -/
theorem formHs_ball_le_form_planar {ϑ α Λ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ Real.pi / 2)
    (hα : 0 < α) (hα2 : α < 2) (hΛ : 1 ≤ Λ) :
    ∃ κ c : ℝ, 1 ≤ κ ∧ 1 ≤ c ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin 2)), IsBounded Γ ϑ → CondMeas Γ →
      ∀ k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ≥0∞,
        KernelBounds Γ α Λ k →
        (Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
          k p.1 p.2) →
      ∀ (x₀ : EuclideanSpace ℝ (Fin 2)) (R : ℝ), 0 < R →
      ∀ f : EuclideanSpace ℝ (Fin 2) → ℝ, Measurable f → LocallyIntegrable f volume →
        (∫⁻ x in ball x₀ (κ * R), ENNReal.ofReal (f x ^ 2)) ≠ ⊤ →
        formHs (ball x₀ R) α f ≤ ENNReal.ofReal c * form (ball x₀ (κ * R)) k f := by
  obtain ⟨κ, c, hκ, hc, hmain⟩ :=
    formHs_ball_le_form_of_formHs_ne_top (d := 2) hϑ hϑ' le_rfl hα hα2 hΛ
  have hs2 : (0:ℝ) ≤ Real.sqrt ((2:ℕ) : ℝ) := Real.sqrt_nonneg _
  refine ⟨2 * (κ + Real.sqrt ((2:ℕ) : ℝ)), c, by nlinarith, hc,
    fun Γ hΓ hmeas k hk hkm x₀ R hR f hfm hf hL2 => ?_⟩
  set ρ : ℝ := (κ + Real.sqrt ((2:ℕ) : ℝ)) * R with hρ
  have hρpos : 0 < ρ := by rw [hρ]; nlinarith
  have hsub : ball x₀ (κ * R) ⊆ ball x₀ (2 * (κ + Real.sqrt ((2:ℕ) : ℝ)) * R) := by
    refine ball_subset_ball ?_
    nlinarith
  -- if the right-hand side is infinite there is nothing to prove
  by_cases htop : form (ball x₀ (2 * (κ + Real.sqrt ((2:ℕ) : ℝ)) * R)) k f = ⊤
  · rw [htop, ENNReal.mul_top (by simpa using lt_of_lt_of_le zero_lt_one hc)]
    exact le_top
  have hfin : formHs (ball x₀ ρ) α f ≠ ⊤ := by
    refine formHs_ball_ne_top_of_planar hϑ hϑ' hα hα2 hΓ hmeas hk hfm hkm
      (show ρ < 2 * (κ + Real.sqrt ((2:ℕ) : ℝ)) * R by rw [hρ]; nlinarith) hL2 htop
  refine le_trans (hmain Γ hΓ hmeas k hk hkm x₀ R hR f hfm hf hfin) (mul_le_mul' le_rfl ?_)
  exact form_mono_set hsub k f


/-- **Theorem 1.1's ball form holds in the plane**, in the shape
`QFS.TheoremOneOneBallCondMeas` records: `κ` and `c` depend on `ϑ`, `Λ` and `α`
alone, the hypothesis on `f` is `f ∈ L²(B_{κR})`, and the only additions to the
paper's own hypotheses are Debreu's measurability condition and the
measurability of `k`, both of which this formalisation carries throughout.

The proof is the planar theorem above applied to a measurable representative of
`f`: `L²` of a ball gives a measurable, globally integrable `g` agreeing with
`f` almost everywhere there (`QFS.exists_measurable_repr`), and neither form
sees the change (`QFS.form_congr_ae`). -/
theorem theoremOneOneBallCondMeas_two : TheoremOneOneBallCondMeas 2 := by
  intro ϑ Λ α hϑ hϑ' hΛ hα hα2
  obtain ⟨κ, c, hκ, hc, hmain⟩ := formHs_ball_le_form_planar hϑ hϑ' hα hα2 hΛ
  refine ⟨κ, c, hκ, hc, fun Γ hΓ hmeas k hk hkm x₀ R hR f hf => ?_⟩
  obtain ⟨g, hgm, hgloc, hae, hL2⟩ := exists_measurable_repr hf
  have hsub : ball x₀ R ⊆ ball x₀ (κ * R) := ball_subset_ball (by nlinarith)
  have h1 : formHs (ball x₀ R) α f = formHs (ball x₀ R) α g :=
    formHs_congr_ae α (ae_restrict_of_ae_restrict_of_subset hsub hae)
  have h2 : form (ball x₀ (κ * R)) k f = form (ball x₀ (κ * R)) k g := form_congr_ae k hae
  rw [h1, h2]
  exact hmain Γ hΓ hmeas k hk hkm x₀ R hR g hgm hgloc hL2


/-- **Theorem 1.1 in the plane**, on the same ball rather than an enlarged one,
granted the Whitney/Dyda input the paper quotes rather than proves.

This is `QFS.formHs_le_form_of_theoremOneOneBall` -- the chain (6.14) of
Lemma 7.1 -- run on the planar ball comparability of this file instead of on the
paper's unproved `QFS.TheoremOneOneBall`. Its hypotheses are the paper's, plus
the two this formalisation carries throughout (Debreu's condition and the
measurability of `k`), plus the Whitney family and Dyda's inequality (13), which
the paper takes from [Dyda06] and a Whitney decomposition. -/
theorem formHs_le_form_planar {ϑ Λ α : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ Real.pi / 2)
    (hΛ : 1 ≤ Λ) (hα : 0 < α) (hα2 : α < 2)
    (hW : ∀ κ : ℝ, 1 ≤ κ → Nonempty (WhitneyBallData 2 α κ)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin 2)), IsBounded Γ ϑ → CondMeas Γ →
      ∀ k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ≥0∞,
        KernelBounds Γ α Λ k →
        (Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
          k p.1 p.2) →
      ∀ (x₀ : EuclideanSpace ℝ (Fin 2)) (R : ℝ), 0 < R →
      ∀ f : EuclideanSpace ℝ (Fin 2) → ℝ,
        MemLp f 2 (volume.restrict (ball x₀ R)) →
        (Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) →
        ENNReal.ofReal c * formHs (ball x₀ R) α f ≤ form (ball x₀ R) k f := by
  obtain ⟨κ, c₀, hκ, hc₀, H⟩ := theoremOneOneBallCondMeas_two ϑ Λ α hϑ hϑ' hΛ hα hα2
  obtain ⟨W⟩ := hW κ hκ
  have hc₀pos : (0 : ℝ) < c₀ := lt_of_lt_of_le zero_lt_one hc₀
  have hMR : (0 : ℝ) < (W.overlapBound : ℝ) := by exact_mod_cast W.overlapBound_pos
  refine ⟨c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ),
    div_pos (mul_pos (inv_pos.mpr hc₀pos) W.dydaConst_pos) hMR,
    fun Γ hΓ hmeas k hk hkm x₀ R hR f hf hFmeas => ?_⟩
  exact formHs_le_form_of_ballComparability hc₀ W
    (fun y₀ S hS hmem => H Γ hΓ hmeas k hk hkm y₀ S hS f hmem) x₀ R hR hf hFmeas


/-! ## Theorem 1.4 for `Ω = ℝ²`

The paper deduces the whole-space case from Theorem 1.1 by monotone convergence,
the constant being independent of the radius.  `QFS.theoremOneFourUniv_of_theoremOneOne`
is that deduction from the paper's `Prop`; here it is run on the planar theorem
instead. -/

/-- **`H_k(ℝ²) ⊆ H^{α/2}(ℝ²)` with a uniform constant**, granted the quoted
Whitney/Dyda input. Unlike `sobolevInclusion_planar`, whose constant is produced
after `f` is fixed, the constant here depends only on `ϑ`, `Λ` and `α`. -/
theorem formHs_univ_le_form_univ_planar {ϑ Λ α : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ Real.pi / 2) (hΛ : 1 ≤ Λ) (hα : 0 < α) (hα2 : α < 2)
    (hW : ∀ κ : ℝ, 1 ≤ κ → Nonempty (WhitneyBallData 2 α κ)) :
    ∃ c : ℝ, 1 ≤ c ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin 2)), IsBounded Γ ϑ → CondMeas Γ →
      ∀ k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ≥0∞,
        KernelBounds Γ α Λ k →
        (Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
          k p.1 p.2) →
      ∀ f : EuclideanSpace ℝ (Fin 2) → ℝ,
        (∀ (x₀ : EuclideanSpace ℝ (Fin 2)) (R : ℝ), 0 < R →
          MemLp f 2 (volume.restrict (ball x₀ R))) →
        (Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) →
        formHs Set.univ α f ≤ ENNReal.ofReal c * form Set.univ k f := by
  obtain ⟨c₀, hc₀pos, H⟩ := formHs_le_form_planar hϑ hϑ' hΛ hα hα2 hW
  refine ⟨max c₀⁻¹ 1, le_max_right _ _,
    fun Γ hΓ hmeas k hk hkm f hf hFmeas => ?_⟩
  simp only [formHs]
  rw [form_univ_eq_iSup, form_univ_eq_iSup, ENNReal.mul_iSup]
  refine iSup_mono fun n => ?_
  have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 := H Γ hΓ hmeas k hk hkm 0 ((n : ℝ) + 1) hR f (hf 0 _ hR) hFmeas
  have hstep : formHs (ball (0 : EuclideanSpace ℝ (Fin 2)) ((n : ℝ) + 1)) α f
      ≤ ENNReal.ofReal c₀⁻¹ * form (ball (0 : EuclideanSpace ℝ (Fin 2)) ((n : ℝ) + 1)) k f := by
    calc formHs (ball (0 : EuclideanSpace ℝ (Fin 2)) ((n : ℝ) + 1)) α f
        = ENNReal.ofReal c₀⁻¹ * (ENNReal.ofReal c₀ *
            formHs (ball (0 : EuclideanSpace ℝ (Fin 2)) ((n : ℝ) + 1)) α f) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hc₀pos)),
            inv_mul_cancel₀ (ne_of_gt hc₀pos), ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal c₀⁻¹ * form (ball (0 : EuclideanSpace ℝ (Fin 2)) ((n : ℝ) + 1)) k f :=
          mul_le_mul' le_rfl h1
  refine le_trans hstep (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl)

/-- **Theorem 1.4 for `Ω = ℝ²`**: the two spaces coincide, granted the quoted
Whitney/Dyda input. -/
theorem Hk_univ_eq_Hs_univ_planar {ϑ Λ α : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ Real.pi / 2)
    (hΛ : 1 ≤ Λ) (hα : 0 < α) (hα2 : α < 2)
    (hW : ∀ κ : ℝ, 1 ≤ κ → Nonempty (WhitneyBallData 2 α κ))
    {Γ : Configuration (EuclideanSpace ℝ (Fin 2))} (hΓ : IsBounded Γ ϑ) (hmeas : CondMeas Γ)
    {k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      k p.1 p.2) :
    Hk Set.univ k = Hs Set.univ α := by
  obtain ⟨c, hc, H⟩ := formHs_univ_le_form_univ_planar hϑ hϑ' hΛ hα hα2 hW
  refine Set.Subset.antisymm (fun f hf => ?_) (Hs_subset_Hk hk Set.univ)
  obtain ⟨hfL2, hfform⟩ := hf
  refine ⟨hfL2, ?_⟩
  -- pass to a measurable representative
  set g : EuclideanSpace ℝ (Fin 2) → ℝ := hfL2.1.mk f with hgdef
  have hgm : Measurable g := hfL2.1.stronglyMeasurable_mk.measurable
  have hae : ∀ᵐ x ∂(volume.restrict (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))), f x = g x :=
    hfL2.1.ae_eq_mk
  have hgL2 : ∀ (x₀ : EuclideanSpace ℝ (Fin 2)) (R : ℝ), 0 < R →
      MemLp g 2 (volume.restrict (ball x₀ R)) := by
    intro x₀ R _
    refine ((hfL2.ae_eq hae).mono_measure ?_)
    exact Measure.restrict_mono (Set.subset_univ _) le_rfl
  have hFmeas : Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal ((g p.2 - g p.1) ^ 2) * k p.1 p.2 :=
    (ENNReal.measurable_ofReal.comp
      (((hgm.comp measurable_snd).sub (hgm.comp measurable_fst)).pow_const 2)).mul hkm
  have hform : form Set.univ k g = form Set.univ k f := (form_congr_ae k hae).symm
  have hformHs : formHs Set.univ α g = formHs Set.univ α f := (formHs_congr_ae α hae).symm
  have hbound := H Γ hΓ hmeas k hk hkm g hgL2 hFmeas
  rw [hformHs, hform] at hbound
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfform) hbound


/-! ## Theorem 1.4 for a domain, in the plane

Lemma 7.1 for a domain (`QFS.formHs_le_form_domain`) turns the ball
comparability into the comparability on `Ω`, given the Whitney family of `Ω` and
Dyda's inequality — the two inputs the paper quotes.  With the planar ball
theorem it gives the inclusion `H_k(Ω) ⊆ H^{α/2}(Ω)` for every planar domain
that has such a family. -/

/-- **The comparability on a domain, in the plane**, granted the quoted Whitney
family and Dyda's inequality for that domain. -/
theorem formHs_le_form_domain_planar {ϑ Λ α : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ Real.pi / 2) (hΛ : 1 ≤ Λ) (hα : 0 < α) (hα2 : α < 2) :
    ∃ κ c₀ : ℝ, 1 ≤ κ ∧ 1 ≤ c₀ ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin 2)), IsBounded Γ ϑ → CondMeas Γ →
      ∀ k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ≥0∞,
        KernelBounds Γ α Λ k →
        (Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
          k p.1 p.2) →
      ∀ Ω : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet Ω →
      ∀ W : WhitneyDomainData 2 α κ Ω,
      ∀ f : EuclideanSpace ℝ (Fin 2) → ℝ,
        MemLp f 2 (volume.restrict Ω) →
        (Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) →
        ENNReal.ofReal (c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ)) * formHs Ω α f
          ≤ form Ω k f := by
  obtain ⟨κ, c₀, hκ, hc₀, H⟩ := theoremOneOneBallCondMeas_two ϑ Λ α hϑ hϑ' hΛ hα hα2
  refine ⟨κ, c₀, hκ, hc₀,
    fun Γ hΓ hmeas k hk hkm Ω hΩ W f hf hFmeas => ?_⟩
  exact formHs_le_form_domain hc₀ hΩ W
    (fun y₀ S hS hmem => H Γ hΓ hmeas k hk hkm y₀ S hS f hmem) hf hFmeas

/-- **Theorem 1.4 for a planar domain**: `H_k(Ω) = H^{α/2}(Ω)` for every
measurable `Ω ⊆ ℝ²` that has a Whitney family and satisfies Dyda's inequality —
the two inputs the paper quotes rather than proves. -/
theorem Hk_domain_eq_Hs_domain_planar {ϑ Λ α : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ Real.pi / 2) (hΛ : 1 ≤ Λ) (hα : 0 < α) (hα2 : α < 2) :
    ∃ κ : ℝ, 1 ≤ κ ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin 2)), IsBounded Γ ϑ → CondMeas Γ →
      ∀ k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ≥0∞,
        KernelBounds Γ α Λ k →
        (Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
          k p.1 p.2) →
      ∀ Ω : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet Ω →
      ∀ _W : WhitneyDomainData 2 α κ Ω, Hk Ω k = Hs Ω α := by
  obtain ⟨κ, c₀, hκ, hc₀, H⟩ := theoremOneOneBallCondMeas_two ϑ Λ α hϑ hϑ' hΛ hα hα2
  refine ⟨κ, hκ, fun Γ hΓ hmeas k hk hkm Ω hΩ W => ?_⟩
  have hc₀pos : (0:ℝ) < c₀ := lt_of_lt_of_le zero_lt_one hc₀
  have hMR : (0 : ℝ) < (W.overlapBound : ℝ) := by exact_mod_cast W.overlapBound_pos
  refine Set.Subset.antisymm (fun f hf => ?_) (Hs_subset_Hk hk Ω)
  obtain ⟨hfL2, hfform⟩ := hf
  refine ⟨hfL2, ?_⟩
  -- a measurable representative, supported in `Ω`
  set g : EuclideanSpace ℝ (Fin 2) → ℝ := Ω.indicator (hfL2.1.mk f) with hgdef
  have hgm : Measurable g := hfL2.1.stronglyMeasurable_mk.measurable.indicator hΩ
  have hae : ∀ᵐ x ∂(volume.restrict Ω), f x = g x := by
    have h1 : ∀ᵐ x ∂(volume.restrict Ω), f x = hfL2.1.mk f x := hfL2.1.ae_eq_mk
    have h2 : ∀ᵐ x ∂(volume.restrict Ω), hfL2.1.mk f x = g x :=
      (ae_restrict_iff' hΩ).mpr (Filter.Eventually.of_forall fun x hx => by
        rw [hgdef, Set.indicator_of_mem hx])
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx1, hx2]
  have hgglob : MemLp g 2 volume :=
    (memLp_indicator_iff_restrict hΩ).mpr (hfL2.ae_eq hfL2.1.ae_eq_mk)
  have hgL2 : MemLp g 2 (volume.restrict Ω) := hgglob.mono_measure Measure.restrict_le_self
  have hFmeas : Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal ((g p.2 - g p.1) ^ 2) * k p.1 p.2 :=
    (ENNReal.measurable_ofReal.comp
      (((hgm.comp measurable_snd).sub (hgm.comp measurable_fst)).pow_const 2)).mul hkm
  have hbound := formHs_le_form_domain hc₀ hΩ W
    (fun y₀ S hS hmem => H Γ hΓ hmeas k hk hkm y₀ S hS g hmem) hgL2 hFmeas
  have hform : form Ω k g = form Ω k f := (form_congr_ae k hae).symm
  have hformHs : formHs Ω α g = formHs Ω α f := (formHs_congr_ae α hae).symm
  rw [hformHs, hform] at hbound
  intro htop
  rw [htop] at hbound
  have hc : ENNReal.ofReal (c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ)) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have := W.dydaConst_pos
    positivity
  rw [ENNReal.mul_top hc] at hbound
  exact hfform (top_le_iff.mp hbound)


/-! ## Lemma 3.7's own statement, in the plane

Lemma 3.7 says the two spaces coincide on a ball.  That follows from the
same-ball comparability, which in the plane is `formHs_le_form_planar`. -/

/-- **Lemma 3.7 in the plane**: `H_k(B) = H^{α/2}(B)` for every ball, granted
the Whitney/Dyda input the paper quotes. -/
theorem Hk_ball_eq_Hs_ball_planar {ϑ Λ α : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ Real.pi / 2)
    (hΛ : 1 ≤ Λ) (hα : 0 < α) (hα2 : α < 2)
    (hW : ∀ κ : ℝ, 1 ≤ κ → Nonempty (WhitneyBallData 2 α κ))
    {Γ : Configuration (EuclideanSpace ℝ (Fin 2))} (hΓ : IsBounded Γ ϑ) (hmeas : CondMeas Γ)
    {k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      k p.1 p.2)
    (x₀ : EuclideanSpace ℝ (Fin 2)) {R : ℝ} (hR : 0 < R) :
    Hk (ball x₀ R) k = Hs (ball x₀ R) α := by
  obtain ⟨c, hcpos, H⟩ := formHs_le_form_planar hϑ hϑ' hΛ hα hα2 hW
  refine Set.Subset.antisymm (fun f hf => ?_) (Hs_subset_Hk hk _)
  obtain ⟨hfL2, hfform⟩ := hf
  refine ⟨hfL2, ?_⟩
  set g : EuclideanSpace ℝ (Fin 2) → ℝ := (ball x₀ R).indicator (hfL2.1.mk f) with hgdef
  have hgm : Measurable g :=
    hfL2.1.stronglyMeasurable_mk.measurable.indicator measurableSet_ball
  have hae : ∀ᵐ x ∂(volume.restrict (ball x₀ R)), f x = g x := by
    have h1 : ∀ᵐ x ∂(volume.restrict (ball x₀ R)), f x = hfL2.1.mk f x := hfL2.1.ae_eq_mk
    have h2 : ∀ᵐ x ∂(volume.restrict (ball x₀ R)), hfL2.1.mk f x = g x :=
      (ae_restrict_iff' measurableSet_ball).mpr (Filter.Eventually.of_forall fun x hx => by
        rw [hgdef, Set.indicator_of_mem hx])
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx1, hx2]
  have hgglob : MemLp g 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr (hfL2.ae_eq hfL2.1.ae_eq_mk)
  have hgL2 : MemLp g 2 (volume.restrict (ball x₀ R)) :=
    hgglob.mono_measure Measure.restrict_le_self
  have hFmeas : Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal ((g p.2 - g p.1) ^ 2) * k p.1 p.2 :=
    (ENNReal.measurable_ofReal.comp
      (((hgm.comp measurable_snd).sub (hgm.comp measurable_fst)).pow_const 2)).mul hkm
  have hbound := H Γ hΓ hmeas k hk hkm x₀ R hR g hgL2 hFmeas
  have hform : form (ball x₀ R) k g = form (ball x₀ R) k f := (form_congr_ae k hae).symm
  have hformHs : formHs (ball x₀ R) α g = formHs (ball x₀ R) α f :=
    (formHs_congr_ae α hae).symm
  rw [hformHs, hform] at hbound
  intro htop
  rw [htop, ENNReal.mul_top (by simpa using hcpos)] at hbound
  exact hfform (top_le_iff.mp hbound)

/-- **The hypotheses of the planar theorems are satisfiable.** The constant
configuration and the plain jump kernel satisfy every one of them, so none of
the statements above is vacuous. -/
theorem planar_hypotheses_nonvacuous {ϑ α : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ Real.pi / 2)
    {v : EuclideanSpace ℝ (Fin 2)} (hv : ‖v‖ = 1) :
    ∃ (Γ : Configuration (EuclideanSpace ℝ (Fin 2)))
      (k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ≥0∞),
      IsBounded Γ ϑ ∧ CondMeas Γ ∧ KernelBounds Γ α 2 k ∧
      (Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
        k p.1 p.2) :=
  ⟨constConfig ⟨v, hv, ϑ, hϑ, hϑ'⟩, jumpKernel 2 α, isBounded_constConfig hϑ hϑ' hv,
    condMeas_constConfig _, kernelBounds_jumpKernel _ α, measurable_jumpKernel 2 α⟩


/-! ## Theorem 1.1 itself, in the plane

Everything above assembles into the paper's own Theorem 1.1, in dimension two,
with the two hypotheses this formalisation carries and the one input Lemma 7.1
quotes. -/

/-- **Theorem 1.1 in the plane**, in the paper's own statement
(`QFS.TheoremOneOneCondMeas`): for every `ϑ`-bounded configuration satisfying
Debreu's condition and every measurable kernel satisfying (1.4) there is a
`c ≥ 1`, depending only on `ϑ`, `Λ` and `α`, with

  `|f|²_{H^{α/2}(B)} ≤ c |f|²_{H_k(B)}`

for every ball `B` and every `f ∈ L²(B)`.

Granted the Whitney family and Dyda's inequality (13), which the paper quotes
rather than proves and which are carried here as `QFS.WhitneyBallData`. -/
theorem theoremOneOneCondMeas_two
    (hW : ∀ (α κ : ℝ), 1 ≤ κ → Nonempty (WhitneyBallData 2 α κ)) :
    TheoremOneOneCondMeas 2 := by
  intro ϑ Λ α hϑ hΛ hα hα2
  by_cases hϑ' : ϑ ≤ Real.pi / 2
  swap
  · -- no configuration is `ϑ`-bounded for `ϑ > π/2`, so the statement is vacuous
    exact ⟨1, le_rfl, fun Γ hΓ _ k _ _ x₀ R _ f _ =>
      absurd (le_pi_div_two_of_isBounded hΓ) hϑ'⟩
  obtain ⟨c₀, hc₀pos, H⟩ :=
    formHs_le_form_planar (ϑ := ϑ) (Λ := Λ) (α := α) hϑ hϑ' hΛ hα hα2 (hW α)
  refine ⟨max c₀⁻¹ 1, le_max_right _ _, fun Γ hΓ hmeas k hk hkm x₀ R hR f hf => ?_⟩
  -- a measurable representative supported in the ball
  set g : EuclideanSpace ℝ (Fin 2) → ℝ := (ball x₀ R).indicator (hf.1.mk f) with hgdef
  have hgm : Measurable g := hf.1.stronglyMeasurable_mk.measurable.indicator measurableSet_ball
  have hae : ∀ᵐ x ∂(volume.restrict (ball x₀ R)), f x = g x := by
    have h1 : ∀ᵐ x ∂(volume.restrict (ball x₀ R)), f x = hf.1.mk f x := hf.1.ae_eq_mk
    have h2 : ∀ᵐ x ∂(volume.restrict (ball x₀ R)), hf.1.mk f x = g x :=
      (ae_restrict_iff' measurableSet_ball).mpr (Filter.Eventually.of_forall fun x hx => by
        rw [hgdef, Set.indicator_of_mem hx])
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx1, hx2]
  have hgL2 : MemLp g 2 (volume.restrict (ball x₀ R)) :=
    ((memLp_indicator_iff_restrict measurableSet_ball).mpr
      (hf.ae_eq hf.1.ae_eq_mk)).mono_measure Measure.restrict_le_self
  have hFmeas : Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal ((g p.2 - g p.1) ^ 2) * k p.1 p.2 :=
    (ENNReal.measurable_ofReal.comp
      (((hgm.comp measurable_snd).sub (hgm.comp measurable_fst)).pow_const 2)).mul hkm
  have hbound := H Γ hΓ hmeas k hk hkm x₀ R hR g hgL2 hFmeas
  have hform : form (ball x₀ R) k g = form (ball x₀ R) k f := (form_congr_ae k hae).symm
  have hformHs : formHs (ball x₀ R) α g = formHs (ball x₀ R) α f :=
    (formHs_congr_ae α hae).symm
  rw [hformHs, hform] at hbound
  -- invert the constant
  calc formHs (ball x₀ R) α f
      = ENNReal.ofReal c₀⁻¹ * (ENNReal.ofReal c₀ * formHs (ball x₀ R) α f) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hc₀pos)),
          inv_mul_cancel₀ (ne_of_gt hc₀pos), ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal c₀⁻¹ * form (ball x₀ R) k f := mul_le_mul' le_rfl hbound
    _ ≤ ENNReal.ofReal (max c₀⁻¹ 1) * form (ball x₀ R) k f :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl


/-! ## Wide cones: dimension three and above

The obstruction to the cross blocks is that two double cones with skew axes can
be disjoint (`no_common_neighbour_of_skew_axes`). That cannot happen when the
cones are **wide**: the angle between two axes, read as an angle between lines,
is at most `π/2`, so two double cones of apex angle more than `π/4` always
overlap in a cone of aperture `apex − π/4`. Their bisector is its axis.

Everything else is already in place: the chaining machinery
(`formHs_le_form_of_commonDirection_on`) asks only that the two ends admit a
*common* cone, not that the configuration be constant, so with the bisector in
hand every block — diagonal or cross — is controlled, in every dimension. -/

/-- An inner product at least `√2/2` between unit vectors means an angle at most
`π/4`. -/
lemma angle_le_pi_div_four_of_inner {v u : E} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1)
    (h : Real.sqrt 2 / 2 ≤ ⟪v, u⟫_ℝ) : InnerProductGeometry.angle v u ≤ π / 4 := by
  have hpi : (π / 4 : ℝ) = Real.arccos (Real.sqrt 2 / 2) := by
    rw [← Real.cos_pi_div_four, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]
  rw [InnerProductGeometry.angle, hv, hu, one_mul, div_one, hpi]
  exact Real.arccos_le_arccos h

private theorem exists_common_subcone_aux {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hc : 0 ≤ ⟪v, w⟫_ℝ) {θ : ℝ} (hθ : π / 4 < θ) (hθ' : θ ≤ π / 2) :
    ∃ u : E, ‖u‖ = 1 ∧ doubleCone u (θ - π / 4) ⊆ doubleCone v θ ∧
      doubleCone u (θ - π / 4) ⊆ doubleCone w θ := by
  have hvv : ⟪v, v⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hww : ⟪w, w⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hne : v + w ≠ 0 := by
    intro h
    have hwv : w = -v := by
      have := congrArg (fun z => z - v) h
      simpa using this
    rw [hwv, inner_neg_right, hvv] at hc
    linarith
  set N : ℝ := ‖v + w‖ with hN
  have hNpos : 0 < N := norm_pos_iff.mpr hne
  have hNsq : N ^ 2 = 2 + 2 * ⟪v, w⟫_ℝ := by
    rw [hN, @norm_add_sq_real, hv, hw]
    ring
  set u : E := N⁻¹ • (v + w) with hu
  have hunorm : ‖u‖ = 1 := by
    rw [hu, hN]
    exact norm_smul_inv_norm hne
  -- both inner products are `(1 + ⟪v,w⟫)/N`
  have hkey : ∀ x : E, ⟪x, v⟫_ℝ + ⟪x, w⟫_ℝ = 1 + ⟪v, w⟫_ℝ → Real.sqrt 2 / 2 ≤ ⟪x, u⟫_ℝ := by
    intro x hx
    have hxu : ⟪x, u⟫_ℝ = N⁻¹ * (1 + ⟪v, w⟫_ℝ) := by
      rw [hu, real_inner_smul_right, inner_add_right, hx]
    rw [hxu, ← div_eq_inv_mul, le_div_iff₀ hNpos]
    have hX0 : 0 ≤ Real.sqrt 2 / 2 * N := by positivity
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hXsq : (Real.sqrt 2 / 2 * N) ^ 2 = 1 + ⟪v, w⟫_ℝ := by
      rw [mul_pow, div_pow, hs2, hNsq]; ring
    have hX1 : 1 ≤ Real.sqrt 2 / 2 * N := by nlinarith [hXsq, hc, hX0]
    nlinarith [hXsq, hX1, hX0]
  have hvu : Real.sqrt 2 / 2 ≤ ⟪v, u⟫_ℝ := hkey v (by rw [hvv])
  have hwu : Real.sqrt 2 / 2 ≤ ⟪w, u⟫_ℝ := by
    refine hkey w ?_
    rw [hww, real_inner_comm]
    ring
  refine ⟨u, hunorm, ?_, ?_⟩
  · have hd : dangle v u ≤ π / 4 :=
      le_trans (min_le_left _ _) (angle_le_pi_div_four_of_inner hv hunorm hvu)
    have := doubleCone_subset_of_dangle_le hv hunorm (a := π / 4) (η := θ - π / 4)
      (by positivity) (by linarith) (by linarith [Real.pi_pos]) hd
    rwa [show π / 4 + (θ - π / 4) = θ from by ring] at this
  · have hd : dangle w u ≤ π / 4 :=
      le_trans (min_le_left _ _) (angle_le_pi_div_four_of_inner hw hunorm hwu)
    have := doubleCone_subset_of_dangle_le hw hunorm (a := π / 4) (η := θ - π / 4)
      (by positivity) (by linarith) (by linarith [Real.pi_pos]) hd
    rwa [show π / 4 + (θ - π / 4) = θ from by ring] at this

/-- **Any two double cones of apex angle more than `π/4` share a subcone**, of
aperture `apex − π/4`, whatever their axes. -/
theorem exists_common_subcone {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) {θ : ℝ}
    (hθ : π / 4 < θ) (hθ' : θ ≤ π / 2) :
    ∃ u : E, ‖u‖ = 1 ∧ doubleCone u (θ - π / 4) ⊆ doubleCone v θ ∧
      doubleCone u (θ - π / 4) ⊆ doubleCone w θ := by
  by_cases h : (0 : ℝ) ≤ ⟪v, w⟫_ℝ
  · exact exists_common_subcone_aux hv hw h hθ hθ'
  · have hlt : ⟪v, w⟫_ℝ < 0 := not_le.mp h
    have hnw : ‖(-w : E)‖ = 1 := by simpa using hw
    obtain ⟨u, hu, h1, h2⟩ := exists_common_subcone_aux hv hnw
      (by rw [inner_neg_right]; linarith) hθ hθ'
    exact ⟨u, hu, h1, by rwa [doubleCone_neg] at h2⟩


/-- **Every block is controlled when the cones are wide.** For two reference
cones of apex `θ > π/4` — with *any* axes, parallel or not — the `H^{α/2}` energy
of the block they cut out is bounded by the `H_k` form. The bisector supplies a
common direction, so the same-direction theorem applies, on the union of the two
pieces. -/
theorem wide_block_le {d : ℕ} (hd : 0 < d) {α Λ θ : ℝ} (hθ1 : π / 4 < θ) (hθ2 : θ ≤ π / 2)
    (hα : 0 ≤ α)
    {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (hmeas : CondMeas Γ)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2)
    {v w : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∫⁻ p in {x | doubleCone v θ ⊆ (Γ x).carrier} ×ˢ
          {x | doubleCone w θ ⊆ (Γ x).carrier},
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2
        ≤ C * form Set.univ k f := by
  obtain ⟨u, hu, h1, h2⟩ := exists_common_subcone hv hw hθ1 hθ2
  set η : ℝ := θ - π / 4 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hη2 : η ≤ π / 2 := by rw [hη]; linarith [Real.pi_pos]
  set U : Set (EuclideanSpace ℝ (Fin d)) :=
    {x | doubleCone v θ ⊆ (Γ x).carrier} ∪ {x | doubleCone w θ ⊆ (Γ x).carrier} with hU
  have hUm : MeasurableSet U := (hmeas _).union (hmeas _)
  have hcommon : ∀ x ∈ U, cone u η ⊆ (Γ x).carrier := by
    intro x hx
    rcases hx with hx | hx
    · exact le_trans (le_trans Set.subset_union_left h1) hx
    · exact le_trans (le_trans Set.subset_union_left h2) hx
  have hmain := formHs_le_form_of_commonDirection_on hu hη0 hη2 hα hd hk hUm hcommon hf hkm
  set K : ℝ≥0∞ := ENNReal.ofReal (2 * Λ) *
    (ENNReal.ofReal (chainConst d η α) + ENNReal.ofReal (chainConst' d η α)) *
    unitBallVol d with hK
  have hKtop : K ≠ ∞ := by
    rw [hK]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩))
      unitBallVol_ne_top
  refine ⟨(unitBallVol d)⁻¹ * K, ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr (unitBallVol_ne_zero d)) hKtop, ?_⟩
  have hsub : {x | doubleCone v θ ⊆ (Γ x).carrier} ×ˢ
      {x | doubleCone w θ ⊆ (Γ x).carrier} ⊆ U ×ˢ U :=
    Set.prod_mono Set.subset_union_left Set.subset_union_right
  calc ∫⁻ p in {x | doubleCone v θ ⊆ (Γ x).carrier} ×ˢ
        {x | doubleCone w θ ⊆ (Γ x).carrier},
        ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2
      ≤ ∫⁻ p in U ×ˢ U, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2 :=
        lintegral_mono_set hsub
    _ = (unitBallVol d)⁻¹ * (unitBallVol d *
          ∫⁻ p in U ×ˢ U, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (unitBallVol_ne_zero d) unitBallVol_ne_top,
          one_mul]
    _ ≤ (unitBallVol d)⁻¹ * (K * form Set.univ k f) := mul_le_mul' le_rfl hmain
    _ = (unitBallVol d)⁻¹ * K * form Set.univ k f := by rw [hK]; ring


/-- **`H_k ⊆ H^{α/2}` in every dimension, for wide cones.** If the apex angles
of `Γ` are bounded below by some `ϑ > π/4`, then

  `|f|²_{H^{α/2}(ℝ^d)} ≤ C·|f|²_{H_k(ℝ^d)}`

for a finite `C`. No planarity, and no common direction: `exists_common_subcone`
supplies one for every pair of reference cones, because cones this wide always
overlap. -/
theorem sobolevInclusion_wide {d : ℕ} (hd : 0 < d) {ϑ α Λ : ℝ} (hϑ : π / 4 < ϑ)
    (hϑ' : ϑ ≤ π / 2) (hα : 0 ≤ α)
    {Γ : Configuration (EuclideanSpace ℝ (Fin d))} (hΓ : IsBounded Γ ϑ) (hmeas : CondMeas Γ)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ formHs Set.univ α f ≤ C * form Set.univ k f := by
  classical
  set θ : ℝ := (π / 4 + ϑ) / 2 with hθdef
  have hθ1 : π / 4 < θ := by rw [hθdef]; linarith
  have hθ2 : θ ≤ π / 2 := by rw [hθdef]; linarith
  have hθ3 : θ < ϑ := by rw [hθdef]; linarith
  have hθ0 : 0 < θ := by linarith [Real.pi_pos]
  obtain ⟨S, hS, hcov⟩ :=
    ref_cones' (E := EuclideanSpace ℝ (Fin d)) (ϑ := ϑ) (θ := θ) hϑ' hθ0 hθ3
  set blk : ↥S × ↥S → Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) := fun i =>
    {x | doubleCone (i.1 : EuclideanSpace ℝ (Fin d)) θ ⊆ (Γ x).carrier} ×ˢ
      {x | doubleCone (i.2 : EuclideanSpace ℝ (Fin d)) θ ⊆ (Γ x).carrier} with hblk
  have hcover : (⋃ i, blk i) = Set.univ := by
    refine Set.eq_univ_of_forall fun p => ?_
    obtain ⟨v, hvS, hv⟩ := hcov Γ hΓ p.1
    obtain ⟨w, hwS, hw⟩ := hcov Γ hΓ p.2
    exact Set.mem_iUnion.mpr ⟨(⟨v, hvS⟩, ⟨w, hwS⟩), hv, hw⟩
  choose C hCtop hCle using fun i : ↥S × ↥S =>
    wide_block_le hd hθ1 hθ2 hα hk hmeas hf hkm (hS _ i.1.2) (hS _ i.2.2)
  refine ⟨∑' i, C i, ?_, ?_⟩
  · rw [tsum_fintype]
    exact (ENNReal.sum_lt_top.mpr fun i _ => (hCtop i).lt_top).ne
  · have hlhs : formHs Set.univ α f
        = ∫⁻ p in ⋃ i, blk i,
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2 := by
      rw [hcover, formHs, form, Set.univ_prod_univ]
    rw [hlhs]
    calc ∫⁻ p in ⋃ i, blk i,
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2
        ≤ ∑' i, ∫⁻ p in blk i,
            ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2 :=
          lintegral_iUnion_le _ _
      _ ≤ ∑' i, C i * form Set.univ k f := ENNReal.tsum_le_tsum hCle
      _ = (∑' i, C i) * form Set.univ k f := ENNReal.tsum_mul_right

/-- **The inclusion §3.2 needs, for wide cones, in every dimension.** If `f` has
finite `L²` norm and finite `H_k` form on the outer ball, then its `H^{α/2}` form
on the inner ball is finite. -/
theorem formHs_ball_ne_top_of_wide {d : ℕ} (hd : 0 < d) {ϑ α Λ : ℝ} (hϑ : π / 4 < ϑ)
    (hϑ' : ϑ ≤ π / 2) (hα : 0 < α) (hα2 : α < 2)
    {Γ : Configuration (EuclideanSpace ℝ (Fin d))} (hΓ : IsBounded Γ ϑ) (hmeas : CondMeas Γ)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      k p.1 p.2)
    {x₀ : EuclideanSpace ℝ (Fin d)} {R R' : ℝ} (hRR : R < R')
    (hL2 : ∫⁻ x in ball x₀ R', ENNReal.ofReal (f x ^ 2) ≠ ∞)
    (hHk : form (ball x₀ R') k f ≠ ∞) :
    formHs (ball x₀ R) α f ≠ ∞ := by
  have hδ : 0 < R' - R := by linarith
  have hcm : Measurable (cutoff x₀ R R') := by unfold cutoff; fun_prop
  set g : EuclideanSpace ℝ (Fin d) → ℝ := fun x => cutoff x₀ R R' x * f x with hgdef
  have hgm : Measurable g := by rw [hgdef]; exact hcm.mul hf
  have hkmg : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((g p.2 - g p.1) ^ 2) * k p.1 p.2 := by
    refine Measurable.mul (ENNReal.measurable_ofReal.comp ?_) hkm
    exact ((hgm.comp measurable_snd).sub (hgm.comp measurable_fst)).pow_const 2
  -- on the inner ball `g` agrees with `f`
  have hcongr : formHs (ball x₀ R) α f = formHs (ball x₀ R) α g := by
    refine setLIntegral_congr_fun (measurableSet_ball.prod measurableSet_ball) ?_
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have hu1 : cutoff x₀ R R' u = 1 := by
      refine cutoff_eq_one hRR ?_
      rw [Metric.mem_ball, dist_eq_norm] at hu
      linarith
    have hv1 : cutoff x₀ R R' v = 1 := by
      refine cutoff_eq_one hRR ?_
      rw [Metric.mem_ball, dist_eq_norm] at hv
      linarith
    simp only [hgdef, hu1, hv1, one_mul]
  -- the whole-space theorem, applied to `g`
  obtain ⟨C, hCtop, hC⟩ := sobolevInclusion_wide hd hϑ hϑ' hα.le hΓ hmeas hk hgm hkmg
  have hmono : formHs (ball x₀ R) α g ≤ formHs Set.univ α g := by
    refine lintegral_mono_set ?_
    exact Set.prod_mono (Set.subset_univ _) (Set.subset_univ _)
  have hCδ : (∫⁻ u : EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal (min (‖u‖ ^ 2 / (R' - R) ^ 2) 1 * ‖u‖ ^ (-(d : ℝ) - α))) ≠ ∞ :=
    (lintegral_cutoff_kernel_lt_top hd hδ hα hα2).ne
  have hcost := form_cutoff_le (x₀ := x₀) hk hd hα hα2 hRR hf hkm
  have hbound : formHs (ball x₀ R) α f ≤ C * form Set.univ k g :=
    le_trans (le_of_eq hcongr) (le_trans hmono hC)
  refine ne_of_lt (lt_of_le_of_lt hbound ?_)
  refine ENNReal.mul_lt_top hCtop.lt_top (lt_of_le_of_lt hcost ?_)
  refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨?_, ?_⟩, ?_⟩
  · exact ENNReal.mul_lt_top (by norm_num) hHk.lt_top
  · exact ENNReal.mul_lt_top (by norm_num)
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCδ.lt_top) hL2.lt_top)
  · exact ENNReal.mul_lt_top (by norm_num)
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCδ.lt_top) hL2.lt_top)


/-! ## Theorem 1.1 for wide cones, in every dimension

The same assembly as in the plane, with `formHs_ball_ne_top_of_wide` in place of
`formHs_ball_ne_top_of_planar`. -/

/-- **Theorem 1.1's enlarged-ball form for wide cones**, in every dimension
`d ≥ 2`: `κ` and `c` depend only on `ϑ`, `Λ`, `α` and `d`. -/
theorem formHs_ball_le_form_wide {d : ℕ} (hd : 2 ≤ d) {ϑ α Λ : ℝ} (hϑ : π / 4 < ϑ)
    (hϑ' : ϑ ≤ π / 2) (hα : 0 < α) (hα2 : α < 2) (hΛ : 1 ≤ Λ) :
    ∃ κ c : ℝ, 1 ≤ κ ∧ 1 ≤ c ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ → CondMeas Γ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
        KernelBounds Γ α Λ k →
        (Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
          k p.1 p.2) →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, Measurable f → LocallyIntegrable f volume →
        (∫⁻ x in ball x₀ (κ * R), ENNReal.ofReal (f x ^ 2)) ≠ ⊤ →
        formHs (ball x₀ R) α f ≤ ENNReal.ofReal c * form (ball x₀ (κ * R)) k f := by
  have hd0 : 0 < d := by omega
  obtain ⟨κ, c, hκ, hc, hmain⟩ :=
    formHs_ball_le_form_of_formHs_ne_top (d := d) (by linarith [Real.pi_pos] : 0 < ϑ)
      hϑ' hd hα hα2 hΛ
  have hs : (0:ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  refine ⟨2 * (κ + Real.sqrt (d : ℝ)), c, by nlinarith, hc,
    fun Γ hΓ hmeas k hk hkm x₀ R hR f hfm hf hL2 => ?_⟩
  set ρ : ℝ := (κ + Real.sqrt (d : ℝ)) * R with hρ
  have hρpos : 0 < ρ := by rw [hρ]; nlinarith
  have hsub : ball x₀ (κ * R) ⊆ ball x₀ (2 * (κ + Real.sqrt (d : ℝ)) * R) := by
    refine ball_subset_ball ?_
    nlinarith
  by_cases htop : form (ball x₀ (2 * (κ + Real.sqrt (d : ℝ)) * R)) k f = ⊤
  · rw [htop, ENNReal.mul_top (by simpa using lt_of_lt_of_le zero_lt_one hc)]
    exact le_top
  have hfin : formHs (ball x₀ ρ) α f ≠ ⊤ := by
    refine formHs_ball_ne_top_of_wide hd0 hϑ hϑ' hα hα2 hΓ hmeas hk hfm hkm
      (show ρ < 2 * (κ + Real.sqrt (d : ℝ)) * R by rw [hρ]; nlinarith) hL2 htop
  refine le_trans (hmain Γ hΓ hmeas k hk hkm x₀ R hR f hfm hf hfin) (mul_le_mul' le_rfl ?_)
  exact form_mono_set hsub k f


/-- **The ball comparability for wide cones, with the paper's `f ∈ L²(B)`.**
The wide-cone analogue of `QFS.theoremOneOneBallCondMeas_two`. -/
theorem ballComparability_wide {d : ℕ} (hd : 2 ≤ d) {ϑ α Λ : ℝ} (hϑ : π / 4 < ϑ)
    (hϑ' : ϑ ≤ π / 2) (hα : 0 < α) (hα2 : α < 2) (hΛ : 1 ≤ Λ) :
    ∃ κ c : ℝ, 1 ≤ κ ∧ 1 ≤ c ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ → CondMeas Γ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
        KernelBounds Γ α Λ k →
        (Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
          k p.1 p.2) →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        MemLp f 2 (volume.restrict (ball x₀ (κ * R))) →
        formHs (ball x₀ R) α f ≤ ENNReal.ofReal c * form (ball x₀ (κ * R)) k f := by
  obtain ⟨κ, c, hκ, hc, hmain⟩ := formHs_ball_le_form_wide hd hϑ hϑ' hα hα2 hΛ
  exact ⟨κ, c, hκ, hc, fun Γ hΓ hmeas k hk hkm x₀ R hR =>
    ballComparability_of_measurable hκ hR
      (fun f hfm hfl hL2 => hmain Γ hΓ hmeas k hk hkm x₀ R hR f hfm hfl hL2)⟩

/-- **Theorem 1.1 for wide cones**, on the same ball, in every dimension `d ≥ 2`,
granted the Whitney/Dyda input Lemma 7.1 quotes. -/
theorem formHs_le_form_wide {d : ℕ} (hd : 2 ≤ d) {ϑ Λ α : ℝ} (hϑ : π / 4 < ϑ)
    (hϑ' : ϑ ≤ π / 2) (hΛ : 1 ≤ Λ) (hα : 0 < α) (hα2 : α < 2)
    (hW : ∀ κ : ℝ, 1 ≤ κ → Nonempty (WhitneyBallData d α κ)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ → CondMeas Γ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
        KernelBounds Γ α Λ k →
        (Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
          k p.1 p.2) →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        MemLp f 2 (volume.restrict (ball x₀ R)) →
        (Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) →
        ENNReal.ofReal c * formHs (ball x₀ R) α f ≤ form (ball x₀ R) k f := by
  obtain ⟨κ, c₀, hκ, hc₀, H⟩ := ballComparability_wide hd hϑ hϑ' hα hα2 hΛ
  obtain ⟨W⟩ := hW κ hκ
  have hc₀pos : (0 : ℝ) < c₀ := lt_of_lt_of_le zero_lt_one hc₀
  have hMR : (0 : ℝ) < (W.overlapBound : ℝ) := by exact_mod_cast W.overlapBound_pos
  refine ⟨c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ),
    div_pos (mul_pos (inv_pos.mpr hc₀pos) W.dydaConst_pos) hMR,
    fun Γ hΓ hmeas k hk hkm x₀ R hR f hf hFmeas => ?_⟩
  exact formHs_le_form_of_ballComparability hc₀ W
    (fun y₀ S hS hmem => H Γ hΓ hmeas k hk hkm y₀ S hS f hmem) x₀ R hR hf hFmeas


/-! ## Theorem 1.4 for wide cones -/

/-- **`H_k(ℝ^d) ⊆ H^{α/2}(ℝ^d)` for wide cones, with a uniform constant**,
granted the quoted Whitney/Dyda input. -/
theorem formHs_univ_le_form_univ_wide {d : ℕ} (hd : 2 ≤ d) {ϑ Λ α : ℝ}
    (hϑ : Real.pi / 4 < ϑ)
    (hϑ' : ϑ ≤ Real.pi / 2) (hΛ : 1 ≤ Λ) (hα : 0 < α) (hα2 : α < 2)
    (hW : ∀ κ : ℝ, 1 ≤ κ → Nonempty (WhitneyBallData d α κ)) :
    ∃ c : ℝ, 1 ≤ c ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ → CondMeas Γ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
        KernelBounds Γ α Λ k →
        (Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
          k p.1 p.2) →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
          MemLp f 2 (volume.restrict (ball x₀ R))) →
        (Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) →
        formHs Set.univ α f ≤ ENNReal.ofReal c * form Set.univ k f := by
  obtain ⟨c₀, hc₀pos, H⟩ := formHs_le_form_wide hd hϑ hϑ' hΛ hα hα2 hW
  refine ⟨max c₀⁻¹ 1, le_max_right _ _,
    fun Γ hΓ hmeas k hk hkm f hf hFmeas => ?_⟩
  simp only [formHs]
  rw [form_univ_eq_iSup, form_univ_eq_iSup, ENNReal.mul_iSup]
  refine iSup_mono fun n => ?_
  have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 := H Γ hΓ hmeas k hk hkm 0 ((n : ℝ) + 1) hR f (hf 0 _ hR) hFmeas
  have hstep : formHs (ball (0 : EuclideanSpace ℝ (Fin d)) ((n : ℝ) + 1)) α f
      ≤ ENNReal.ofReal c₀⁻¹ * form (ball (0 : EuclideanSpace ℝ (Fin d)) ((n : ℝ) + 1)) k f := by
    calc formHs (ball (0 : EuclideanSpace ℝ (Fin d)) ((n : ℝ) + 1)) α f
        = ENNReal.ofReal c₀⁻¹ * (ENNReal.ofReal c₀ *
            formHs (ball (0 : EuclideanSpace ℝ (Fin d)) ((n : ℝ) + 1)) α f) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hc₀pos)),
            inv_mul_cancel₀ (ne_of_gt hc₀pos), ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal c₀⁻¹ * form (ball (0 : EuclideanSpace ℝ (Fin d)) ((n : ℝ) + 1)) k f :=
          mul_le_mul' le_rfl h1
  refine le_trans hstep (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl)

/-- **Theorem 1.4 for `Ω = ℝ^d`, for wide cones**: the two spaces coincide,
granted the quoted Whitney/Dyda input. -/
theorem Hk_univ_eq_Hs_univ_wide {d : ℕ} (hd : 2 ≤ d) {ϑ Λ α : ℝ}
    (hϑ : Real.pi / 4 < ϑ) (hϑ' : ϑ ≤ Real.pi / 2)
    (hΛ : 1 ≤ Λ) (hα : 0 < α) (hα2 : α < 2)
    (hW : ∀ κ : ℝ, 1 ≤ κ → Nonempty (WhitneyBallData d α κ))
    {Γ : Configuration (EuclideanSpace ℝ (Fin d))} (hΓ : IsBounded Γ ϑ) (hmeas : CondMeas Γ)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      k p.1 p.2) :
    Hk Set.univ k = Hs Set.univ α := by
  obtain ⟨c, hc, H⟩ := formHs_univ_le_form_univ_wide hd hϑ hϑ' hΛ hα hα2 hW
  refine Set.Subset.antisymm (fun f hf => ?_) (Hs_subset_Hk hk Set.univ)
  obtain ⟨hfL2, hfform⟩ := hf
  refine ⟨hfL2, ?_⟩
  -- pass to a measurable representative
  set g : EuclideanSpace ℝ (Fin d) → ℝ := hfL2.1.mk f with hgdef
  have hgm : Measurable g := hfL2.1.stronglyMeasurable_mk.measurable
  have hae : ∀ᵐ x ∂(volume.restrict (Set.univ : Set (EuclideanSpace ℝ (Fin d)))), f x = g x :=
    hfL2.1.ae_eq_mk
  have hgL2 : ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
      MemLp g 2 (volume.restrict (ball x₀ R)) := by
    intro x₀ R _
    refine ((hfL2.ae_eq hae).mono_measure ?_)
    exact Measure.restrict_mono (Set.subset_univ _) le_rfl
  have hFmeas : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((g p.2 - g p.1) ^ 2) * k p.1 p.2 :=
    (ENNReal.measurable_ofReal.comp
      (((hgm.comp measurable_snd).sub (hgm.comp measurable_fst)).pow_const 2)).mul hkm
  have hform : form Set.univ k g = form Set.univ k f := (form_congr_ae k hae).symm
  have hformHs : formHs Set.univ α g = formHs Set.univ α f := (formHs_congr_ae α hae).symm
  have hbound := H Γ hΓ hmeas k hk hkm g hgL2 hFmeas
  rw [hformHs, hform] at hbound
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfform) hbound


/-! ## Dimension one is trivial

On the line a double cone of positive apex angle is everything but the origin,
so *every* pair of distinct points is a cone pair and the lower bound of (1.4)
gives the inclusion directly, with the constant `Λ/2`. This is what makes the
open case precisely "narrow cones in dimension at least three". -/

/-- On the line every double cone of positive apex angle is `ℝ \ {0}`. -/
theorem doubleCone_dim_one {v : EuclideanSpace ℝ (Fin 1)} (hv : ‖v‖ = 1) {ϑ : ℝ}
    (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) : doubleCone v ϑ = {(0 : EuclideanSpace ℝ (Fin 1))}ᶜ := by
  ext h
  constructor
  · rintro (hh | hh)
    · exact hh.1
    · rw [Set.mem_neg] at hh
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h0
      exact hh.1 (by rw [h0]; simp)
  · intro hh
    have hne : h ≠ 0 := hh
    have hnorm : 0 < ‖h‖ := norm_pos_iff.mpr hne
    -- in dimension one `|⟪v, h⟫| = ‖v‖ ‖h‖`
    have habs : |⟪v, h⟫_ℝ| = ‖h‖ := by
      have := abs_real_inner_le_norm v h
      rw [hv, one_mul] at this
      refine le_antisymm this ?_
      -- the space is one-dimensional, so `v` and `h` are parallel
      obtain ⟨c, hc⟩ : ∃ c : ℝ, h = c • v := by
        have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1 := by
          simp [finrank_euclideanSpace]
        have hvne : v ≠ 0 := by intro h0; rw [h0] at hv; simp at hv
        have hspan : Submodule.span ℝ {v} = ⊤ := by
          refine Submodule.eq_top_of_finrank_eq ?_
          rw [finrank_span_singleton hvne, hfin]
        have : h ∈ Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin 1))) := by
          rw [hspan]; trivial
        rcases Submodule.mem_span_singleton.mp this with ⟨c, hc⟩
        exact ⟨c, hc.symm⟩
      rw [hc, real_inner_smul_right, abs_mul, norm_smul, real_inner_self_eq_norm_sq, hv]
      simp [abs_of_nonneg]
    have hcos : Real.cos ϑ < 1 := by
      have h0 : Real.cos ϑ < Real.cos 0 :=
        Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [Real.pi_pos]) hϑ
      simpa using h0
    rcases abs_cases (⟪v, h⟫_ℝ) with ⟨he, -⟩ | ⟨he, -⟩
    · left
      refine ⟨hne, ?_⟩
      rw [lt_div_iff₀ hnorm]
      nlinarith [habs, he]
    · right
      rw [Set.mem_neg]
      refine ⟨by simpa using hne, ?_⟩
      rw [inner_neg_right, norm_neg, lt_div_iff₀ hnorm]
      nlinarith [habs, he]


/-- On the line every pair of distinct points is a cone pair, so the lower bound
of (1.4) alone gives `jumpKernel ≤ (Λ/2) k`. -/
theorem jumpKernel_le_of_dim_one {α Λ : ℝ} (hα : 0 ≤ α)
    {Γ : Configuration (EuclideanSpace ℝ (Fin 1))}
    {k : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (x y : EuclideanSpace ℝ (Fin 1)) :
    jumpKernel 1 α x y ≤ ENNReal.ofReal (Λ / 2) * k x y := by
  have hΛ0 : (0:ℝ) < Λ := lt_of_lt_of_le zero_lt_one hk.one_le
  by_cases hxy : x = y
  · have : jumpKernel 1 α x y = 0 := by
      rw [jumpKernel, hxy, sub_self, norm_zero, Real.zero_rpow (by
        have : (0:ℝ) ≤ (1:ℕ) := by norm_num
        push_cast
        linarith), ENNReal.ofReal_zero]
    rw [this]
    exact bot_le
  -- both indicators are `1`
  have hcarrier : ∀ z : EuclideanSpace ℝ (Fin 1),
      (Γ z).carrier = {(0 : EuclideanSpace ℝ (Fin 1))}ᶜ := fun z => by
    rw [DCone.carrier]
    exact doubleCone_dim_one (Γ z).norm_axis (Γ z).apex_pos (Γ z).apex_le
  have hind1 : indE (coneAt Γ x) y = 1 := by
    rw [indE, Set.indicator_of_mem]
    rw [mem_coneAt, hcarrier]
    simpa using sub_ne_zero_of_ne (Ne.symm hxy)
  have hind2 : indE (coneAt Γ y) x = 1 := by
    rw [indE, Set.indicator_of_mem]
    rw [mem_coneAt, hcarrier]
    simpa using sub_ne_zero_of_ne hxy
  have hlow := hk.lower x y
  rw [hind1, hind2] at hlow
  have hprod : ENNReal.ofReal (Λ / 2) * (ENNReal.ofReal Λ⁻¹ * (1 + 1)) = 1 := by
    rw [show (1 : ℝ≥0∞) + 1 = 2 from by norm_num, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity),
      show Λ / 2 * Λ⁻¹ = 2⁻¹ from by field_simp]
    rw [show ENNReal.ofReal (2⁻¹ : ℝ) = (2 : ℝ≥0∞)⁻¹ from by
      rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2)]
      norm_num]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  calc jumpKernel 1 α x y
      = ENNReal.ofReal (Λ / 2) * (ENNReal.ofReal Λ⁻¹ * ((1 + 1) * jumpKernel 1 α x y)) := by
        rw [show ENNReal.ofReal (Λ / 2) *
            (ENNReal.ofReal Λ⁻¹ * ((1 + 1) * jumpKernel 1 α x y))
          = (ENNReal.ofReal (Λ / 2) * (ENNReal.ofReal Λ⁻¹ * (1 + 1))) * jumpKernel 1 α x y from
          by ring, hprod, one_mul]
    _ ≤ ENNReal.ofReal (Λ / 2) * k x y := mul_le_mul' le_rfl hlow

/-- **The inclusion is trivial on the line**: `|f|²_{H^{α/2}(Ω)} ≤ (Λ/2)·|f|²_{H_k(Ω)}`
for every `Ω`, with no chaining at all. -/
theorem formHs_le_form_dim_one {α Λ : ℝ} (hα : 0 ≤ α)
    {Γ : Configuration (EuclideanSpace ℝ (Fin 1))}
    {k : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (Ω : Set (EuclideanSpace ℝ (Fin 1)))
    (f : EuclideanSpace ℝ (Fin 1) → ℝ) :
    formHs Ω α f ≤ ENNReal.ofReal (Λ / 2) * form Ω k f := by
  rw [formHs, form, form]
  calc ∫⁻ p in Ω ×ˢ Ω, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel 1 α p.1 p.2
      ≤ ∫⁻ p in Ω ×ˢ Ω, ENNReal.ofReal (Λ / 2) *
          (ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) := by
        refine lintegral_mono fun p => ?_
        rw [show ENNReal.ofReal (Λ / 2) * (ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2)
          = ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * (ENNReal.ofReal (Λ / 2) * k p.1 p.2) from
          by ring]
        exact mul_le_mul' le_rfl (jumpKernel_le_of_dim_one hα hk p.1 p.2)
    _ = ENNReal.ofReal (Λ / 2) *
        ∫⁻ p in Ω ×ˢ Ω, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2 :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top


/-- **The wide-cone hypotheses are satisfiable.** The constant configuration with
apex angle `π/2` is `ϑ`-bounded for every `ϑ ≤ π/2`, in particular for a
`ϑ > π/4`, and the plain jump kernel satisfies (1.4) with `Λ = 2`. -/
theorem wide_hypotheses_nonvacuous {d : ℕ} {α : ℝ}
    {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) :
    ∃ (ϑ : ℝ) (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
      (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞),
      π / 4 < ϑ ∧ ϑ ≤ π / 2 ∧ IsBounded Γ ϑ ∧ CondMeas Γ ∧ KernelBounds Γ α 2 k ∧
      (Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        k p.1 p.2) := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  refine ⟨π / 2, constConfig ⟨v, hv, π / 2, by linarith, le_rfl⟩, jumpKernel d α,
    by linarith, le_rfl, isBounded_constConfig (by linarith) le_rfl hv,
    condMeas_constConfig _, kernelBounds_jumpKernel _ α, measurable_jumpKernel d α⟩


/-! ## Narrow cones: a densely visible type

The obstruction in dimension three and above is that the cones at `s` and at `t`
can be disjoint, so no single point sees both. But the chaining never needed the
intermediate point to be seen *by the cones of the endpoints*: it needs the three
points to be joined by cone pairs, and a pair `(s,z)` is a cone pair as soon as
`s − z` lies in the cone at `z`. So it is enough that the intermediate points be
of one fixed type — the balls of `exists_ball_in_two_cones` are available for
*every* pair, since that lemma constrains only the direction `v`, not the
configuration.

What has to be paid for is measure: the average is over the part of the ball
that has the right type. The hypothesis below asks exactly that this part be a
fixed fraction. -/

/-- A double cone `W` is **densely visible** for `Γ`, with density `c₀`, if the
set of points whose cone contains `W` meets every ball in measure at least
`c₀ r^d`.

This holds trivially with `c₀ = c_d` when every cone of `Γ` contains `W`; it is
strictly weaker, and unlike a common direction it constrains the configuration
only on a set of positive density. -/
def VisibleDense {d : ℕ} (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (W : Set (EuclideanSpace ℝ (Fin d))) (c₀ : ℝ) : Prop :=
  ∀ (y : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r →
    ENNReal.ofReal (c₀ * r ^ d) ≤
      volume ({x : EuclideanSpace ℝ (Fin d) | W ⊆ (Γ x).carrier} ∩ closedBall y r)

/-- **The averaging step, over the common neighbours of the visible type.** -/
theorem osc_weighted_le_visible {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (ϑ : ℝ) {α c₀ : ℝ}
    (hc₀ : 0 ≤ c₀) {U : Set (EuclideanSpace ℝ (Fin d))} (hUm : MeasurableSet U)
    (hU : ∀ (y : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r →
      ENNReal.ofReal (c₀ * r ^ d) ≤ volume (U ∩ closedBall y r))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) {s t : EuclideanSpace ℝ (Fin d)} (hst : s ≠ t) :
    ENNReal.ofReal ((f t - f s) ^ 2) * ENNReal.ofReal (‖s - t‖ ^ (-(d : ℝ) - α)) *
        ENNReal.ofReal c₀
      ≤ ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)) *
        ∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖,
          U.indicator (fun z =>
            ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2)) z := by
  have hr : 0 < ‖s - t‖ := by rw [norm_pos_iff]; exact sub_ne_zero_of_ne hst
  have hw : ‖s - t‖ ^ (-(d : ℝ) - α)
      = ‖s - t‖ ^ (-(2 * (d : ℝ)) - α) * ‖s - t‖ ^ d := by
    rw [← Real.rpow_natCast ‖s - t‖ d, ← Real.rpow_add hr]
    congr 1
    ring
  have heq : ∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖,
        U.indicator (fun z =>
          ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2)) z
      = ∫⁻ z in U ∩ closedBall (midCentre v ϑ s t) ‖s - t‖,
          ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2) := by
    rw [lintegral_indicator hUm, Measure.restrict_restrict hUm]
  have hpt : ENNReal.ofReal ((f t - f s) ^ 2) *
        volume (U ∩ closedBall (midCentre v ϑ s t) ‖s - t‖)
      ≤ ∫⁻ z in U ∩ closedBall (midCentre v ϑ s t) ‖s - t‖,
          ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2) := by
    rw [← setLIntegral_const (U ∩ closedBall (midCentre v ϑ s t) ‖s - t‖)
      (ENNReal.ofReal ((f t - f s) ^ 2))]
    refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
    nlinarith [sq_nonneg (f z - f s - (f t - f z)), sq_nonneg (f z - f s + (f t - f z))]
  calc ENNReal.ofReal ((f t - f s) ^ 2) * ENNReal.ofReal (‖s - t‖ ^ (-(d : ℝ) - α)) *
        ENNReal.ofReal c₀
      = ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)) *
          (ENNReal.ofReal ((f t - f s) ^ 2) * ENNReal.ofReal (c₀ * ‖s - t‖ ^ d)) := by
        rw [hw, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hc₀]
        ring
    _ ≤ ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)) *
          (ENNReal.ofReal ((f t - f s) ^ 2) *
            volume (U ∩ closedBall (midCentre v ϑ s t) ‖s - t‖)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (hU _ _ hr))
    _ ≤ ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)) *
          ∫⁻ z in U ∩ closedBall (midCentre v ϑ s t) ‖s - t‖,
            ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2) :=
        mul_le_mul' le_rfl hpt
    _ = ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)) *
          ∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖,
            U.indicator (fun z =>
              ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2)) z := by
        rw [heq]


/-- **The local Poincaré inequality with a densely visible type.** The full
fractional energy is controlled by the energy of the pairs `(s,z)` with
`z − s ∈ Ṽ(v,ϑ)` **and `z` of the visible type** — which is the class the lower
bound of (1.4) can read, through the cone at `z`. -/
theorem localPoincare_visible {d : ℕ} {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α c₀ : ℝ} (hα : 0 ≤ α) (hd : 0 < d)
    (hc₀ : 0 ≤ c₀) {U : Set (EuclideanSpace ℝ (Fin d))} (hUm : MeasurableSet U)
    (hU : ∀ (y : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r →
      ENNReal.ofReal (c₀ * r ^ d) ≤ volume (U ∩ closedBall y r))
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) :
    ENNReal.ofReal c₀ * ∫⁻ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
        ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α))
      ≤ ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
          (∫⁻ s, ∫⁻ z in {z | z - s ∈ cone v ϑ},
            U.indicator (fun z => ENNReal.ofReal (2 * (f z - f s) ^ 2)) z *
              ENNReal.ofReal (‖z - s‖ ^ (-(d : ℝ) - α)))
        + ENNReal.ofReal (chainConst' d ϑ α) * unitBallVol d *
          (∫⁻ t, ∫⁻ z in {z | z - t ∈ cone v ϑ},
            U.indicator (fun z => ENNReal.ofReal (2 * (f t - f z) ^ 2)) z *
              ENNReal.ofReal (‖z - t‖ ^ (-(d : ℝ) - α))) := by
  set A : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 * (d : ℝ)) - α)) *
      ∫⁻ z in closedBall (midCentre v ϑ p.1 p.2) ‖p.1 - p.2‖,
        U.indicator (fun z => ENNReal.ofReal (2 * (f z - f p.1) ^ 2)) z with hAdef
  set B : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 * (d : ℝ)) - α)) *
      ∫⁻ z in closedBall (midCentre v ϑ p.1 p.2) ‖p.1 - p.2‖,
        U.indicator (fun z => ENNReal.ofReal (2 * (f p.2 - f z) ^ 2)) z with hBdef
  have hw2m : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 * (d : ℝ)) - α)) := by fun_prop
  have hUsnd : MeasurableSet {q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      EuclideanSpace ℝ (Fin d) | q.2 ∈ U} := hUm.preimage measurable_snd
  have hHA : Measurable fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      EuclideanSpace ℝ (Fin d) =>
      U.indicator (fun z => ENNReal.ofReal (2 * (f z - f q.1.1) ^ 2)) q.2 := by
    have hEq : (fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
          EuclideanSpace ℝ (Fin d) =>
          U.indicator (fun z => ENNReal.ofReal (2 * (f z - f q.1.1) ^ 2)) q.2)
        = {q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
            EuclideanSpace ℝ (Fin d) | q.2 ∈ U}.indicator
            (fun q => ENNReal.ofReal (2 * (f q.2 - f q.1.1) ^ 2)) := by
      funext q
      by_cases hq : q.2 ∈ U
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem (show q ∈ {q | q.2 ∈ U} from hq)]
      · rw [Set.indicator_of_notMem hq,
          Set.indicator_of_notMem (show q ∉ {q | q.2 ∈ U} from hq)]
    rw [hEq]
    exact Measurable.indicator (by fun_prop) hUsnd
  have hHB : Measurable fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      EuclideanSpace ℝ (Fin d) =>
      U.indicator (fun z => ENNReal.ofReal (2 * (f q.1.2 - f z) ^ 2)) q.2 := by
    have hEq : (fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
          EuclideanSpace ℝ (Fin d) =>
          U.indicator (fun z => ENNReal.ofReal (2 * (f q.1.2 - f z) ^ 2)) q.2)
        = {q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
            EuclideanSpace ℝ (Fin d) | q.2 ∈ U}.indicator
            (fun q => ENNReal.ofReal (2 * (f q.1.2 - f q.2) ^ 2)) := by
      funext q
      by_cases hq : q.2 ∈ U
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem (show q ∈ {q | q.2 ∈ U} from hq)]
      · rw [Set.indicator_of_notMem hq,
          Set.indicator_of_notMem (show q ∉ {q | q.2 ∈ U} from hq)]
    rw [hEq]
    exact Measurable.indicator (by fun_prop) hUsnd
  have hGs : ∀ s : EuclideanSpace ℝ (Fin d),
      Measurable (U.indicator fun z => ENNReal.ofReal (2 * (f z - f s) ^ 2)) := by
    intro s; exact Measurable.indicator (by fun_prop) hUm
  have hGt : ∀ t : EuclideanSpace ℝ (Fin d),
      Measurable (U.indicator fun z => ENNReal.ofReal (2 * (f t - f z) ^ 2)) := by
    intro t; exact Measurable.indicator (by fun_prop) hUm
  have hAm : Measurable A := by
    rw [hAdef]; exact hw2m.mul (measurable_param_midBall v ϑ hHA)
  have hBm : Measurable B := by
    rw [hBdef]; exact hw2m.mul (measurable_param_midBall v ϑ hHB)
  -- the pointwise bound
  have hptwise : ∀ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
        ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α)) * ENNReal.ofReal c₀
        ≤ A p + B p := by
    rintro ⟨s, t⟩
    by_cases hst : s = t
    · subst hst
      simp only [sub_self, norm_zero]
      rw [Real.zero_rpow (by
        have : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
        intro hc; linarith), ENNReal.ofReal_zero]
      simp
    · have hsplit : ∀ z : EuclideanSpace ℝ (Fin d),
          U.indicator (fun z => ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2)) z
            = U.indicator (fun z => ENNReal.ofReal (2 * (f z - f s) ^ 2)) z
              + U.indicator (fun z => ENNReal.ofReal (2 * (f t - f z) ^ 2)) z := by
        intro z
        by_cases hz : z ∈ U
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Set.indicator_of_mem hz,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz,
            Set.indicator_of_notMem hz, add_zero]
      have hsum : ∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖,
            U.indicator (fun z =>
              ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2)) z
          = (∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖,
              U.indicator (fun z => ENNReal.ofReal (2 * (f z - f s) ^ 2)) z)
            + ∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖,
              U.indicator (fun z => ENNReal.ofReal (2 * (f t - f z) ^ 2)) z := by
        rw [← lintegral_add_left (hGs s)]
        exact lintegral_congr fun z => hsplit z
      refine le_trans (osc_weighted_le_visible v ϑ hc₀ hUm hU f hst) (le_of_eq ?_)
      rw [hAdef, hBdef, ← mul_add]
      exact congrArg _ hsum
  calc ENNReal.ofReal c₀ * ∫⁻ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α))
      = ∫⁻ p, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α)) * ENNReal.ofReal c₀ := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun p => by ring
    _ ≤ ∫⁻ p, (A p + B p) := lintegral_mono hptwise
    _ = (∫⁻ p, A p) + ∫⁻ p, B p := lintegral_add_left hAm _
    _ ≤ ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
          (∫⁻ s, ∫⁻ z in {z | z - s ∈ cone v ϑ},
            U.indicator (fun z => ENNReal.ofReal (2 * (f z - f s) ^ 2)) z *
              ENNReal.ofReal (‖z - s‖ ^ (-(d : ℝ) - α)))
        + ENNReal.ofReal (chainConst' d ϑ α) * unitBallVol d *
          (∫⁻ t, ∫⁻ z in {z | z - t ∈ cone v ϑ},
            U.indicator (fun z => ENNReal.ofReal (2 * (f t - f z) ^ 2)) z *
              ENNReal.ofReal (‖z - t‖ ^ (-(d : ℝ) - α))) := by
        refine add_le_add ?_ ?_
        · rw [Measure.volume_eq_prod, lintegral_prod _ hAm.aemeasurable,
            ← lintegral_const_mul' _ _
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top unitBallVol_ne_top)]
          exact lintegral_mono fun s => lintegral_swap_fibre hv hϑ hϑ' hα hd s (hGs s)
        · rw [Measure.volume_eq_prod, lintegral_prod_symm _ hBm.aemeasurable,
            ← lintegral_const_mul' _ _
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top unitBallVol_ne_top)]
          exact lintegral_mono fun t => lintegral_swap_fibre' hv hϑ hϑ' hα hd t (hGt t)


/-- **The open statement of §3.2, for a densely visible type — narrow cones, any
dimension.** If some double cone `Ṽ(v,ϑ)` is contained in the cones of a set of
points of positive density, then finiteness of the `H_k` form forces finiteness
of the `H^{α/2}` form.

No hypothesis on the apex angle beyond `ϑ ≤ π/2`, and none on the dimension: the
chain `s → z → t` runs through a point `z` of the visible type, and both of its
legs are cone pairs **through the cone at `z`**, not through the cones at `s` and
`t` — which may well be disjoint. -/
theorem formHs_le_form_of_visibleDense {d : ℕ} {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α) (hd : 0 < d)
    {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {Λ c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (hmeas : CondMeas Γ)
    (hvis : VisibleDense Γ (doubleCone v ϑ) c₀)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    ENNReal.ofReal c₀ * formHs Set.univ α f
      ≤ ENNReal.ofReal (2 * Λ) *
          (ENNReal.ofReal (chainConst d ϑ α) + ENNReal.ofReal (chainConst' d ϑ α)) *
          unitBallVol d * form Set.univ k f := by
  have hΛ : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hk.one_le
  set U : Set (EuclideanSpace ℝ (Fin d)) :=
    {x | doubleCone v ϑ ⊆ (Γ x).carrier} with hUdef
  have hUm : MeasurableSet U := hmeas _
  -- the `H_k` form as an iterated integral
  have hform : form Set.univ k f
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((f y - f x) ^ 2) * k x y := by
    rw [form, Set.univ_prod_univ, setLIntegral_univ, Measure.volume_eq_prod,
      lintegral_prod _ hkm.aemeasurable]
  have hconeMeas : ∀ x : EuclideanSpace ℝ (Fin d),
      MeasurableSet {y : EuclideanSpace ℝ (Fin d) | y - x ∈ cone v ϑ} := fun x =>
    ((isOpen_cone v ϑ).preimage (by fun_prop)).measurableSet
  -- each cone-and-type-restricted term is dominated by the `H_k` form
  have hterm : ∀ (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ),
      (∀ x y, (g x y) ^ 2 = (f y - f x) ^ 2) →
      (∫⁻ x, ∫⁻ y in {y | y - x ∈ cone v ϑ},
          U.indicator (fun y => ENNReal.ofReal (2 * (g x y) ^ 2)) y *
            ENNReal.ofReal (‖y - x‖ ^ (-(d : ℝ) - α)))
        ≤ ENNReal.ofReal (2 * Λ) * form Set.univ k f := by
    intro g hg
    rw [hform, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ∫⁻ y in {y | y - x ∈ cone v ϑ},
          U.indicator (fun y => ENNReal.ofReal (2 * (g x y) ^ 2)) y *
            ENNReal.ofReal (‖y - x‖ ^ (-(d : ℝ) - α))
        ≤ ∫⁻ y in {y | y - x ∈ cone v ϑ},
            ENNReal.ofReal (2 * Λ) * (ENNReal.ofReal ((f y - f x) ^ 2) * k x y) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem (hconeMeas x)] with y hyc
          by_cases hyU : y ∈ U
          · -- `y` has the visible type, so `x` lies in the cone at `y`
            have hxy : x ∈ coneAt Γ y := by
              have hmem : x - y ∈ doubleCone v ϑ := by
                have : y - x ∈ cone v ϑ := hyc
                refine Or.inr ?_
                rw [Set.mem_neg]
                simpa using this
              exact hyU hmem
            have hjk : ENNReal.ofReal (‖y - x‖ ^ (-(d : ℝ) - α))
                ≤ ENNReal.ofReal Λ * k x y := by
              have h0 : ENNReal.ofReal (‖y - x‖ ^ (-(d : ℝ) - α)) = jumpKernel d α y x := by
                rw [jumpKernel]
              have h1 : jumpKernel d α y x ≤ ENNReal.ofReal Λ * k y x :=
                jumpKernel_le_of_mem_coneAt hk hxy
              rw [h0, hk.symm y x] at *
              exact h1
            rw [Set.indicator_of_mem hyU]
            calc ENNReal.ofReal (2 * (g x y) ^ 2) *
                  ENNReal.ofReal (‖y - x‖ ^ (-(d : ℝ) - α))
                ≤ ENNReal.ofReal (2 * (f y - f x) ^ 2) * (ENNReal.ofReal Λ * k x y) := by
                  rw [hg]; exact mul_le_mul' le_rfl hjk
              _ = ENNReal.ofReal (2 * Λ) * (ENNReal.ofReal ((f y - f x) ^ 2) * k x y) := by
                  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
                    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
                  ring
          · rw [Set.indicator_of_notMem hyU, zero_mul]
            exact bot_le
      _ ≤ ∫⁻ y, ENNReal.ofReal (2 * Λ) * (ENNReal.ofReal ((f y - f x) ^ 2) * k x y) := by
          exact lintegral_mono' Measure.restrict_le_self le_rfl
  -- assemble
  have hlhs : ENNReal.ofReal c₀ * formHs Set.univ α f
      = ENNReal.ofReal c₀ * ∫⁻ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
            ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α)) := by
    rw [formHs, form, Set.univ_prod_univ, setLIntegral_univ]
    rfl
  rw [hlhs]
  refine le_trans (localPoincare_visible hv hϑ hϑ' hα hd hc₀ hUm hvis hf) ?_
  have hA := hterm (fun x y => f y - f x) (fun x y => rfl)
  have hB := hterm (fun x y => f x - f y) (fun x y => by ring)
  calc ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
        (∫⁻ s, ∫⁻ z in {z | z - s ∈ cone v ϑ},
          U.indicator (fun z => ENNReal.ofReal (2 * (f z - f s) ^ 2)) z *
            ENNReal.ofReal (‖z - s‖ ^ (-(d : ℝ) - α)))
      + ENNReal.ofReal (chainConst' d ϑ α) * unitBallVol d *
        (∫⁻ t, ∫⁻ z in {z | z - t ∈ cone v ϑ},
          U.indicator (fun z => ENNReal.ofReal (2 * (f t - f z) ^ 2)) z *
            ENNReal.ofReal (‖z - t‖ ^ (-(d : ℝ) - α)))
      ≤ ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
          (ENNReal.ofReal (2 * Λ) * form Set.univ k f)
        + ENNReal.ofReal (chainConst' d ϑ α) * unitBallVol d *
          (ENNReal.ofReal (2 * Λ) * form Set.univ k f) :=
        add_le_add (mul_le_mul' le_rfl hA) (mul_le_mul' le_rfl hB)
    _ = ENNReal.ofReal (2 * Λ) *
          (ENNReal.ofReal (chainConst d ϑ α) + ENNReal.ofReal (chainConst' d ϑ α)) *
          unitBallVol d * form Set.univ k f := by ring


/-! ### How far the one-point chaining reaches

The hypothesis of `formHs_le_form_of_visibleDense` asks for density at *every*
scale, because pairs at every distance need intermediate points. By the Lebesgue
density theorem that forces the visible set to be co-null: a set of uniform
positive density at all scales has null complement. So the theorem above is
exactly the almost-everywhere form of the common-direction theorem, and **no
sparser set of good types can serve a chaining argument with a single
intermediate point** — which is why the narrow-cone case in dimension three and
above needs chains of length at least three, and with them the continuum
analogue of §§5–6. -/

/-- A set of uniform positive density at all scales has null complement. -/
theorem null_compl_of_uniform_density {d : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin d))} (hUm : MeasurableSet U) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hU : ∀ (y : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r →
      ENNReal.ofReal (c₀ * r ^ d) ≤ volume (U ∩ closedBall y r)) :
    volume Uᶜ = 0 := by
  by_contra hne
  have hnb : (ae (volume.restrict (Uᶜ : Set (EuclideanSpace ℝ (Fin d))))).NeBot := by
    refine MeasureTheory.ae_neBot.mpr ?_
    simpa [Measure.restrict_apply_univ] using hne
  obtain ⟨x, hxdens⟩ := (Besicovitch.ae_tendsto_measure_inter_div
    (volume : Measure (EuclideanSpace ℝ (Fin d))) Uᶜ).exists
  have hunit0 : unitBallVol d ≠ 0 := unitBallVol_ne_zero d
  have hunitR : 0 < (unitBallVol d).toReal := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨pos_iff_ne_zero.mpr hunit0, lt_of_le_of_ne le_top unitBallVol_ne_top⟩
  obtain ⟨u, hu0, hu⟩ : ∃ u : ℝ, 0 < u ∧ unitBallVol d = ENNReal.ofReal u :=
    ⟨(unitBallVol d).toReal, hunitR, (ENNReal.ofReal_toReal unitBallVol_ne_top).symm⟩
  set δ : ℝ≥0∞ := ENNReal.ofReal (c₀ / u) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    simp only [ENNReal.ofReal_pos]
    positivity
  have key : ∀ r : ℝ, 0 < r →
      volume (Uᶜ ∩ closedBall x r) / volume (closedBall x r) ≤ 1 - δ := by
    intro r hr
    have hrd : (0:ℝ) < r ^ d := by positivity
    have hbv : volume (closedBall x r) = ENNReal.ofReal (r ^ d) * unitBallVol d :=
      volume_closedBall_eq x hr.le
    have hbvne : volume (closedBall x r) ≠ 0 := by
      rw [hbv]; exact mul_ne_zero (by simpa using hrd) hunit0
    have hbvtop : volume (closedBall x r) ≠ ∞ := measure_closedBall_lt_top.ne
    have hsplit : volume (U ∩ closedBall x r) + volume (Uᶜ ∩ closedBall x r)
        = volume (closedBall x r) := by
      rw [Set.inter_comm U, Set.inter_comm Uᶜ, ← Set.sdiff_eq]
      exact measure_inter_add_sdiff _ hUm
    have hAtop : volume (U ∩ closedBall x r) ≠ ∞ :=
      ne_top_of_le_ne_top hbvtop (measure_mono Set.inter_subset_right)
    have hδV : δ * volume (closedBall x r) ≤ volume (U ∩ closedBall x r) := by
      have hune : u ≠ 0 := ne_of_gt hu0
      have hval : δ * volume (closedBall x r) = ENNReal.ofReal (c₀ * r ^ d) := by
        rw [hδdef, hbv, hu, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
      rw [hval]
      exact hU x r hr
    have hC : volume (Uᶜ ∩ closedBall x r)
        = volume (closedBall x r) - volume (U ∩ closedBall x r) := by
      rw [← hsplit]
      exact (ENNReal.add_sub_cancel_left hAtop).symm
    refine ENNReal.div_le_of_le_mul ?_
    rw [hC]
    calc volume (closedBall x r) - volume (U ∩ closedBall x r)
        ≤ volume (closedBall x r) - δ * volume (closedBall x r) :=
          tsub_le_tsub_left hδV _
      _ = (1 - δ) * volume (closedBall x r) := by
          rw [ENNReal.sub_mul (fun _ _ => hbvtop), one_mul]
  have hle : (1 : ℝ≥0∞) ≤ 1 - δ := by
    refine le_of_tendsto hxdens ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact key r hr
  exact absurd hle
    (not_le.mpr (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (ne_of_gt hδpos)))


/-- Almost-everywhere visibility gives density with the constant of the unit
ball. -/
theorem visibleDense_of_ae {d : ℕ} {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {W : Set (EuclideanSpace ℝ (Fin d))}
    (hae : ∀ᵐ x : EuclideanSpace ℝ (Fin d), W ⊆ (Γ x).carrier) :
    VisibleDense Γ W ((unitBallVol d).toReal) := by
  intro y r hr
  have hnull : volume {x : EuclideanSpace ℝ (Fin d) | ¬ (W ⊆ (Γ x).carrier)} = 0 :=
    ae_iff.mp hae
  have hdiff : volume (closedBall y r \ {x : EuclideanSpace ℝ (Fin d) |
      W ⊆ (Γ x).carrier}) = 0 := by
    refine measure_mono_null ?_ hnull
    intro z hz
    exact hz.2
  have hle : volume (closedBall y r)
      ≤ volume (closedBall y r ∩ {x : EuclideanSpace ℝ (Fin d) | W ⊆ (Γ x).carrier}) := by
    refine le_trans (measure_le_inter_add_sdiff volume (closedBall y r)
      {x : EuclideanSpace ℝ (Fin d) | W ⊆ (Γ x).carrier}) ?_
    rw [hdiff, add_zero]
  rw [Set.inter_comm]
  refine le_trans ?_ hle
  rw [volume_closedBall_eq y hr.le]
  obtain ⟨u, hu0, hu⟩ : ∃ u : ℝ, 0 ≤ u ∧ unitBallVol d = ENNReal.ofReal u :=
    ⟨(unitBallVol d).toReal, ENNReal.toReal_nonneg,
      (ENNReal.ofReal_toReal (unitBallVol_ne_top (d := d))).symm⟩
  rw [hu, ← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal hu0]
  exact le_of_eq (by ring_nf)

/-- **The common-direction theorem, needing the direction only almost
everywhere.** By `null_compl_of_uniform_density` this is the exact reach of a
chaining argument with a single intermediate point: the intermediate points must
be available at every scale, and a set of positive density at every scale is
co-null. -/
theorem formHs_le_form_of_ae_commonDirection {d : ℕ} {v : EuclideanSpace ℝ (Fin d)}
    (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α) (hd : 0 < d)
    {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {Λ : ℝ}
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (hmeas : CondMeas Γ)
    (hae : ∀ᵐ x : EuclideanSpace ℝ (Fin d), doubleCone v ϑ ⊆ (Γ x).carrier)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    unitBallVol d * formHs Set.univ α f
      ≤ ENNReal.ofReal (2 * Λ) *
          (ENNReal.ofReal (chainConst d ϑ α) + ENNReal.ofReal (chainConst' d ϑ α)) *
          unitBallVol d * form Set.univ k f := by
  have hmain := formHs_le_form_of_visibleDense hv hϑ hϑ' hα hd
    (c₀ := (unitBallVol d).toReal) ENNReal.toReal_nonneg hk
      hmeas (visibleDense_of_ae hae) hf hkm
  rwa [ENNReal.ofReal_toReal (unitBallVol_ne_top (d := d))] at hmain


/-! ## Pairwise overlapping cones: narrow cones without a common direction

Chains of length three or more cannot help (see the note below), but chains of
length two reach further than the wide-cone case suggests. All they need is that
the two cones **overlap** — the intermediate point is then seen by both
endpoints' own cones, and no constraint is placed on its type. Overlapping is
strictly weaker than sharing a direction: three cones can pairwise overlap with
no direction common to all three, and that happens for narrow cones in dimension
three and above. -/

/-- **A block of two overlapping types is controlled.** The hypothesis is a cone
`Ṽ(u,η)` inside the cones of every point of `A` and of every point of `B`; no
apex angle and no dimension enters. -/
theorem overlap_block_le {d : ℕ} (hd : 0 < d) {α Λ η : ℝ} (hη0 : 0 < η) (hη2 : η ≤ π / 2)
    (hα : 0 ≤ α)
    {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2)
    {A B : Set (EuclideanSpace ℝ (Fin d))} (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    {u : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1)
    (hA : ∀ x ∈ A, cone u η ⊆ (Γ x).carrier)
    (hB : ∀ x ∈ B, cone u η ⊆ (Γ x).carrier) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∫⁻ p in A ×ˢ B, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2
        ≤ C * form Set.univ k f := by
  set U : Set (EuclideanSpace ℝ (Fin d)) := A ∪ B with hU
  have hUm : MeasurableSet U := hAm.union hBm
  have hcommon : ∀ x ∈ U, cone u η ⊆ (Γ x).carrier := by
    intro x hx
    rcases hx with hx | hx
    · exact hA x hx
    · exact hB x hx
  have hmain := formHs_le_form_of_commonDirection_on hu hη0 hη2 hα hd hk hUm hcommon hf hkm
  set K : ℝ≥0∞ := ENNReal.ofReal (2 * Λ) *
    (ENNReal.ofReal (chainConst d η α) + ENNReal.ofReal (chainConst' d η α)) *
    unitBallVol d with hK
  have hKtop : K ≠ ∞ := by
    rw [hK]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩))
      unitBallVol_ne_top
  refine ⟨(unitBallVol d)⁻¹ * K, ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr (unitBallVol_ne_zero d)) hKtop, ?_⟩
  have hsub : A ×ˢ B ⊆ U ×ˢ U :=
    Set.prod_mono Set.subset_union_left Set.subset_union_right
  calc ∫⁻ p in A ×ˢ B, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2
      ≤ ∫⁻ p in U ×ˢ U, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2 :=
        lintegral_mono_set hsub
    _ = (unitBallVol d)⁻¹ * (unitBallVol d *
          ∫⁻ p in U ×ˢ U, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (unitBallVol_ne_zero d) unitBallVol_ne_top,
          one_mul]
    _ ≤ (unitBallVol d)⁻¹ * (K * form Set.univ k f) := mul_le_mul' le_rfl hmain
    _ = (unitBallVol d)⁻¹ * K * form Set.univ k f := by rw [hK]; ring

/-- **`H_k ⊆ H^{α/2}` for a pairwise overlapping family of cone types**, in every
dimension and at any apex angle.

The family `W` need not have a direction common to all of it: pairwise overlap
suffices, and pairwise overlap does not imply a common direction — three cones
of apex `θ` whose axes form a spherical triangle of side just under `2θ` overlap
pairwise, while their circumradius exceeds `θ`. -/
theorem sobolevInclusion_of_overlapping {d : ℕ} (hd : 0 < d) {α Λ η : ℝ}
    (hη0 : 0 < η) (hη2 : η ≤ π / 2) (hα : 0 ≤ α)
    {Γ : Configuration (EuclideanSpace ℝ (Fin d))} (hmeas : CondMeas Γ)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k)
    {ι : Type} [Finite ι] (W : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hcover : ∀ x : EuclideanSpace ℝ (Fin d), ∃ i, W i ⊆ (Γ x).carrier)
    (hcompat : ∀ i j : ι, ∃ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 ∧
      cone u η ⊆ W i ∧ cone u η ⊆ W j)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ formHs Set.univ α f ≤ C * form Set.univ k f := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  set blk : ι × ι → Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) := fun i =>
    {x | W i.1 ⊆ (Γ x).carrier} ×ˢ {x | W i.2 ⊆ (Γ x).carrier} with hblk
  have hcover' : (⋃ i, blk i) = Set.univ := by
    refine Set.eq_univ_of_forall fun p => ?_
    obtain ⟨i, hi⟩ := hcover p.1
    obtain ⟨j, hj⟩ := hcover p.2
    exact Set.mem_iUnion.mpr ⟨(i, j), hi, hj⟩
  choose u hu h1 h2 using hcompat
  choose C hCtop hCle using fun i : ι × ι =>
    overlap_block_le hd hη0 hη2 hα hk hf hkm (hmeas (W i.1)) (hmeas (W i.2)) (hu i.1 i.2)
      (fun x hx => le_trans (h1 i.1 i.2) hx) (fun x hx => le_trans (h2 i.1 i.2) hx)
  refine ⟨∑' i, C i, ?_, ?_⟩
  · rw [tsum_fintype]
    exact (ENNReal.sum_lt_top.mpr fun i _ => (hCtop i).lt_top).ne
  · have hlhs : formHs Set.univ α f
        = ∫⁻ p in ⋃ i, blk i,
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2 := by
      rw [hcover', formHs, form, Set.univ_prod_univ]
    rw [hlhs]
    calc ∫⁻ p in ⋃ i, blk i,
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2
        ≤ ∑' i, ∫⁻ p in blk i,
            ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2 :=
          lintegral_iUnion_le _ _
      _ ≤ ∑' i, C i * form Set.univ k f := ENNReal.tsum_le_tsum hCle
      _ = (∑' i, C i) * form Set.univ k f := ENNReal.tsum_mul_right


/-! ### When do two cones overlap?

The bisector argument of `exists_common_subcone` is not about `π/4`: two double
cones of apex `θ` overlap in a cone of aperture `θ − β`, where `β` is half the
angle between their axes. The `π/4` threshold is what makes *every* pair overlap;
a particular pair needs only its own axes to be close. -/

/-- An inner product at least `cos c` between unit vectors means an angle at most
`c`. -/
lemma angle_le_of_cos_le_inner {v u : E} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) {c : ℝ}
    (hc0 : 0 ≤ c) (hcπ : c ≤ π) (h : Real.cos c ≤ ⟪v, u⟫_ℝ) :
    InnerProductGeometry.angle v u ≤ c := by
  rw [InnerProductGeometry.angle, hv, hu, one_mul, div_one]
  exact le_trans (Real.arccos_le_arccos h) (le_of_eq (Real.arccos_cos hc0 hcπ))

private theorem exists_common_subcone_aux' {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hc : (0 : ℝ) ≤ ⟪v, w⟫_ℝ) {θ η : ℝ} (hη : 0 < η) (hθ : θ ≤ π / 2) (hηθ : η ≤ θ)
    (hbis : Real.cos (θ - η) ≤ Real.sqrt ((1 + ⟪v, w⟫_ℝ) / 2)) :
    ∃ u : E, ‖u‖ = 1 ∧ doubleCone u η ⊆ doubleCone v θ ∧
      doubleCone u η ⊆ doubleCone w θ := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hvv : ⟪v, v⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hww : ⟪w, w⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hne : v + w ≠ 0 := by
    intro h
    have hwv : w = -v := by
      have := congrArg (fun z => z - v) h
      simpa using this
    rw [hwv, inner_neg_right, hvv] at hc
    linarith
  set N : ℝ := ‖v + w‖ with hN
  have hNpos : 0 < N := norm_pos_iff.mpr hne
  have hNsq : N ^ 2 = 2 + 2 * ⟪v, w⟫_ℝ := by
    rw [hN, @norm_add_sq_real, hv, hw]; ring
  have hNval : N = Real.sqrt (2 + 2 * ⟪v, w⟫_ℝ) := by
    rw [← hNsq, Real.sqrt_sq hNpos.le]
  set u : E := N⁻¹ • (v + w) with hu
  have hunorm : ‖u‖ = 1 := by rw [hu, hN]; exact norm_smul_inv_norm hne
  have hmul : Real.sqrt ((1 + ⟪v, w⟫_ℝ) / 2) * N = 1 + ⟪v, w⟫_ℝ := by
    rw [hNval, ← Real.sqrt_mul (by positivity)]
    rw [show (1 + ⟪v, w⟫_ℝ) / 2 * (2 + 2 * ⟪v, w⟫_ℝ) = (1 + ⟪v, w⟫_ℝ) ^ 2 from by ring]
    exact Real.sqrt_sq (by linarith)
  have hkey : ∀ x : E, ⟪x, v⟫_ℝ + ⟪x, w⟫_ℝ = 1 + ⟪v, w⟫_ℝ →
      ⟪x, u⟫_ℝ = Real.sqrt ((1 + ⟪v, w⟫_ℝ) / 2) := by
    intro x hx
    rw [hu, real_inner_smul_right, inner_add_right, hx, inv_mul_eq_div,
      div_eq_iff (ne_of_gt hNpos)]
    exact hmul.symm
  have hvu : Real.cos (θ - η) ≤ ⟪v, u⟫_ℝ := by
    rw [hkey v (by rw [hvv])]; exact hbis
  have hwu : Real.cos (θ - η) ≤ ⟪w, u⟫_ℝ := by
    rw [hkey w (by rw [hww, real_inner_comm]; ring)]; exact hbis
  have hrange : (0:ℝ) ≤ θ - η := by linarith
  have hrange' : θ - η ≤ π := by linarith
  have hdv : dangle v u ≤ θ - η :=
    le_trans (min_le_left _ _) (angle_le_of_cos_le_inner hv hunorm hrange hrange' hvu)
  have hdw : dangle w u ≤ θ - η :=
    le_trans (min_le_left _ _) (angle_le_of_cos_le_inner hw hunorm hrange hrange' hwu)
  refine ⟨u, hunorm, ?_, ?_⟩
  · have := doubleCone_subset_of_dangle_le hv hunorm (a := θ - η) (η := η) hrange hη.le
      (by linarith) hdv
    rwa [show θ - η + η = θ from by ring] at this
  · have := doubleCone_subset_of_dangle_le hw hunorm (a := θ - η) (η := η) hrange hη.le
      (by linarith) hdw
    rwa [show θ - η + η = θ from by ring] at this

/-- **Two double cones overlap when their axes are close.** If the bisector's
inner product with each axis is at least `cos (θ − η)`, the cone of aperture `η`
about the bisector lies in both. -/
theorem exists_common_subcone_of_inner {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    {θ η : ℝ} (hη : 0 < η) (hθ : θ ≤ π / 2) (hηθ : η ≤ θ)
    (hbis : Real.cos (θ - η) ≤ Real.sqrt ((1 + |⟪v, w⟫_ℝ|) / 2)) :
    ∃ u : E, ‖u‖ = 1 ∧ doubleCone u η ⊆ doubleCone v θ ∧ doubleCone u η ⊆ doubleCone w θ := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  -- replace `w` by `-w` if necessary, so that the inner product is nonnegative
  by_cases hsign : (0 : ℝ) ≤ ⟪v, w⟫_ℝ
  · have habs : |⟪v, w⟫_ℝ| = ⟪v, w⟫_ℝ := abs_of_nonneg hsign
    rw [habs] at hbis
    exact exists_common_subcone_aux' hv hw hsign hη hθ hηθ hbis
  · have hneg : ⟪v, w⟫_ℝ < 0 := not_le.mp hsign
    have hnw : ‖(-w : E)‖ = 1 := by simpa using hw
    have hsign' : (0:ℝ) ≤ ⟪v, -w⟫_ℝ := by rw [inner_neg_right]; linarith
    have habs : |⟪v, w⟫_ℝ| = ⟪v, -w⟫_ℝ := by
      rw [inner_neg_right, abs_of_neg hneg]
    rw [habs] at hbis
    obtain ⟨u, hu, h1, h2⟩ := exists_common_subcone_aux' hv hnw hsign' hη hθ hηθ hbis
    exact ⟨u, hu, h1, by rwa [doubleCone_neg] at h2⟩

/-! ### The overlap hypothesis is not vacuous, and is strictly weaker

Three unit vectors in `ℝ³` with pairwise inner product `8/9`, and the apex
`θ = arccos √(14/15) ≈ 15°` — far below the `π/4` at which every pair of double
cones is forced to meet. The three cones still overlap pairwise, because half the
angle between two axes is `arccos √(17/18) < θ`; but no direction lies in all
three at once, because for a unit `u`

  `∑ᵢ ⟪vᵢ, u⟫² = (8 (u₀+u₁+u₂)² + 1)/9 ≤ 25/9 < 3 · 14/15`,

so some `|⟪vᵢ, u⟫|` falls below `cos θ = √(14/15)`. Neither
`sobolevInclusion_wide` nor `formHs_le_form_of_commonDirection` applies to such a
configuration; `sobolevInclusion_of_overlapping` does. -/

noncomputable def exAxis : Fin 3 → EuclideanSpace ℝ (Fin 3)
  | 0 => !₂[1/3, 2/3, 2/3]
  | 1 => !₂[2/3, 1/3, 2/3]
  | 2 => !₂[2/3, 2/3, 1/3]

noncomputable def exApex : ℝ := Real.arccos (Real.sqrt (14/15))

noncomputable def exAperture : ℝ := exApex - Real.arccos (Real.sqrt (17/18))

lemma exAxis_norm (i : Fin 3) : ‖exAxis i‖ = 1 := by
  have h : ‖exAxis i‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    fin_cases i <;> simp [exAxis, Fin.sum_univ_three] <;> norm_num
  nlinarith [norm_nonneg (exAxis i)]

lemma exAxis_inner_ge (i j : Fin 3) : (8 : ℝ) / 9 ≤ ⟪exAxis i, exAxis j⟫_ℝ := by
  fin_cases i <;> fin_cases j <;>
    simp only [exAxis, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;> norm_num

lemma sqrt_14_15_le_one : Real.sqrt (14/15) ≤ 1 := by
  rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

lemma sqrt_17_18_le_one : Real.sqrt (17/18) ≤ 1 := by
  rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

lemma cos_exApex : Real.cos exApex = Real.sqrt (14/15) :=
  Real.cos_arccos (le_trans (by norm_num) (Real.sqrt_nonneg _)) sqrt_14_15_le_one

lemma exApex_lt_pi_div_four : exApex < π / 4 := by
  have h1 : Real.sqrt 2 / 2 < Real.sqrt (14/15) := by
    nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0),
      Real.sq_sqrt (by norm_num : (14:ℝ)/15 ≥ 0), Real.sqrt_nonneg 2,
      Real.sqrt_nonneg ((14:ℝ)/15)]
  calc exApex < Real.arccos (Real.sqrt 2 / 2) :=
        Real.arccos_lt_arccos (x := Real.sqrt 2 / 2) (y := Real.sqrt (14/15))
          (by linarith [Real.sqrt_nonneg 2]) h1 sqrt_14_15_le_one
    _ ≤ π / 4 := Real.arccos_le_pi_div_four.mpr le_rfl

lemma exApex_pos : 0 < exApex := by
  rw [exApex, Real.arccos_pos]
  nlinarith [Real.sq_sqrt (by norm_num : (14:ℝ)/15 ≥ 0), Real.sqrt_nonneg ((14:ℝ)/15)]

lemma exAperture_pos : 0 < exAperture := by
  have h : Real.arccos (Real.sqrt (17/18)) < exApex :=
    Real.arccos_lt_arccos (x := Real.sqrt (14/15)) (y := Real.sqrt (17/18))
      (le_trans (by norm_num) (Real.sqrt_nonneg _))
      (Real.sqrt_lt_sqrt (by norm_num) (by norm_num)) sqrt_17_18_le_one
  simpa [exAperture, sub_pos] using h

lemma exAperture_le_exApex : exAperture ≤ exApex := by
  have := Real.arccos_nonneg (Real.sqrt (17/18))
  simp only [exAperture]
  linarith

/-- The cones of the example overlap pairwise. -/
theorem ex_overlap (i j : Fin 3) :
    ∃ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 ∧
      doubleCone u exAperture ⊆ doubleCone (exAxis i) exApex ∧
      doubleCone u exAperture ⊆ doubleCone (exAxis j) exApex := by
  refine exists_common_subcone_of_inner (exAxis_norm i) (exAxis_norm j) exAperture_pos
    (le_of_lt (lt_trans exApex_lt_pi_div_four (by linarith [Real.pi_pos])))
    exAperture_le_exApex ?_
  have hsub : exApex - exAperture = Real.arccos (Real.sqrt (17/18)) := by
    simp [exAperture]
  rw [hsub, Real.cos_arccos (le_trans (by norm_num) (Real.sqrt_nonneg _)) sqrt_17_18_le_one]
  have ht : (8:ℝ)/9 ≤ |⟪exAxis i, exAxis j⟫_ℝ| :=
    le_trans (exAxis_inner_ge i j) (le_abs_self _)
  exact Real.sqrt_le_sqrt (by linarith)

/-- No direction lies in all three cones of the example. -/
theorem ex_no_common_direction (u : EuclideanSpace ℝ (Fin 3)) (hu : ‖u‖ = 1) :
    ∃ i, u ∉ doubleCone (exAxis i) exApex := by
  by_contra hcon
  push Not at hcon
  have key : ∀ i, 14/15 < (⟪exAxis i, u⟫_ℝ) ^ 2 := by
    intro i
    have hmem := hcon i
    rw [mem_doubleCone_iff] at hmem
    have habs : Real.sqrt (14/15) < |⟪exAxis i, u⟫_ℝ| := by
      rcases hmem with h | h
      · have h2 := h.2
        rw [hu, div_one, cos_exApex] at h2
        exact lt_of_lt_of_le h2 (le_abs_self _)
      · have h2 := h.2
        rw [norm_neg, hu, div_one, inner_neg_right, cos_exApex] at h2
        exact lt_of_lt_of_le h2 (neg_le_abs _)
    have h0 : (0:ℝ) ≤ Real.sqrt (14/15) := Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt (by norm_num : (14:ℝ)/15 ≥ 0), abs_nonneg (⟪exAxis i, u⟫_ℝ),
      sq_abs (⟪exAxis i, u⟫_ℝ)]
  have hnorm : (u 0) ^ 2 + (u 1) ^ 2 + (u 2) ^ 2 = 1 := by
    have := EuclideanSpace.real_norm_sq_eq u
    rw [hu] at this
    simpa [Fin.sum_univ_three] using this.symm
  have e0 := key 0
  have e1 := key 1
  have e2 := key 2
  simp only [exAxis, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at e0 e1 e2
  nlinarith [sq_nonneg (u 0 - u 1), sq_nonneg (u 1 - u 2), sq_nonneg (u 0 - u 2)]

/-- **Narrow cones that overlap pairwise without a common direction.** The apex
is below `π/4`, every pair of cones contains a common cone of aperture `η > 0`,
and no unit vector lies in all three cones. -/
theorem exists_narrow_overlapping_cones_without_common_direction :
    ∃ (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) (θ η : ℝ),
      0 < θ ∧ θ < π / 4 ∧ 0 < η ∧ (∀ i, ‖v i‖ = 1) ∧
      (∀ i j, ∃ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 ∧
        cone u η ⊆ doubleCone (v i) θ ∧ cone u η ⊆ doubleCone (v j) θ) ∧
      (∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → ∃ i, u ∉ doubleCone (v i) θ) := by
  refine ⟨exAxis, exApex, exAperture, exApex_pos, exApex_lt_pi_div_four, exAperture_pos,
    exAxis_norm, fun i j => ?_, ex_no_common_direction⟩
  obtain ⟨u, hu, h1, h2⟩ := ex_overlap i j
  exact ⟨u, hu, le_trans Set.subset_union_left h1, le_trans Set.subset_union_left h2⟩

/-- **Theorem 1.1 for a narrow, direction-less configuration in dimension three.**
Every point's cone contains one of the three `≈ 15°` double cones of the example
above; no direction is common to all three, so neither the paper's §3.2 (which
needs condition (M) at every point) nor `sobolevInclusion_wide` (which needs an
apex above `π/4`) covers this case. -/
theorem sobolevInclusion_narrow_example {α Λ : ℝ} (hα : 0 ≤ α)
    {Γ : Configuration (EuclideanSpace ℝ (Fin 3))} (hmeas : CondMeas Γ)
    {k : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k)
    (hcover : ∀ x : EuclideanSpace ℝ (Fin 3),
      ∃ i : Fin 3, doubleCone (exAxis i) exApex ⊆ (Γ x).carrier)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Measurable f)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ formHs Set.univ α f ≤ C * form Set.univ k f := by
  have hη2 : exAperture ≤ π / 2 := by
    have := exApex_lt_pi_div_four
    have := exAperture_le_exApex
    have := Real.pi_pos
    linarith
  refine sobolevInclusion_of_overlapping (by norm_num) exAperture_pos hη2 hα hmeas hk
    (fun i : Fin 3 => doubleCone (exAxis i) exApex) hcover (fun i j => ?_) hf hkm
  obtain ⟨u, hu, h1, h2⟩ := ex_overlap i j
  exact ⟨u, hu, le_trans Set.subset_union_left h1, le_trans Set.subset_union_left h2⟩

end QFS
