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

Section 3.2 needs an a priori hypothesis its argument never establishes, and the
formalisation reduces that need to (see the README):

> `liminf_{h → 0} h^{-α}‖f − E_h f‖²_{L²(B*)} < ∞` for every `f ∈ H_k(B*)`,

`E_h` being the average over the tiles of the `h`-tiling. `QFS.oscillation_sameTile_le_form`
settles the part of that modulus carried by pairs which see each other's cones.
What is left is the *off-cone* oscillation inside a single tile.

## What this file proves, and what it does not

The route is a local Poincaré inequality: for a cube `Q` of side `h`,

  (★)  `∫∫_{Q×Q}(f(s) − f(t))² ≤ C(d,ϑ,α,Λ) · h^{d+α} · ∫∫_{Q*×Q*}(f(s) − f(t))² k(s,t)`,

which summed over the tiles bounds `A_h` uniformly and closes the theorem with
Fatou alone. `(★)` is proved by chaining: join `s` to `t` through intermediate
points that *do* see the relevant cones, and average over a positive-measure set
of such chains.

`exists_ball_in_two_cones` is the geometric heart of that argument, and it is
proved here in full. It supplies, for any two distinct points sharing a cone
direction, a **ball** of intermediate points each of which lies in both of their
cones — a positive-measure strengthening of the qualitative "path of length at
most two" of the paper's Lemma 4.3, which produces a single point.

What is **not** proved here is the case of two points whose cones share no
direction. In dimension three, two thin double cones with skew axes need not
meet at all, so one intermediate point cannot suffice and genuinely longer
chains are required; producing them, with a uniform bound on the length and with
positive measure at every link, is the continuous analogue of the paper's §§5–6.
The paper establishes that machinery only in the discrete setting — which is
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
  set w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ :=
    fun t => ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)) with hwdef
  have hwmeas : Measurable w := by rw [hwdef]; fun_prop
  -- the graph of the averaging balls is closed, hence measurable
  have hgraph : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      p.2 ∈ closedBall (midCentre v ϑ s p.1) ‖s - p.1‖} := by
    have h1 : Continuous fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        dist p.2 (midCentre v ϑ s p.1) := by unfold midCentre; fun_prop
    have h2 : Continuous fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ‖s - p.1‖ := by fun_prop
    simpa [Metric.mem_closedBall] using (isClosed_le h1 h2).measurableSet
  -- rewrite the inner set integral as an integral of an indicator, then swap
  have hstep : ∀ t, w t * ∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖, G z
      = ∫⁻ z, w t * (closedBall (midCentre v ϑ s t) ‖s - t‖).indicator G z := by
    intro t
    rw [lintegral_const_mul' _ _ (by simp [hwdef] : w t ≠ ∞),
      lintegral_indicator measurableSet_closedBall]
  have hunc : AEMeasurable (Function.uncurry fun t z =>
      w t * (closedBall (midCentre v ϑ s t) ‖s - t‖).indicator G z) volume := by
    refine Measurable.aemeasurable ?_
    have : (Function.uncurry fun t z =>
        w t * (closedBall (midCentre v ϑ s t) ‖s - t‖).indicator G z)
        = fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
          w p.1 * {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
            p.2 ∈ closedBall (midCentre v ϑ s p.1) ‖s - p.1‖}.indicator
              (fun q => G q.2) p := by
      funext p
      obtain ⟨t, z⟩ := p
      simp only [Function.uncurry]
      by_cases hp : z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖
      · rw [Set.indicator_of_mem hp,
          Set.indicator_of_mem (show (t, z) ∈ {p : EuclideanSpace ℝ (Fin d) ×
            EuclideanSpace ℝ (Fin d) | p.2 ∈ closedBall (midCentre v ϑ s p.1) ‖s - p.1‖}
            from hp)]
      · rw [Set.indicator_of_notMem hp,
          Set.indicator_of_notMem (show (t, z) ∉ {p : EuclideanSpace ℝ (Fin d) ×
            EuclideanSpace ℝ (Fin d) | p.2 ∈ closedBall (midCentre v ϑ s p.1) ‖s - p.1‖}
            from hp)]
    rw [this]
    exact (hwmeas.comp measurable_fst).mul
      ((hG.comp measurable_snd).indicator hgraph)
  calc ∫⁻ t, w t * ∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖, G z
      = ∫⁻ t, ∫⁻ z, w t * (closedBall (midCentre v ϑ s t) ‖s - t‖).indicator G z := by
        exact lintegral_congr hstep
    _ = ∫⁻ z, ∫⁻ t, w t * (closedBall (midCentre v ϑ s t) ‖s - t‖).indicator G z :=
        lintegral_lintegral_swap hunc
    _ ≤ ∫⁻ z, {z | z - s ∈ cone v ϑ}.indicator
          (fun z => G z * (ENNReal.ofReal (chainConst d ϑ α * ‖z - s‖ ^ (-(d : ℝ) - α)) *
            unitBallVol d)) z := by
        refine lintegral_mono fun z => ?_
        have hfibmeas : MeasurableSet {t : EuclideanSpace ℝ (Fin d) |
            z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖} := by
          have h1 : Continuous fun t : EuclideanSpace ℝ (Fin d) =>
              dist z (midCentre v ϑ s t) := by unfold midCentre; fun_prop
          have h2 : Continuous fun t : EuclideanSpace ℝ (Fin d) => ‖s - t‖ := by fun_prop
          simpa [Metric.mem_closedBall] using (isClosed_le h1 h2).measurableSet
        have hpw : ∀ t, w t * (closedBall (midCentre v ϑ s t) ‖s - t‖).indicator G z
            = {t | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖}.indicator
              (fun t => G z * w t) t := by
          intro t
          by_cases hp : z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖
          · rw [Set.indicator_of_mem hp,
              Set.indicator_of_mem (show t ∈ {t | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖}
                from hp)]
            ring
          · rw [Set.indicator_of_notMem hp,
              Set.indicator_of_notMem (show t ∉ {t | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖}
                from hp)]
            simp
        have hfib : ∫⁻ t, w t * (closedBall (midCentre v ϑ s t) ‖s - t‖).indicator G z
            = G z * ∫⁻ t in {t | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖}, w t := by
          calc ∫⁻ t, w t * (closedBall (midCentre v ϑ s t) ‖s - t‖).indicator G z
              = ∫⁻ t, {t | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖}.indicator
                  (fun t => G z * w t) t := lintegral_congr hpw
            _ = ∫⁻ t in {t | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖}, G z * w t :=
                lintegral_indicator hfibmeas _
            _ = G z * ∫⁻ t in {t | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖}, w t :=
                lintegral_const_mul _ hwmeas
        rw [hfib]
        by_cases hzc : z - s ∈ cone v ϑ
        · rw [Set.indicator_of_mem (show z ∈ {z | z - s ∈ cone v ϑ} from hzc)]
          exact mul_le_mul' le_rfl (lintegral_midBall_fibre_le hv hϑ hϑ' hα hd s z)
        · rw [Set.indicator_of_notMem (show z ∉ {z | z - s ∈ cone v ϑ} from hzc)]
          have hball0 : volume (closedBall s (0 : ℝ)) = 0 := by
            rw [volume_closedBall_eq _ le_rfl, zero_pow (Nat.ne_of_gt hd), ENNReal.ofReal_zero,
              zero_mul]
          have hnull : volume {t : EuclideanSpace ℝ (Fin d) |
              z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖} = 0 :=
            measure_mono_null
              (le_trans (fibre_subset_singleton_of_notMem_cone hv hϑ hϑ' hzc)
                (by simp)) hball0
          rw [setLIntegral_measure_zero _ _ hnull, mul_zero]
    _ = ∫⁻ z in {z | z - s ∈ cone v ϑ},
          G z * (ENNReal.ofReal (chainConst d ϑ α * ‖z - s‖ ^ (-(d : ℝ) - α)) *
            unitBallVol d) := lintegral_indicator hconeMeas _
    _ = ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
          ∫⁻ z in {z | z - s ∈ cone v ϑ},
            G z * ENNReal.ofReal (‖z - s‖ ^ (-(d : ℝ) - α)) := by
        rw [← lintegral_const_mul' _ _
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top unitBallVol_ne_top)]
        refine lintegral_congr fun z => ?_
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
  set w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ :=
    fun s => ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)) with hwdef
  have hwmeas : Measurable w := by rw [hwdef]; fun_prop
  have hgraph : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      p.2 ∈ closedBall (midCentre v ϑ p.1 t) ‖p.1 - t‖} := by
    have h1 : Continuous fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        dist p.2 (midCentre v ϑ p.1 t) := by unfold midCentre; fun_prop
    have h2 : Continuous fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ‖p.1 - t‖ := by fun_prop
    simpa [Metric.mem_closedBall] using (isClosed_le h1 h2).measurableSet
  have hstep : ∀ s, w s * ∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖, G z
      = ∫⁻ z, w s * (closedBall (midCentre v ϑ s t) ‖s - t‖).indicator G z := by
    intro s
    rw [lintegral_const_mul' _ _ (by simp [hwdef] : w s ≠ ∞),
      lintegral_indicator measurableSet_closedBall]
  have hunc : AEMeasurable (Function.uncurry fun s z =>
      w s * (closedBall (midCentre v ϑ s t) ‖s - t‖).indicator G z) volume := by
    refine Measurable.aemeasurable ?_
    have heq : (Function.uncurry fun s z =>
        w s * (closedBall (midCentre v ϑ s t) ‖s - t‖).indicator G z)
        = fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
          w p.1 * {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
            p.2 ∈ closedBall (midCentre v ϑ p.1 t) ‖p.1 - t‖}.indicator
              (fun q => G q.2) p := by
      funext p
      obtain ⟨s, z⟩ := p
      simp only [Function.uncurry]
      by_cases hp : z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖
      · rw [Set.indicator_of_mem hp,
          Set.indicator_of_mem (show (s, z) ∈ {p : EuclideanSpace ℝ (Fin d) ×
            EuclideanSpace ℝ (Fin d) | p.2 ∈ closedBall (midCentre v ϑ p.1 t) ‖p.1 - t‖}
            from hp)]
      · rw [Set.indicator_of_notMem hp,
          Set.indicator_of_notMem (show (s, z) ∉ {p : EuclideanSpace ℝ (Fin d) ×
            EuclideanSpace ℝ (Fin d) | p.2 ∈ closedBall (midCentre v ϑ p.1 t) ‖p.1 - t‖}
            from hp)]
    rw [heq]
    exact (hwmeas.comp measurable_fst).mul ((hG.comp measurable_snd).indicator hgraph)
  calc ∫⁻ s, w s * ∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖, G z
      = ∫⁻ s, ∫⁻ z, w s * (closedBall (midCentre v ϑ s t) ‖s - t‖).indicator G z :=
        lintegral_congr hstep
    _ = ∫⁻ z, ∫⁻ s, w s * (closedBall (midCentre v ϑ s t) ‖s - t‖).indicator G z :=
        lintegral_lintegral_swap hunc
    _ ≤ ∫⁻ z, {z | z - t ∈ cone v ϑ}.indicator
          (fun z => G z * (ENNReal.ofReal (chainConst' d ϑ α * ‖z - t‖ ^ (-(d : ℝ) - α)) *
            unitBallVol d)) z := by
        refine lintegral_mono fun z => ?_
        have hfibmeas : MeasurableSet {s : EuclideanSpace ℝ (Fin d) |
            z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖} := by
          have h1 : Continuous fun s : EuclideanSpace ℝ (Fin d) =>
              dist z (midCentre v ϑ s t) := by unfold midCentre; fun_prop
          have h2 : Continuous fun s : EuclideanSpace ℝ (Fin d) => ‖s - t‖ := by fun_prop
          simpa [Metric.mem_closedBall] using (isClosed_le h1 h2).measurableSet
        have hpw : ∀ s, w s * (closedBall (midCentre v ϑ s t) ‖s - t‖).indicator G z
            = {s | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖}.indicator
              (fun s => G z * w s) s := by
          intro s
          by_cases hp : z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖
          · rw [Set.indicator_of_mem hp,
              Set.indicator_of_mem (show s ∈ {s | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖}
                from hp)]
            ring
          · rw [Set.indicator_of_notMem hp,
              Set.indicator_of_notMem (show s ∉ {s | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖}
                from hp)]
            simp
        have hfib : ∫⁻ s, w s * (closedBall (midCentre v ϑ s t) ‖s - t‖).indicator G z
            = G z * ∫⁻ s in {s | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖}, w s := by
          calc ∫⁻ s, w s * (closedBall (midCentre v ϑ s t) ‖s - t‖).indicator G z
              = ∫⁻ s, {s | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖}.indicator
                  (fun s => G z * w s) s := lintegral_congr hpw
            _ = ∫⁻ s in {s | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖}, G z * w s :=
                lintegral_indicator hfibmeas _
            _ = G z * ∫⁻ s in {s | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖}, w s :=
                lintegral_const_mul _ hwmeas
        rw [hfib]
        by_cases hzc : z - t ∈ cone v ϑ
        · rw [Set.indicator_of_mem (show z ∈ {z | z - t ∈ cone v ϑ} from hzc)]
          exact mul_le_mul' le_rfl (lintegral_midBall_fibre_le' hv hϑ hϑ' hα hd t z)
        · rw [Set.indicator_of_notMem (show z ∉ {z | z - t ∈ cone v ϑ} from hzc)]
          have hball0 : volume (closedBall t (0 : ℝ)) = 0 := by
            rw [volume_closedBall_eq _ le_rfl, zero_pow (Nat.ne_of_gt hd), ENNReal.ofReal_zero,
              zero_mul]
          have hnull : volume {s : EuclideanSpace ℝ (Fin d) |
              z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖} = 0 :=
            measure_mono_null
              (le_trans (fibre_subset_singleton_of_notMem_cone' hv hϑ hϑ' hzc) (by simp)) hball0
          rw [setLIntegral_measure_zero _ _ hnull, mul_zero]
    _ = ∫⁻ z in {z | z - t ∈ cone v ϑ},
          G z * (ENNReal.ofReal (chainConst' d ϑ α * ‖z - t‖ ^ (-(d : ℝ) - α)) *
            unitBallVol d) := lintegral_indicator hconeMeas _
    _ = ENNReal.ofReal (chainConst' d ϑ α) * unitBallVol d *
          ∫⁻ z in {z | z - t ∈ cone v ϑ},
            G z * ENNReal.ofReal (‖z - t‖ ^ (-(d : ℝ) - α)) := by
        rw [← lintegral_const_mul' _ _
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top unitBallVol_ne_top)]
        refine lintegral_congr fun z => ?_
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

end QFS
