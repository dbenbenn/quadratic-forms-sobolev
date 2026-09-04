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
        ∫⁻ z, G z * ENNReal.ofReal (‖z - s‖ ^ (-(d : ℝ) - α)) := by
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
    _ ≤ ∫⁻ z, G z * (ENNReal.ofReal (chainConst d ϑ α * ‖z - s‖ ^ (-(d : ℝ) - α)) *
          unitBallVol d) := by
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
        exact mul_le_mul' le_rfl (lintegral_midBall_fibre_le hv hϑ hϑ' hα hd s z)
    _ = ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
          ∫⁻ z, G z * ENNReal.ofReal (‖z - s‖ ^ (-(d : ℝ) - α)) := by
        rw [← lintegral_const_mul' _ _
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top unitBallVol_ne_top)]
        refine lintegral_congr fun z => ?_
        rw [ENNReal.ofReal_mul hcc]
        ring

end QFS
