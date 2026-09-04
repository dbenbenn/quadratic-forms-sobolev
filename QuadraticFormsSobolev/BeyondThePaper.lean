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

open Metric Set
open scoped Real InnerProductSpace

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

end QFS
