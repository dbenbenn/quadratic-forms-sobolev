/-
The signed distance to the boundary of a cone.

For a unit axis `v` and apex angle `ϑ`, write `a = ⟪v,p⟫` and `b = ‖p − a·v‖` for
the components of `p` along and across the axis. Then

  `coneGap v ϑ p = a sin ϑ − b cos ϑ`

is positive exactly on the cone `Ṽ(v, ϑ)`, is `1`-Lipschitz in `p`, and is
positively homogeneous. Consequently a ball of radius `ρ < coneGap v ϑ p` about
`p` lies inside the cone — the quantitative fact used throughout Sections 4 and
5, of which `mem_cone_of_norm_sub_lt` is the special case `p = t·v`.
-/
import QuadraticFormsSobolev.Defs

open Real Set Metric
open RealInnerProductSpace

namespace QFS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The component of `p` across the axis `v`. -/
noncomputable def across (v p : E) : E := p - ⟪v, p⟫ • v

/-- The signed distance from `p` to the boundary of the cone `Ṽ(v, ϑ)`. -/
noncomputable def coneGap (v : E) (ϑ : ℝ) (p : E) : ℝ :=
  ⟪v, p⟫ * Real.sin ϑ - ‖across v p‖ * Real.cos ϑ

lemma across_sub (v p q : E) : across v (p - q) = across v p - across v q := by
  simp only [across, inner_sub_right, sub_smul]
  abel

/-- Pythagoras for the decomposition along and across a unit axis. -/
lemma norm_sq_eq_inner_sq_add {v : E} (hv : ‖v‖ = 1) (p : E) :
    ‖p‖ ^ 2 = ⟪v, p⟫ ^ 2 + ‖across v p‖ ^ 2 := by
  have hexp : ‖across v p‖ ^ 2
      = ‖p‖ ^ 2 - 2 * (⟪v, p⟫ * ⟪p, v⟫) + ⟪v, p⟫ ^ 2 * ‖v‖ ^ 2 := by
    rw [across, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
  rw [hexp, hv, real_inner_comm p v]
  ring

/-- Membership in a cone is exactly positivity of the gap. -/
theorem mem_cone_iff_coneGap_pos {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ π / 2) (p : E) : p ∈ cone v ϑ ↔ 0 < coneGap v ϑ p := by
  have hs0 : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [pi_pos])
  have hc0 : 0 ≤ Real.cos ϑ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hϑ'⟩
  have hsc : Real.sin ϑ ^ 2 + Real.cos ϑ ^ 2 = 1 := Real.sin_sq_add_cos_sq ϑ
  have hpy := norm_sq_eq_inner_sq_add hv p
  have hbn : 0 ≤ ‖across v p‖ := norm_nonneg _
  have hpn : 0 ≤ ‖p‖ := norm_nonneg _
  rw [mem_cone_iff_mul, coneGap]
  constructor
  · rintro ⟨-, hlt⟩
    have ha : 0 < ⟪v, p⟫ := lt_of_le_of_lt (mul_nonneg hc0 hpn) hlt
    have hsq : (Real.cos ϑ * ‖p‖) ^ 2 < ⟪v, p⟫ ^ 2 := by
      have h0 : 0 ≤ Real.cos ϑ * ‖p‖ := mul_nonneg hc0 hpn
      nlinarith
    have h2 : (‖across v p‖ * Real.cos ϑ) ^ 2 < (⟪v, p⟫ * Real.sin ϑ) ^ 2 := by nlinarith
    have h3 : ‖across v p‖ * Real.cos ϑ < ⟪v, p⟫ * Real.sin ϑ :=
      lt_of_pow_lt_pow_left₀ 2 (le_of_lt (mul_pos ha hs0)) h2
    linarith
  · intro hgap
    have hbc : 0 ≤ ‖across v p‖ * Real.cos ϑ := mul_nonneg hbn hc0
    have ha : 0 < ⟪v, p⟫ := by nlinarith
    have hne : p ≠ 0 := by
      intro hz
      rw [hz] at ha
      simp at ha
    refine ⟨hne, ?_⟩
    have h2 : (‖across v p‖ * Real.cos ϑ) ^ 2 < (⟪v, p⟫ * Real.sin ϑ) ^ 2 := by nlinarith
    have hsq : (Real.cos ϑ * ‖p‖) ^ 2 < ⟪v, p⟫ ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (le_of_lt ha) hsq

/-- The gap is `1`-Lipschitz. -/
theorem coneGap_sub_le {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    (p q : E) : coneGap v ϑ p - coneGap v ϑ q ≤ ‖p - q‖ := by
  have hs0 : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [pi_pos])
  have hc0 : 0 ≤ Real.cos ϑ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hϑ'⟩
  have hsc : Real.sin ϑ ^ 2 + Real.cos ϑ ^ 2 = 1 := Real.sin_sq_add_cos_sq ϑ
  set w := p - q with hw
  have hA : ⟪v, p⟫ - ⟪v, q⟫ = ⟪v, w⟫ := by rw [hw, inner_sub_right]
  have h1 : across v w = across v p - across v q := by rw [hw, across_sub]
  have hBle : ‖across v q‖ - ‖across v p‖ ≤ ‖across v w‖ := by
    have h2 : ‖across v q‖ - ‖across v p‖ ≤ |‖across v p‖ - ‖across v q‖| := by
      rw [abs_sub_comm]; exact le_abs_self _
    refine h2.trans ?_
    rw [h1]
    exact abs_norm_sub_norm_le _ _
  have hpy : ‖w‖ ^ 2 = ⟪v, w⟫ ^ 2 + ‖across v w‖ ^ 2 := norm_sq_eq_inner_sq_add hv w
  have hkey : |⟪v, w⟫| * Real.sin ϑ + ‖across v w‖ * Real.cos ϑ ≤ ‖w‖ := by
    have hnn : 0 ≤ |⟪v, w⟫| * Real.sin ϑ + ‖across v w‖ * Real.cos ϑ := by positivity
    have habs : |⟪v, w⟫| ^ 2 = ⟪v, w⟫ ^ 2 := sq_abs _
    have hsq : (|⟪v, w⟫| * Real.sin ϑ + ‖across v w‖ * Real.cos ϑ) ^ 2 ≤ ‖w‖ ^ 2 := by
      nlinarith [sq_nonneg (|⟪v, w⟫| * Real.cos ϑ - ‖across v w‖ * Real.sin ϑ)]
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [norm_nonneg w]
  have hAle : ⟪v, w⟫ ≤ |⟪v, w⟫| := le_abs_self _
  have hexp : coneGap v ϑ p - coneGap v ϑ q
      = ⟪v, w⟫ * Real.sin ϑ + (‖across v q‖ - ‖across v p‖) * Real.cos ϑ := by
    rw [coneGap, coneGap, ← hA]; ring
  rw [hexp]
  nlinarith [hAle, hBle, hkey]

/-- A ball of radius less than the gap lies inside the cone. -/
theorem closedBall_subset_cone {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    {p : E} {ρ : ℝ} (hρ : ρ < coneGap v ϑ p) : closedBall p ρ ⊆ cone v ϑ := by
  intro u hu
  rw [Metric.mem_closedBall, dist_eq_norm] at hu
  rw [mem_cone_iff_coneGap_pos hv hϑ hϑ' u]
  have h := coneGap_sub_le hv hϑ hϑ' p u
  have h2 : ‖p - u‖ = ‖u - p‖ := norm_sub_rev _ _
  linarith

/-- The gap is positively homogeneous. -/
lemma coneGap_smul (v : E) (ϑ : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) (p : E) :
    coneGap v ϑ (lam • p) = lam * coneGap v ϑ p := by
  have hacross : across v (lam • p) = lam • across v p := by
    simp only [across, real_inner_smul_right, smul_sub, smul_smul]
  rw [coneGap, coneGap, hacross, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hlam]
  ring

@[simp] lemma coneGap_zero (v : E) (ϑ : ℝ) : coneGap v ϑ (0 : E) = 0 := by
  simp [coneGap, across]

/-- The gap never exceeds the norm. -/
lemma coneGap_le_norm {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) (p : E) :
    coneGap v ϑ p ≤ ‖p‖ := by
  have h := coneGap_sub_le hv hϑ hϑ' p 0
  rw [coneGap_zero, sub_zero, sub_zero] at h
  exact h


/-- Moving along the axis raises the gap by exactly `a sin ϑ`; the component
across the axis is unchanged. This is the mechanism behind Lemma 5.6. -/
lemma coneGap_add_smul_axis {v : E} (hv : ‖v‖ = 1) (ϑ : ℝ) (q : E) (a : ℝ) :
    coneGap v ϑ (q + a • v) = coneGap v ϑ q + a * Real.sin ϑ := by
  have hin : ⟪v, q + a • v⟫ = ⟪v, q⟫ + a := by
    rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hv]
    ring
  have hac : across v (q + a • v) = across v q := by
    rw [across, across, hin, add_smul]
    abel
  rw [coneGap, coneGap, hin, hac]
  ring

/-- Consistency check: on the axis the gap is `t sin ϑ`, so
`closedBall_subset_cone` specialises to `mem_cone_of_norm_sub_lt`. -/
lemma coneGap_smul_axis {v : E} (hv : ‖v‖ = 1) (ϑ : ℝ) (t : ℝ) :
    coneGap v ϑ (t • v) = t * Real.sin ϑ := by
  have h := coneGap_add_smul_axis hv ϑ 0 t
  rw [zero_add, coneGap_zero, zero_add] at h
  exact h

/-- Replacing the axis by its negative reflects the cone. -/
lemma cone_neg (v : E) (ϑ : ℝ) : cone (-v) ϑ = -(cone v ϑ) := by
  ext h
  simp only [cone, Set.mem_neg, Set.mem_ofPred_eq, inner_neg_left, inner_neg_right, norm_neg,
    neg_div, neg_ne_zero]

end QFS
