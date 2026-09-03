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


/-- A point whose gap exceeds `ρ` lies in the `ρ`-shrunk cone `Ṽ_ρ`. This is how
Lemma 5.7 produces lattice points inside the double half-cones it works with. -/
lemma mem_shrink_cone_of_lt_coneGap {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ π / 2) {p : E} {ρ : ℝ} (hρ : 0 ≤ ρ) (h : ρ < coneGap v ϑ p) :
    p ∈ shrink (cone v ϑ) ρ := by
  refine ⟨?_, closedBall_subset_cone hv hϑ hϑ' h⟩
  rw [mem_cone_iff_coneGap_pos hv hϑ hϑ']
  linarith


/-- Translating along the axis shifts the gap: `coneGap v ϑ (p − a·v) = gap p − a sin ϑ`. -/
lemma coneGap_sub_smul_axis {v : E} (hv : ‖v‖ = 1) (ϑ : ℝ) (p : E) (a : ℝ) :
    coneGap v ϑ (p - a • v) = coneGap v ϑ p - a * Real.sin ϑ := by
  have h := coneGap_add_smul_axis hv ϑ p (-a)
  rw [show p + (-a) • v = p - a • v by rw [neg_smul]; abel] at h
  rw [h]
  ring

/-- **The `ρ`-shrunk half-cone is a half-cone with a displaced apex.** The points
of gap more than `ρ` are exactly the half-cone with the same axis and angle whose
apex has been moved `ρ / sin ϑ` along the axis. -/
theorem coneGap_gt_eq_shift_cone {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ π / 2) (ρ : ℝ) :
    {p : E | ρ < coneGap v ϑ p} = shift (cone v ϑ) ((ρ / Real.sin ϑ) • v) := by
  have hs0 : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [pi_pos])
  ext p
  rw [Set.mem_ofPred_eq, mem_shift, mem_cone_iff_coneGap_pos hv hϑ hϑ',
    coneGap_sub_smul_axis hv, div_mul_cancel₀ _ (ne_of_gt hs0)]
  constructor <;> intro h <;> linarith

/-- Consequently the displaced half-cone lies inside the paper's shrunk cone
`Ṽ_ρ`. -/
theorem shift_cone_subset_shrink {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ π / 2) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    shift (cone v ϑ) ((ρ / Real.sin ϑ) • v) ⊆ shrink (cone v ϑ) ρ := by
  rw [← coneGap_gt_eq_shift_cone hv hϑ hϑ']
  intro p hp
  exact mem_shrink_cone_of_lt_coneGap hv hϑ hϑ' hρ hp


/-! ## The gap as a distance

`coneGap v ϑ h = ‖h‖ sin(ϑ − ∠(v,h))`, which is the exact distance from `h` to the
boundary of the cone. This makes the constants in Section 5.2 computable. -/

open InnerProductGeometry in
/-- The component of `h` across the axis has norm `‖h‖ sin ∠(v,h)`. -/
lemma norm_across_eq {v : E} (hv : ‖v‖ = 1) (h : E) :
    ‖across v h‖ = ‖h‖ * Real.sin (angle v h) := by
  have hin : ⟪v, h⟫ = ‖h‖ * Real.cos (angle v h) := by
    have := cos_angle_mul_norm_mul_norm v h
    rw [hv, one_mul] at this
    linarith [this]
  have hpy := norm_sq_eq_inner_sq_add hv h
  have hsc : Real.sin (angle v h) ^ 2 + Real.cos (angle v h) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  have hsq : ‖across v h‖ ^ 2 = (‖h‖ * Real.sin (angle v h)) ^ 2 := by
    rw [hin] at hpy; nlinarith
  have h2 : 0 ≤ ‖across v h‖ := norm_nonneg _
  have h3 : 0 ≤ ‖h‖ * Real.sin (angle v h) :=
    mul_nonneg (norm_nonneg _) (sin_angle_nonneg v h)
  have := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq h2, Real.sqrt_sq h3] at this

open InnerProductGeometry in
/-- **The gap is the distance to the cone boundary**: `‖h‖ sin(ϑ − ∠(v,h))`. -/
theorem coneGap_eq_norm_mul_sin {v : E} (hv : ‖v‖ = 1) (ϑ : ℝ) (h : E) :
    coneGap v ϑ h = ‖h‖ * Real.sin (ϑ - angle v h) := by
  have hin : ⟪v, h⟫ = ‖h‖ * Real.cos (angle v h) := by
    have := cos_angle_mul_norm_mul_norm v h
    rw [hv, one_mul] at this
    linarith [this]
  rw [coneGap, hin, norm_across_eq hv, Real.sin_sub]
  ring

open InnerProductGeometry in
/-- A point of the *half*-angle cone `Ṽ(v, ϑ/2)` has gap at least
`‖h‖ sin(ϑ/2)` with respect to `Ṽ(v, ϑ)` — and this is sharp, by
`coneGap_eq_norm_mul_sin`, as the angle approaches `ϑ/2`. -/
theorem coneGap_ge_of_mem_half {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ π / 2) {h : E} (hh : h ∈ cone v (ϑ / 2)) :
    ‖h‖ * Real.sin (ϑ / 2) ≤ coneGap v ϑ h := by
  rw [mem_cone_iff_angle hv (by positivity) (by linarith [pi_pos])] at hh
  obtain ⟨-, hlt⟩ := hh
  have hnn : 0 ≤ angle v h := angle_nonneg v h
  rw [coneGap_eq_norm_mul_sin hv]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg h)
  refine Real.strictMonoOn_sin.monotoneOn ⟨by linarith [pi_pos], by linarith⟩
    ⟨by linarith [pi_pos], by linarith⟩ (by linarith)


/-- Cones are invariant under positive scaling. -/
lemma smul_mem_cone {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    {t : ℝ} (ht : 0 < t) {h : E} (hh : h ∈ cone v ϑ) : t • h ∈ cone v ϑ := by
  rw [mem_cone_iff_coneGap_pos hv hϑ hϑ'] at hh ⊢
  rw [coneGap_smul v ϑ ht.le]
  positivity

/-- A double cone does not depend on the sign of its axis. -/
lemma doubleCone_neg (v : E) (ϑ : ℝ) : doubleCone (-v) ϑ = doubleCone v ϑ := by
  rw [doubleCone, doubleCone, cone_neg, Set.union_comm]
  congr 1
  simp

end QFS
