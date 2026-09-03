/-
A quantitative geometric fact about cones, used implicitly throughout Sections 4
and 5 of Bux–Kassmann–Schulze: a ball of radius `ℓ` about the point `t·v` on the
axis lies inside the cone `Ṽ(v, ϑ)` as soon as `ℓ < t sin ϑ`.

From it we get that two translates `V[x]`, `V[y]` of one double cone always
intersect (used in Lemma 4.3), and the constant `λ` of the observation opening
the proof of Theorem 4.1.
-/
import QuadraticFormsSobolev.Defs
import QuadraticFormsSobolev.ConeGap

open Real Set Metric
open RealInnerProductSpace

namespace QFS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A point at distance less than `t sin ϑ` from `t • v` lies in the cone
`Ṽ(v, ϑ)`. Geometrically: `dist (t • v) (∂ Ṽ(v,ϑ)) = t sin ϑ`. -/
theorem mem_cone_of_norm_sub_lt {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ π / 2) {t : ℝ} (ht : 0 < t) {u : E}
    (hu : ‖u - t • v‖ < t * Real.sin ϑ) : u ∈ cone v ϑ := by
  set w : E := u - t • v with hwdef
  have hus : u = t • v + w := by rw [hwdef]; abel
  have hs0 : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [pi_pos])
  have hs1 : Real.sin ϑ ≤ 1 := Real.sin_le_one ϑ
  have hc0 : 0 ≤ Real.cos ϑ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hϑ'⟩
  have hsc : Real.sin ϑ ^ 2 + Real.cos ϑ ^ 2 = 1 := Real.sin_sq_add_cos_sq ϑ
  have hwn : 0 ≤ ‖w‖ := norm_nonneg _
  -- Cauchy–Schwarz for the axis component of `w`.
  have hcs : |⟪v, w⟫| ≤ ‖w‖ := by
    have h := abs_real_inner_le_norm v w
    rwa [hv, one_mul] at h
  have hinner : ⟪v, u⟫ = t + ⟪v, w⟫ := by
    rw [hus, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hv]
    ring
  have hnormsq : ‖u‖ ^ 2 = t ^ 2 + 2 * t * ⟪v, w⟫ + ‖w‖ ^ 2 := by
    rw [hus, norm_add_sq_real, real_inner_smul_left, norm_smul, hv, Real.norm_eq_abs,
      abs_of_pos ht]
    ring
  -- `t + ⟪v,w⟫ > 0`, since `‖w‖ < t sin ϑ ≤ t`.
  have hwt : ‖w‖ < t := lt_of_lt_of_le hu (by nlinarith)
  have htpos : 0 < t + ⟪v, w⟫ := by
    have := (abs_le.mp hcs).1
    linarith
  have hun : 0 < ‖u‖ := by
    rcases eq_or_lt_of_le (norm_nonneg u) with h | h
    · exfalso
      have hu0 : u = 0 := by simpa [eq_comm] using norm_eq_zero.mp h.symm
      rw [hu0] at hinner
      simp at hinner
      linarith
    · exact h
  refine ⟨fun hc => by rw [hc] at hun; simp at hun, ?_⟩
  rw [lt_div_iff₀ hun, hinner]
  -- Reduce to a comparison of squares.
  have hsq : (Real.cos ϑ * ‖u‖) ^ 2 < (t + ⟪v, w⟫) ^ 2 := by
    have hw2 : ‖w‖ ^ 2 < t ^ 2 * Real.sin ϑ ^ 2 := by nlinarith
    have hexp : (t + ⟪v, w⟫) ^ 2 - (Real.cos ϑ * ‖u‖) ^ 2
        = (t * Real.sin ϑ ^ 2 + ⟪v, w⟫) ^ 2
          + Real.cos ϑ ^ 2 * (t ^ 2 * Real.sin ϑ ^ 2 - ‖w‖ ^ 2) := by
      rw [mul_pow, hnormsq]; nlinarith [hsc]
    rcases eq_or_lt_of_le hc0 with hc | hc
    · -- `cos ϑ = 0`, so `sin ϑ = 1`.
      have hs : Real.sin ϑ ^ 2 = 1 := by nlinarith
      nlinarith [hexp, sq_nonneg (t * Real.sin ϑ ^ 2 + ⟪v, w⟫)]
    · nlinarith [hexp, sq_nonneg (t * Real.sin ϑ ^ 2 + ⟪v, w⟫), mul_pos (mul_pos hc hc)
        (sub_pos.mpr hw2)]
  exact lt_of_pow_lt_pow_left₀ 2 htpos.le hsq

/-- The point `t • v` lies in the cone about `v`, for every `t > 0`. -/
lemma smul_axis_mem_cone {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    {t : ℝ} (ht : 0 < t) : t • v ∈ cone v ϑ := by
  refine mem_cone_of_norm_sub_lt hv hϑ hϑ' ht ?_
  simp only [sub_self, norm_zero]
  exact mul_pos ht (Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [pi_pos]))

/-- Two translates of one double cone always meet: for any `x, y`, the cones
`V[x]` and `V[y]` have a common point. This is the geometric input to
Lemma 4.3. -/
theorem shift_inter_shift_nonempty (V : DCone E) (x y : E) :
    (shift V.carrier x ∩ shift V.carrier y).Nonempty := by
  set v := V.axis
  set ϑ := V.apex
  have hv : ‖v‖ = 1 := V.norm_axis
  have hϑ : 0 < ϑ := V.apex_pos
  have hϑ' : ϑ ≤ π / 2 := V.apex_le
  have hs0 : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [pi_pos])
  -- Choose `t` large enough that a ball of radius `‖y - x‖` about `t • v` fits in the cone.
  obtain ⟨t, ht0, ht⟩ : ∃ t : ℝ, 0 < t ∧ ‖y - x‖ < t * Real.sin ϑ := by
    refine ⟨(‖y - x‖ + 1) / Real.sin ϑ, by positivity, ?_⟩
    rw [div_mul_cancel₀ _ (ne_of_gt hs0)]
    linarith
  refine ⟨x + t • v, ?_, ?_⟩
  · have : x + t • v - x = t • v := by abel
    rw [mem_shift, this]
    exact Or.inl (smul_axis_mem_cone hv hϑ hϑ' ht0)
  · have he : x + t • v - y = t • v + (x - y) := by abel
    rw [mem_shift, he]
    refine Or.inl (mem_cone_of_norm_sub_lt hv hϑ hϑ' ht0 ?_)
    have : t • v + (x - y) - t • v = x - y := by abel
    rw [this, norm_sub_rev]
    exact ht

end QFS
