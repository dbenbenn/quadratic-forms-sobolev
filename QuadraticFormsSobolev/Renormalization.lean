/-
Section 5.2 of Bux–Kassmann–Schulze, "Renormalization: Blocks and Towns".

Lemma 5.9: at distances that are large compared to the cube size, passing from a
cone of apex angle `ϑ/2` to one of apex angle `ϑ` absorbs a whole cube at each
end.
-/
import QuadraticFormsSobolev.Section5

open Real Set Metric

namespace QFS

variable {d : ℕ}

/-- **Lemma 5.9** of Bux–Kassmann–Schulze. There is a constant `δ`, depending only
on `ϑ` and `d`, such that whenever `‖x − y‖ ≥ δ ℓ` and `y` lies in the cone of
apex angle `ϑ/2` at `x`, the whole cube `Ā_ℓ(y)` lies in the cone of apex angle
`ϑ` based at *every* point of `Ā_ℓ(x)`.

The constant proved here is `δ = (√d + 1)/sin(ϑ/2)`; the paper's
`δ = 3√d/(2 sin ϑ)` is too small — see the README. -/
theorem renormalization_apex_shrink {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ = 1 →
      ∀ ℓ : ℝ, 0 < ℓ → ∀ x y : EuclideanSpace ℝ (Fin d),
        δ * ℓ ≤ ‖x - y‖ → y ∈ shift (cone v (ϑ / 2)) x →
        closedCube ℓ y ⊆ ⋂ z ∈ closedCube ℓ x, shift (cone v ϑ) z := by
  have hs2 : 0 < Real.sin (ϑ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
  have hD : (0:ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  refine ⟨(Real.sqrt d + 1) / Real.sin (ϑ / 2), by positivity, ?_⟩
  intro v hv ℓ hℓ x y hdist hy u hu
  -- the gap of `y − x` with respect to the *wide* cone
  have hgapy : (Real.sqrt d + 1) * ℓ ≤ coneGap v ϑ (y - x) := by
    refine le_trans ?_ (coneGap_ge_of_mem_half hv hϑ hϑ' hy)
    have hnorm : (Real.sqrt d + 1) / Real.sin (ϑ / 2) * ℓ ≤ ‖y - x‖ := by
      rw [norm_sub_rev]; exact hdist
    have := mul_le_mul_of_nonneg_right hnorm (le_of_lt hs2)
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc,
      div_self (ne_of_gt hs2), mul_one] at this
    linarith [this]
  -- `u` is deep inside the wide cone at `x`
  have hux : ‖u - y‖ ≤ ℓ / 2 * Real.sqrt d := by
    have := closedCube_subset_closedBall (le_of_lt hℓ) y hu
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have hgapu : ℓ / 2 * Real.sqrt d < coneGap v ϑ (u - x) := by
    have hlip := coneGap_sub_le hv hϑ hϑ' (y - x) (u - x)
    have he : ‖y - x - (u - x)‖ = ‖u - y‖ := by
      rw [show y - x - (u - x) = -(u - y) by abel, norm_neg]
    rw [he] at hlip
    nlinarith
  have hshr : u - x ∈ shrink (cone v ϑ) (ℓ / 2 * Real.sqrt d) :=
    mem_shrink_cone_of_lt_coneGap hv hϑ hϑ' (by positivity) hgapu
  -- Lemma 2.7 (⋆): the shrunk cone lies in every translate by a small vector
  rw [shrink_eq_iInter_shift (cone v ϑ) (by positivity)] at hshr
  refine Set.mem_iInter₂.mpr (fun z hz => ?_)
  have hzx : ‖z - x‖ ≤ ℓ / 2 * Real.sqrt d := by
    have := closedCube_subset_closedBall (le_of_lt hℓ) x hz
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have hmem := Set.mem_iInter₂.mp hshr (z - x)
    (by rw [Metric.mem_closedBall, dist_zero_right]; exact hzx)
  rw [mem_shift] at hmem ⊢
  have he : u - x - (z - x) = u - z := by abel
  rwa [he] at hmem


/-! ## The paper's constant

The proof of Lemma 5.9 passes through the intermediate estimate

> if `y ∈ Ṽ[x]` and `|x − y| ≥ ℓ√d/(2 sin ϑ)`, then `B_{ℓ√d/2}(y) ⊆ V̄[x]`,

and concludes with `δ = 3√d/(2 sin ϑ)`. By `coneGap_eq_norm_mul_sin` the distance
from `y` to the boundary of `V̄[x]` is exactly `‖y − x‖ sin(ϑ − ∠(v, y−x))`, and
`y ∈ Ṽ[x]` only bounds `∠(v, y−x)` by `ϑ/2`. So at the threshold distance the
available gap can be as small as `ℓ√d sin(ϑ/2)/(2 sin ϑ)`, and the lemma below
says this is *always* less than the `ℓ√d/2` the estimate needs. -/

/-- The threshold distance used in the paper's proof of Lemma 5.9 is too small,
for every admissible apex angle: the gap it guarantees falls strictly short of
what the estimate requires. -/
theorem paper_threshold_insufficient {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    {c : ℝ} (hc : 0 < c) :
    c * Real.sin (ϑ / 2) / (2 * Real.sin ϑ) < c / 2 := by
  have hsϑ : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [pi_pos])
  have hlt : Real.sin (ϑ / 2) < Real.sin ϑ :=
    Real.strictMonoOn_sin ⟨by linarith [pi_pos], by linarith⟩
      ⟨by linarith [pi_pos], hϑ'⟩ (by linarith)
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

end QFS
