/-
Section 3.1 of Bux–Kassmann–Schulze: the discrete version of the kernel.

For a kernel `k` on `ℝ^d × ℝ^d` and `h > 0` the paper sets

  `ω^k_h(x, y) = h^{-2d} ∫∫_{A_h(x) × A_h(y)} k(s, t) d(s,t)`,

a kernel on `hℤ^d`, and Proposition 3.5 checks that it satisfies assumption
(1.7). The upper bound is "just a consequence of Lemma 3.4": on the product of
the two cubes `|s − t|` is bounded below by `|x − y|/(2√d)`, so the kernel is
bounded above by `(2√d)^{d+α}` times its value at `(x, y)`.
-/
import QuadraticFormsSobolev.Section1
import QuadraticFormsSobolev.ThinCones

open Real Set Metric MeasureTheory ENNReal

namespace QFS

variable {d : ℕ}

/-- The **discrete kernel** `ω^k_h` of Section 3.1. -/
noncomputable def discreteKernel (d : ℕ)
    (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (h : ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ENNReal.ofReal ((h ^ (2 * d))⁻¹) * ∫⁻ p in cube h x ×ˢ cube h y, k p.1 p.2

lemma volume_cube_prod {h : ℝ} (hh : 0 < h) (x y : EuclideanSpace ℝ (Fin d)) :
    volume (cube h x ×ˢ cube h y) = ENNReal.ofReal (h ^ d) * ENNReal.ofReal (h ^ d) := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, volume_cube hh, volume_cube hh]

lemma ofReal_inv_pow_mul {h : ℝ} (hh : 0 < h) :
    ENNReal.ofReal ((h ^ (2 * d))⁻¹) *
      (ENNReal.ofReal (h ^ d) * ENNReal.ofReal (h ^ d)) = 1 := by
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  rw [show (h ^ (2 * d))⁻¹ * (h ^ d * h ^ d) = 1 by
    rw [two_mul, pow_add]
    field_simp]
  exact ENNReal.ofReal_one

/-- **The upper bound of Proposition 3.5 / Corollary 3.6 (ii)**, which the paper
calls "just a consequence of Lemma 3.4". -/
theorem discreteKernel_le {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {α Λ : ℝ}
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (hα : 0 < α) {h : ℝ} (hh : 0 < h)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ scaledLattice d h)
    (hy : y ∈ scaledLattice d h) (hxy : Real.sqrt d * h < ‖x - y‖) :
    discreteKernel d k h x y
      ≤ ENNReal.ofReal (Λ * (2 * Real.sqrt d) ^ ((d:ℝ) + α)) * jumpKernel d α x y := by
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exfalso
      have h0 : ‖x - y‖ = 0 := by simp [EuclideanSpace.norm_eq]
      rw [h0] at hxy
      simp at hxy
    · exact hd
  have hsd : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hxy0 : (0:ℝ) < ‖x - y‖ := lt_trans (by positivity) hxy
  have hexp : (-(d:ℝ) - α) ≤ 0 := by
    have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    linarith
  have hΛ0 : (0:ℝ) < Λ := lt_of_lt_of_le zero_lt_one hk.one_le
  -- the pointwise bound on the product of the cubes
  have hpt : ∀ p ∈ cube h x ×ˢ cube h y,
      k p.1 p.2 ≤ ENNReal.ofReal (Λ * (2 * Real.sqrt d) ^ ((d:ℝ) + α)) * jumpKernel d α x y := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    obtain ⟨hlow, -⟩ := lemma_cubes hh hx hy hxy hs ht
    have hst0 : (0:ℝ) < ‖s - t‖ := lt_trans (by positivity) hlow
    have hkey : ‖s - t‖ ^ (-(d:ℝ) - α)
        ≤ (2 * Real.sqrt d) ^ ((d:ℝ) + α) * ‖x - y‖ ^ (-(d:ℝ) - α) := by
      have hle : ‖x - y‖ / (2 * Real.sqrt d) ≤ ‖s - t‖ := by
        have h1 : (1 / (2 * Real.sqrt d) * ‖x - y‖) * (2 * Real.sqrt d)
            < ‖s - t‖ * (2 * Real.sqrt d) := mul_lt_mul_of_pos_right hlow (by positivity)
        have h2 : (1 / (2 * Real.sqrt d) * ‖x - y‖) * (2 * Real.sqrt d) = ‖x - y‖ := by
          field_simp
        rw [div_le_iff₀ (by positivity)]
        linarith [h1, h2.le, h2.ge]
      have h1 := Real.rpow_le_rpow_of_nonpos (by positivity) hle hexp
      have h2 : (‖x - y‖ / (2 * Real.sqrt d)) ^ (-(d:ℝ) - α)
          = (2 * Real.sqrt d) ^ ((d:ℝ) + α) * ‖x - y‖ ^ (-(d:ℝ) - α) := by
        rw [Real.div_rpow (norm_nonneg _) (by positivity)]
        have hneg : (-(d:ℝ) - α) = -((d:ℝ) + α) := by ring
        rw [hneg, Real.rpow_neg (by positivity : (0:ℝ) ≤ 2 * Real.sqrt d)]
        field_simp
      linarith [h1, h2.le, h2.ge]
    calc k s t ≤ ENNReal.ofReal Λ * jumpKernel d α s t := hk.upper s t
      _ ≤ ENNReal.ofReal Λ *
            ENNReal.ofReal ((2 * Real.sqrt d) ^ ((d:ℝ) + α) * ‖x - y‖ ^ (-(d:ℝ) - α)) :=
          mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hkey)
      _ = ENNReal.ofReal (Λ * (2 * Real.sqrt d) ^ ((d:ℝ) + α)) * jumpKernel d α x y := by
          rw [jumpKernel, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul hΛ0.le, mul_assoc]
  -- integrate
  calc discreteKernel d k h x y
      ≤ ENNReal.ofReal ((h ^ (2 * d))⁻¹) *
          ∫⁻ _ in cube h x ×ˢ cube h y,
            ENNReal.ofReal (Λ * (2 * Real.sqrt d) ^ ((d:ℝ) + α)) * jumpKernel d α x y := by
        refine mul_le_mul' le_rfl (lintegral_mono_ae ?_)
        exact ae_restrict_of_forall_mem
          ((measurableSet_cube hh x).prod (measurableSet_cube hh y)) hpt
    _ = ENNReal.ofReal (Λ * (2 * Real.sqrt d) ^ ((d:ℝ) + α)) * jumpKernel d α x y := by
        rw [setLIntegral_const, volume_cube_prod hh]
        rw [show ENNReal.ofReal ((h ^ (2 * d))⁻¹) *
            (ENNReal.ofReal (Λ * (2 * Real.sqrt d) ^ ((d:ℝ) + α)) * jumpKernel d α x y *
              (ENNReal.ofReal (h ^ d) * ENNReal.ofReal (h ^ d)))
          = (ENNReal.ofReal ((h ^ (2 * d))⁻¹) *
              (ENNReal.ofReal (h ^ d) * ENNReal.ofReal (h ^ d))) *
            (ENNReal.ofReal (Λ * (2 * Real.sqrt d) ^ ((d:ℝ) + α)) * jumpKernel d α x y) by
          ring]
        rw [ofReal_inv_pow_mul hh, one_mul]

end QFS
