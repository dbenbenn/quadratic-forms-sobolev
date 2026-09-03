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

/-! ## Towards the lower bound of Proposition 3.5 -/

/-- Every point has a `h`-favoured index. -/
theorem exists_isFavoured {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {θ : ℝ}
    (F : RefFamily Γ θ) (h : ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    ∃ v, IsFavoured F h u v := by
  obtain ⟨w₀, hw₀, -⟩ := F.covers 0
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image F.axes
    (fun w => volume (cubeCone Γ (F.cone w) h u)) ⟨w₀, hw₀⟩
  exact ⟨v, hv, hmax⟩

lemma indE_eq_ofReal_ind (S : Set (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) :
    indE S x = ENNReal.ofReal (ind S x) := by
  by_cases hx : x ∈ S
  · rw [indE, Set.indicator_of_mem hx, ind_of_mem hx, ENNReal.ofReal_one]
  · rw [indE, Set.indicator_of_notMem hx, ind, Set.indicator_of_notMem hx,
      ENNReal.ofReal_zero]

lemma indE_le_indE {S T : Set (EuclideanSpace ℝ (Fin d))}
    {x y : EuclideanSpace ℝ (Fin d)} (h : x ∈ S → y ∈ T) :
    indE S x ≤ indE T y := by
  by_cases hx : x ∈ S
  · rw [indE, Set.indicator_of_mem hx, indE, Set.indicator_of_mem (h hx)]
  · rw [indE, Set.indicator_of_notMem hx]
    exact zero_le

/-- **Lemma 3.2** in `ℝ≥0∞`, which is where the integrand lives. -/
theorem lemma_min_dist_E {V W : Set (EuclideanSpace ℝ (Fin d))}
    {x y s t : EuclideanSpace ℝ (Fin d)} (hs : s ∈ cube 1 x) (ht : t ∈ cube 1 y) :
    indE (shift (shrink V (Real.sqrt d)) x) y + indE (shift (shrink W (Real.sqrt d)) y) x
      ≤ indE (shift (shrink V (Real.sqrt d / 2)) x) t
        + indE (shift (shrink W (Real.sqrt d / 2)) y) s := by
  refine add_le_add (indE_le_indE (fun hy => ?_)) (indE_le_indE (fun hx => ?_))
  · exact cube_subset_of_mem_shift_shrink hy ht
  · exact cube_subset_of_mem_shift_shrink hx hs

/-- **The pointwise estimate of Proposition 3.5.** On the product of the two
favoured sub-cubes the integrand of `ω^k_1` is at least a constant: `Λ⁻¹` times
the bracket of Lemma 3.2 at `(x, y)` times `(2√d)^{-d-α}|x − y|^{-d-α}`.

The three inputs are the paper's: Lemma 2.7 pushes the shrunk reference cone at
`x` inside the cone at `s`, Lemma 3.2 replaces the indicators at `(s, t)` by the
ones at `(x, y)`, and Lemma 3.4 bounds `|s − t|` by `2√d|x − y|`. -/
theorem discreteKernel_integrand_ge {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {α Λ : ℝ} {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (hα : 0 < α) {θ : ℝ} (F : RefFamily Γ θ)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ lattice d) (hy : y ∈ lattice d)
    (hxy : Real.sqrt d < ‖x - y‖) {m n : EuclideanSpace ℝ (Fin d)}
    {s t : EuclideanSpace ℝ (Fin d)} (hs : s ∈ cubeCone Γ (F.cone m) 1 x)
    (ht : t ∈ cubeCone Γ (F.cone n) 1 y) :
    ENNReal.ofReal Λ⁻¹ *
        ((indE (F.shrunkAt m (Real.sqrt d) x) y + indE (F.shrunkAt n (Real.sqrt d) y) x)
          * ENNReal.ofReal ((2 * Real.sqrt d) ^ (-(d:ℝ) - α) * ‖x - y‖ ^ (-(d:ℝ) - α)))
      ≤ k s t := by
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exfalso
      have h0 : ‖x - y‖ = 0 := by simp [EuclideanSpace.norm_eq]
      rw [h0] at hxy
      simp at hxy
    · exact hd
  have hsd : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hxy0 : (0:ℝ) < ‖x - y‖ := lt_trans hsd hxy
  have hexp : (-(d:ℝ) - α) ≤ 0 := by
    have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    linarith
  have hs1 : s ∈ cube 1 x := hs.1
  have ht1 : t ∈ cube 1 y := ht.1
  -- Lemma 2.7: the shrunk reference cone at `x` sits inside the cone at `s`
  have hpush : ∀ {V : Set (EuclideanSpace ℝ (Fin d))} {u ξ : EuclideanSpace ℝ (Fin d)},
      ξ ∈ cube 1 u → shift (shrink V (Real.sqrt d / 2)) u ⊆ shift V ξ := by
    intro V u ξ hξ
    have h := (cone_in_intersection V (by norm_num : (0:ℝ) ≤ 1) u hξ).2
    rwa [show (1:ℝ) / 2 * Real.sqrt d = Real.sqrt d / 2 by ring] at h
  have hbr1 : indE (shift (shrink (F.cone m) (Real.sqrt d / 2)) x) t
      ≤ indE (coneAt Γ s) t := by
    refine indE_le_indE (fun hmem => ?_)
    rw [mem_coneAt]
    exact hs.2 (hpush hs1 hmem)
  have hbr2 : indE (shift (shrink (F.cone n) (Real.sqrt d / 2)) y) s
      ≤ indE (coneAt Γ t) s := by
    refine indE_le_indE (fun hmem => ?_)
    rw [mem_coneAt]
    exact ht.2 (hpush ht1 hmem)
  -- Lemma 3.4: the kernel at `(s, t)` dominates the constant
  have hker : ENNReal.ofReal ((2 * Real.sqrt d) ^ (-(d:ℝ) - α) * ‖x - y‖ ^ (-(d:ℝ) - α))
      ≤ jumpKernel d α s t := by
    obtain ⟨hlow, hup⟩ := lemma_cubes (h := 1) one_pos hx hy
      (by rw [mul_one]; exact hxy) hs1 ht1
    have hst0 : (0:ℝ) < ‖s - t‖ := lt_trans (by positivity) hlow
    have h1 : ‖s - t‖ ^ (-(d:ℝ) - α) ≥ (2 * Real.sqrt d * ‖x - y‖) ^ (-(d:ℝ) - α) :=
      Real.rpow_le_rpow_of_nonpos hst0 hup.le hexp
    have h2 : (2 * Real.sqrt d * ‖x - y‖) ^ (-(d:ℝ) - α)
        = (2 * Real.sqrt d) ^ (-(d:ℝ) - α) * ‖x - y‖ ^ (-(d:ℝ) - α) :=
      Real.mul_rpow (by positivity) (norm_nonneg _)
    rw [jumpKernel]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith [h1, h2.le, h2.ge]
  -- assemble
  refine le_trans (mul_le_mul' le_rfl (mul_le_mul' ?_ hker)) (hk.lower s t)
  exact le_trans (lemma_min_dist_E hs1 ht1) (add_le_add hbr1 hbr2)

/-! ## Integrating the estimate

The integration needs the sets `A_h^m(u)` to be measurable, i.e. the sets
`{x | V ⊆ Γ(x)}` to be measurable. The paper obtains this from condition (M) by
quoting Debreu's measurable-selection theorem; that implication is not
formalised here, so it is carried as an explicit hypothesis. -/

/-- What the paper draws from condition (M) via [Debreu67, Thm. 4.4]: for every
double cone `V`, the set of points whose cone contains `V` is measurable. -/
def CondMeas (Γ : Configuration (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ V : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet {x | V ⊆ (Γ x).carrier}

lemma measurableSet_cubeCone {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    (hm : CondMeas Γ) (V : Set (EuclideanSpace ℝ (Fin d))) {h : ℝ} (hh : 0 < h)
    (u : EuclideanSpace ℝ (Fin d)) : MeasurableSet (cubeCone Γ V h u) :=
  (measurableSet_cube hh u).inter (hm V)

/-- **The lower bound of Proposition 3.5**, before the constants are collected:
integrating the pointwise estimate over the two favoured sub-cubes. -/
theorem discreteKernel_ge_volume {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {α Λ : ℝ} {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (hα : 0 < α) {θ : ℝ} (F : RefFamily Γ θ)
    (hmeas : CondMeas Γ) {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ lattice d)
    (hy : y ∈ lattice d) (hxy : Real.sqrt d < ‖x - y‖)
    (m n : EuclideanSpace ℝ (Fin d)) :
    ENNReal.ofReal Λ⁻¹ *
        ((indE (F.shrunkAt m (Real.sqrt d) x) y + indE (F.shrunkAt n (Real.sqrt d) y) x)
          * ENNReal.ofReal ((2 * Real.sqrt d) ^ (-(d:ℝ) - α) * ‖x - y‖ ^ (-(d:ℝ) - α)))
        * (volume (cubeCone Γ (F.cone m) 1 x) * volume (cubeCone Γ (F.cone n) 1 y))
      ≤ discreteKernel d k 1 x y := by
  have hsub : cubeCone Γ (F.cone m) 1 x ×ˢ cubeCone Γ (F.cone n) 1 y
      ⊆ cube 1 x ×ˢ cube 1 y :=
    Set.prod_mono (cubeCone_subset_cube _ _ _ _) (cubeCone_subset_cube _ _ _ _)
  have hpre : discreteKernel d k 1 x y = ∫⁻ p in cube 1 x ×ˢ cube 1 y, k p.1 p.2 := by
    rw [discreteKernel, one_pow, inv_one, ENNReal.ofReal_one, one_mul]
  rw [hpre]
  calc ENNReal.ofReal Λ⁻¹ *
        ((indE (F.shrunkAt m (Real.sqrt d) x) y + indE (F.shrunkAt n (Real.sqrt d) y) x)
          * ENNReal.ofReal ((2 * Real.sqrt d) ^ (-(d:ℝ) - α) * ‖x - y‖ ^ (-(d:ℝ) - α)))
        * (volume (cubeCone Γ (F.cone m) 1 x) * volume (cubeCone Γ (F.cone n) 1 y))
      = ∫⁻ _ in cubeCone Γ (F.cone m) 1 x ×ˢ cubeCone Γ (F.cone n) 1 y,
          ENNReal.ofReal Λ⁻¹ *
            ((indE (F.shrunkAt m (Real.sqrt d) x) y
              + indE (F.shrunkAt n (Real.sqrt d) y) x)
              * ENNReal.ofReal ((2 * Real.sqrt d) ^ (-(d:ℝ) - α)
                * ‖x - y‖ ^ (-(d:ℝ) - α))) := by
        rw [setLIntegral_const, Measure.volume_eq_prod, Measure.prod_prod]
    _ ≤ ∫⁻ p in cubeCone Γ (F.cone m) 1 x ×ˢ cubeCone Γ (F.cone n) 1 y, k p.1 p.2 := by
        refine lintegral_mono_ae (ae_restrict_of_forall_mem
          ((measurableSet_cubeCone hmeas _ one_pos x).prod
            (measurableSet_cubeCone hmeas _ one_pos y)) ?_)
        rintro ⟨s, t⟩ ⟨hs, ht⟩
        exact discreteKernel_integrand_ge hk hα F hx hy hxy hs ht
    _ ≤ ∫⁻ p in cube 1 x ×ˢ cube 1 y, k p.1 p.2 :=
        lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl

end QFS
