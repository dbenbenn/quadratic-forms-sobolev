/-
Section 3.1 of Bux–Kassmann–Schulze: the discrete version of the kernel.

For a kernel `k` on `ℝ^d × ℝ^d` and `h > 0` the paper sets

  `ω^k_h(x, y) = h^{-2d} ∫∫_{A_h(x) × A_h(y)} k(s, t) d(s,t)`,

a kernel on `hℤ^d`, and Proposition 3.5 checks that it satisfies assumption
(4). The upper bound is "just a consequence of Lemma 3.4": on the product of
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

/-- The upper bound with an `α`-free constant, which is what the paper's remark
that "for `0 < α₀ ≤ α < 2` the constant depends on `α₀` but not on `α`" needs. -/
theorem discreteKernel_le' {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {α Λ : ℝ}
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (hα : 0 < α) (hα2 : α ≤ 2) {h : ℝ} (hh : 0 < h)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ scaledLattice d h)
    (hy : y ∈ scaledLattice d h) (hxy : Real.sqrt d * h < ‖x - y‖) :
    discreteKernel d k h x y
      ≤ ENNReal.ofReal (Λ * (2 * Real.sqrt d) ^ ((d:ℝ) + 2)) * jumpKernel d α x y := by
  refine le_trans (discreteKernel_le hk hα hh hx hy hxy) (mul_le_mul' ?_ le_rfl)
  refine ENNReal.ofReal_le_ofReal ?_
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exfalso
      have h0 : ‖x - y‖ = 0 := by simp [EuclideanSpace.norm_eq]
      rw [h0] at hxy
      simp at hxy
    · exact hd
  have hbase : (1:ℝ) ≤ 2 * Real.sqrt d := by
    have h1 : (1:ℝ) ≤ Real.sqrt d := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
    linarith
  have hΛ0 : (0:ℝ) < Λ := lt_of_lt_of_le zero_lt_one hk.one_le
  have hmono : (2 * Real.sqrt d) ^ ((d:ℝ) + α) ≤ (2 * Real.sqrt d) ^ ((d:ℝ) + 2) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  nlinarith

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

/-! ## Proposition 3.5 -/

/-- A favoured sub-cube fills at least a `1/L` share of the unit cube. -/
lemma inv_card_le_volume_cubeCone {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {θ : ℝ}
    (F : RefFamily Γ θ) (hne : F.axes.Nonempty) {x v : EuclideanSpace ℝ (Fin d)}
    (hv : IsFavoured F 1 x v) :
    ((F.axes.card : ℝ≥0∞))⁻¹ ≤ volume (cubeCone Γ (F.cone v) 1 x) := by
  have hL : (F.axes.card : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero]
    exact Finset.nonempty_iff_ne_empty.mp hne
  have hLt : (F.axes.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h1 : (1 : ℝ≥0∞) ≤ (F.axes.card : ℝ≥0∞) * volume (cubeCone Γ (F.cone v) 1 x) := by
    have h := volume_cube_le_card_mul F hv
    rwa [volume_cube one_pos, one_pow, ENNReal.ofReal_one] at h
  calc ((F.axes.card : ℝ≥0∞))⁻¹ = ((F.axes.card : ℝ≥0∞))⁻¹ * 1 := by rw [mul_one]
    _ ≤ ((F.axes.card : ℝ≥0∞))⁻¹ *
          ((F.axes.card : ℝ≥0∞) * volume (cubeCone Γ (F.cone v) 1 x)) :=
        mul_le_mul' le_rfl h1
    _ = volume (cubeCone Γ (F.cone v) 1 x) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hL hLt, one_mul]

/-- **Proposition 3.5** of Bux–Kassmann–Schulze, for `d ≥ 2`.

The constants `C` and `ϑ'` are chosen before the configuration, as the paper
requires ("the angle `ϑ'` depends only on `θ` and on the infimum `ϑ` … there is
no further dependence on `Γ`"). `CondMeas` is what the paper draws from condition
(M) by quoting Debreu's theorem; see the README. Dimension `d ≥ 2` is inherited
from Lemma 3.3, which is false in dimension one. -/
theorem prop_test_fct {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) (hd : 2 ≤ d) {α : ℝ}
    (hα : 0 < α) (hα2 : α ≤ 2) :
    ∃ C θ' : ℝ, 0 < C ∧ 0 < θ' ∧ θ' ≤ π / 2 ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ → CondMeas Γ →
      ∀ (Λ : ℝ) (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞),
        KernelBounds Γ α Λ k →
      ∃ Γ' : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ' θ' ∧
        ∀ x ∈ lattice d, ∀ y ∈ lattice d, Real.sqrt d < ‖x - y‖ →
          ENNReal.ofReal (C * Λ⁻¹) *
              ((indE (coneAt Γ' x) y + indE (coneAt Γ' y) x) * jumpKernel d α x y)
            ≤ discreteKernel d k 1 x y := by
  classical
  have hd1 : 0 < d := by omega
  have hsd : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd1)
  have hθ0 : (0:ℝ) < ϑ / 3 := by positivity
  have hθle : ϑ / 3 ≤ π / 2 := by linarith [pi_pos]
  -- the reference axes, fixed once and for all
  obtain ⟨S, hSdef⟩ : ∃ S : Finset (EuclideanSpace ℝ (Fin d)),
      S = (ref_cones (E := EuclideanSpace ℝ (Fin d)) hϑ hϑ').choose := ⟨_, rfl⟩
  have hSnorm : ∀ v ∈ S, ‖v‖ = 1 := by
    rw [hSdef]; exact (ref_cones (E := EuclideanSpace ℝ (Fin d)) hϑ hϑ').choose_spec.1
  obtain ⟨e, he⟩ : ∃ e : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 := by
    refine ⟨EuclideanSpace.single (⟨0, hd1⟩ : Fin d) (1:ℝ), ?_⟩
    simp
  have hSne : S.Nonempty := by
    obtain ⟨v, hv, -⟩ :=
      (ref_cones (E := EuclideanSpace ℝ (Fin d)) hϑ hϑ').choose_spec.2
        (fun _ => ⟨e, he, ϑ, hϑ, hϑ'⟩) ⟨hϑ, fun _ => le_rfl⟩ 0
    exact ⟨v, by rw [hSdef]; exact hv⟩
  -- Lemma 3.3, applied to the reference cones at radius `√d`
  obtain ⟨θ', hθ'0, hθ'le, hthin⟩ := lemma_new_config hd hsd hθ0 hθle S hSnorm
  refine ⟨(2 * Real.sqrt d) ^ (-(d:ℝ) - 2) * ((S.card : ℝ)⁻¹ * (S.card : ℝ)⁻¹), θ',
    by positivity, hθ'0, hθ'le, ?_⟩
  intro Γ hΓ hmeas Λ k hk
  obtain ⟨F, hFdef⟩ : ∃ F : RefFamily Γ (ϑ / 3), F = refFamily hϑ hϑ' Γ hΓ := ⟨_, rfl⟩
  have hFaxes : F.axes = S := by rw [hFdef, hSdef]; rfl
  choose fav hfav using (fun u => exists_isFavoured F 1 u)
  have haxex : ∀ u : EuclideanSpace ℝ (Fin d), ∃ w : EuclideanSpace ℝ (Fin d), ‖w‖ = 1 ∧
      (u ∈ S → doubleCone w θ' ∩ lattice d
        ⊆ shrink (doubleCone u (ϑ / 3)) (Real.sqrt d) ∩ lattice d) := by
    intro u
    by_cases hu : u ∈ S
    · obtain ⟨w, hw, hsub⟩ := hthin u hu
      exact ⟨w, hw, fun _ => hsub⟩
    · exact ⟨e, he, fun hc => absurd hc hu⟩
  choose ax hax haxsub using haxex
  refine ⟨fun u => ⟨ax (fav u), hax (fav u), θ', hθ'0, hθ'le⟩, ⟨hθ'0, fun _ => le_rfl⟩, ?_⟩
  intro x hx y hy hxy
  -- Lemma 3.3 turns the thin cone at `u` into the shrunk reference cone
  have hind : ∀ u w : EuclideanSpace ℝ (Fin d), u ∈ lattice d → w ∈ lattice d →
      indE (coneAt (fun p => (⟨ax (fav p), hax (fav p), θ', hθ'0, hθ'le⟩ :
          DCone (EuclideanSpace ℝ (Fin d)))) u) w
        ≤ indE (F.shrunkAt (fav u) (Real.sqrt d) u) w := by
    intro u w hu hw
    refine indE_le_indE (fun hmem => ?_)
    exact (haxsub (fav u) (by rw [← hFaxes]; exact (hfav u).1)
      ⟨hmem, lattice_sub hw hu⟩).1
  have hvolx := inv_card_le_volume_cubeCone F (by rw [hFaxes]; exact hSne) (hfav x)
  have hvoly := inv_card_le_volume_cubeCone F (by rw [hFaxes]; exact hSne) (hfav y)
  refine le_trans ?_ (discreteKernel_ge_volume hk hα F hmeas hx hy hxy (fav x) (fav y))
  -- the constants
  have hLpos : (0:ℝ) < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hSne
  have hLinv : ENNReal.ofReal ((S.card : ℝ)⁻¹) = ((F.axes.card : ℝ≥0∞))⁻¹ := by
    rw [hFaxes, ← ENNReal.ofReal_natCast S.card, ← ENNReal.ofReal_inv_of_pos hLpos]
  have hΛ0 : (0:ℝ) ≤ Λ⁻¹ := by
    have := lt_of_lt_of_le zero_lt_one hk.one_le
    positivity
  have hsplit : ENNReal.ofReal ((2 * Real.sqrt d) ^ (-(d:ℝ) - α) *
        ((S.card : ℝ)⁻¹ * (S.card : ℝ)⁻¹) * Λ⁻¹) *
      ((indE (coneAt (fun p => (⟨ax (fav p), hax (fav p), θ', hθ'0, hθ'le⟩ :
          DCone (EuclideanSpace ℝ (Fin d)))) x) y
        + indE (coneAt (fun p => (⟨ax (fav p), hax (fav p), θ', hθ'0, hθ'le⟩ :
          DCone (EuclideanSpace ℝ (Fin d)))) y) x) * jumpKernel d α x y)
      = ENNReal.ofReal Λ⁻¹ *
          ((indE (coneAt (fun p => (⟨ax (fav p), hax (fav p), θ', hθ'0, hθ'le⟩ :
              DCone (EuclideanSpace ℝ (Fin d)))) x) y
            + indE (coneAt (fun p => (⟨ax (fav p), hax (fav p), θ', hθ'0, hθ'le⟩ :
              DCone (EuclideanSpace ℝ (Fin d)))) y) x)
            * ENNReal.ofReal ((2 * Real.sqrt d) ^ (-(d:ℝ) - α) * ‖x - y‖ ^ (-(d:ℝ) - α)))
          * (((F.axes.card : ℝ≥0∞))⁻¹ * ((F.axes.card : ℝ≥0∞))⁻¹) := by
    rw [← hLinv, jumpKernel,
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2 * Real.sqrt d) ^ (-(d:ℝ) - α)),
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2 * Real.sqrt d) ^ (-(d:ℝ) - α) *
        ((S.card : ℝ)⁻¹ * (S.card : ℝ)⁻¹)),
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2 * Real.sqrt d) ^ (-(d:ℝ) - α)),
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ((S.card : ℝ))⁻¹)]
    ring
  -- the paper's constant is `α`-free, using `α ≤ 2`
  have hconst : ENNReal.ofReal ((2 * Real.sqrt d) ^ (-(d:ℝ) - 2) *
        ((S.card : ℝ)⁻¹ * (S.card : ℝ)⁻¹) * Λ⁻¹)
      ≤ ENNReal.ofReal ((2 * Real.sqrt d) ^ (-(d:ℝ) - α) *
        ((S.card : ℝ)⁻¹ * (S.card : ℝ)⁻¹) * Λ⁻¹) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have hbase : (1:ℝ) ≤ 2 * Real.sqrt d := by
      have h1 : (1:ℝ) ≤ Real.sqrt d := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ d by omega))
      linarith
    have hmono : (2 * Real.sqrt d) ^ (-(d:ℝ) - 2) ≤ (2 * Real.sqrt d) ^ (-(d:ℝ) - α) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    have hΛpos : (0:ℝ) < Λ⁻¹ := by
      have := lt_of_lt_of_le zero_lt_one hk.one_le
      positivity
    have hL2 : (0:ℝ) < (S.card : ℝ)⁻¹ * (S.card : ℝ)⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hmono hL2.le]
  refine le_trans (mul_le_mul' hconst le_rfl) ?_
  rw [hsplit]
  exact mul_le_mul' (mul_le_mul' le_rfl (mul_le_mul'
    (add_le_add (hind x y hx hy) (hind y x hy hx)) le_rfl))
    (mul_le_mul' hvolx hvoly)

/-! ## Corollary 3.6: the same at scale `h`

Everything in Proposition 3.5's proof is scale-covariant, so rather than
transporting the *integral* along `x ↦ hx` — which would need the change of
variables for Lebesgue measure — the estimate is proved at scale `h` directly.
The `h`'s cancel exactly: the prefactor `h^{-2d}` of `ω^k_h` against the two cube
volumes `h^d`, so the constant `C` is the same as at scale `1`, which is the
content of the paper's rescaling argument. -/

lemma sub_mem_scaledLattice {h : ℝ} {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ scaledLattice d h) (hy : y ∈ scaledLattice d h) :
    x - y ∈ scaledLattice d h := by
  intro i
  obtain ⟨n, hn⟩ := hx i
  obtain ⟨m, hm⟩ := hy i
  refine ⟨n - m, ?_⟩
  have he : (x - y) i = x i - y i := by simp
  rw [he, hn, hm]
  push_cast
  ring

/-- Shrinking commutes with scaling, for a set closed under positive scaling. -/
lemma mem_shrink_smul {V : Set (EuclideanSpace ℝ (Fin d))}
    (hV : ∀ t : ℝ, 0 < t → ∀ p, p ∈ V → t • p ∈ V) {h : ℝ} (hh : 0 < h) {r : ℝ}
    {p : EuclideanSpace ℝ (Fin d)} (hp : p ∈ shrink V r) : h • p ∈ shrink V (h * r) := by
  refine ⟨hV h hh p hp.1, fun z hz => ?_⟩
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have hzz : h⁻¹ • z ∈ closedBall p r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have he : h⁻¹ • z - p = h⁻¹ • (z - h • p) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hh), one_smul]
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [inv_mul_le_iff₀ hh]
    linarith
  have := hV h hh _ (hp.2 hzz)
  rwa [smul_smul, mul_inv_cancel₀ (ne_of_gt hh), one_smul] at this

/-- **Lemma 3.3 at scale `h`**: the thin cone's points of `hℤ^d` lie in the
`h√d`-shrinking. -/
lemma thin_cone_subset_scaled {V : Set (EuclideanSpace ℝ (Fin d))}
    (hV : ∀ t : ℝ, 0 < t → ∀ p, p ∈ V → t • p ∈ V) {w : EuclideanSpace ℝ (Fin d)}
    (hw : ‖w‖ = 1) {θ' : ℝ} (hθ0 : 0 < θ') (hθle : θ' ≤ π / 2) {h : ℝ} (hh : 0 < h)
    (hsub : doubleCone w θ' ∩ lattice d ⊆ shrink V (Real.sqrt d) ∩ lattice d) :
    doubleCone w θ' ∩ scaledLattice d h ⊆ shrink V (h * Real.sqrt d) := by
  rintro p ⟨hpc, hplat⟩
  have h1 : h⁻¹ • p ∈ lattice d := inv_smul_mem_lattice (ne_of_gt hh) hplat
  have h2 : h⁻¹ • p ∈ doubleCone w θ' :=
    smul_mem_doubleCone hw hθ0 hθle (by positivity) hpc
  have h4 := mem_shrink_smul hV hh (hsub ⟨h2, h1⟩).1
  rwa [smul_smul, mul_inv_cancel₀ (ne_of_gt hh), one_smul] at h4

/-- **Lemma 3.2** in `ℝ≥0∞`, at scale `h`. -/
theorem lemma_min_dist_E_scaled {V W : Set (EuclideanSpace ℝ (Fin d))} {h : ℝ}
    {x y s t : EuclideanSpace ℝ (Fin d)} (hs : s ∈ cube h x) (ht : t ∈ cube h y) :
    indE (shift (shrink V (h * Real.sqrt d)) x) y
        + indE (shift (shrink W (h * Real.sqrt d)) y) x
      ≤ indE (shift (shrink V (h / 2 * Real.sqrt d)) x) t
        + indE (shift (shrink W (h / 2 * Real.sqrt d)) y) s := by
  refine add_le_add (indE_le_indE (fun hy => ?_)) (indE_le_indE (fun hx => ?_))
  · exact cube_subset_of_mem_shift_shrink_scaled hy ht
  · exact cube_subset_of_mem_shift_shrink_scaled hx hs

/-- **The pointwise estimate of Proposition 3.5**, at scale `h`. -/
theorem discreteKernel_integrand_ge_scaled
    {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {α Λ : ℝ}
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (hα : 0 < α) {θ : ℝ} (F : RefFamily Γ θ) {h : ℝ}
    (hh : 0 < h) {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ scaledLattice d h)
    (hy : y ∈ scaledLattice d h) (hxy : Real.sqrt d * h < ‖x - y‖)
    {m n s t : EuclideanSpace ℝ (Fin d)} (hs : s ∈ cubeCone Γ (F.cone m) h x)
    (ht : t ∈ cubeCone Γ (F.cone n) h y) :
    ENNReal.ofReal Λ⁻¹ *
        ((indE (F.shrunkAt m (h * Real.sqrt d) x) y
          + indE (F.shrunkAt n (h * Real.sqrt d) y) x)
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
  have hxy0 : (0:ℝ) < ‖x - y‖ := lt_trans (by positivity) hxy
  have hexp : (-(d:ℝ) - α) ≤ 0 := by
    have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    linarith
  have hs1 : s ∈ cube h x := hs.1
  have ht1 : t ∈ cube h y := ht.1
  have hbr1 : indE (shift (shrink (F.cone m) (h / 2 * Real.sqrt d)) x) t
      ≤ indE (coneAt Γ s) t := by
    refine indE_le_indE (fun hmem => ?_)
    rw [mem_coneAt]
    exact hs.2 ((cone_in_intersection (F.cone m) hh.le x hs1).2 hmem)
  have hbr2 : indE (shift (shrink (F.cone n) (h / 2 * Real.sqrt d)) y) s
      ≤ indE (coneAt Γ t) s := by
    refine indE_le_indE (fun hmem => ?_)
    rw [mem_coneAt]
    exact ht.2 ((cone_in_intersection (F.cone n) hh.le y ht1).2 hmem)
  have hker : ENNReal.ofReal ((2 * Real.sqrt d) ^ (-(d:ℝ) - α) * ‖x - y‖ ^ (-(d:ℝ) - α))
      ≤ jumpKernel d α s t := by
    obtain ⟨hlow, hup⟩ := lemma_cubes hh hx hy hxy hs1 ht1
    have hst0 : (0:ℝ) < ‖s - t‖ := lt_trans (by positivity) hlow
    have h1 : ‖s - t‖ ^ (-(d:ℝ) - α) ≥ (2 * Real.sqrt d * ‖x - y‖) ^ (-(d:ℝ) - α) :=
      Real.rpow_le_rpow_of_nonpos hst0 hup.le hexp
    have h2 : (2 * Real.sqrt d * ‖x - y‖) ^ (-(d:ℝ) - α)
        = (2 * Real.sqrt d) ^ (-(d:ℝ) - α) * ‖x - y‖ ^ (-(d:ℝ) - α) :=
      Real.mul_rpow (by positivity) (norm_nonneg _)
    rw [jumpKernel]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith [h1, h2.le, h2.ge]
  refine le_trans (mul_le_mul' le_rfl (mul_le_mul' ?_ hker)) (hk.lower s t)
  exact le_trans (lemma_min_dist_E_scaled hs1 ht1) (add_le_add hbr1 hbr2)

/-- A favoured sub-cube fills at least a `1/L` share of the cube, at scale `h`. -/
lemma inv_card_le_volume_cubeCone_scaled
    {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {θ : ℝ} (F : RefFamily Γ θ)
    (hne : F.axes.Nonempty) {h : ℝ} (hh : 0 < h) {x v : EuclideanSpace ℝ (Fin d)}
    (hv : IsFavoured F h x v) :
    ENNReal.ofReal (h ^ d) * ((F.axes.card : ℝ≥0∞))⁻¹
      ≤ volume (cubeCone Γ (F.cone v) h x) := by
  have hL : (F.axes.card : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero]
    exact Finset.nonempty_iff_ne_empty.mp hne
  have hLt : (F.axes.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h1 : ENNReal.ofReal (h ^ d)
      ≤ (F.axes.card : ℝ≥0∞) * volume (cubeCone Γ (F.cone v) h x) := by
    have h := volume_cube_le_card_mul F hv
    rwa [volume_cube hh] at h
  calc ENNReal.ofReal (h ^ d) * ((F.axes.card : ℝ≥0∞))⁻¹
      ≤ ((F.axes.card : ℝ≥0∞) * volume (cubeCone Γ (F.cone v) h x))
        * ((F.axes.card : ℝ≥0∞))⁻¹ := mul_le_mul' h1 le_rfl
    _ = volume (cubeCone Γ (F.cone v) h x) := by
        rw [mul_comm ((F.axes.card : ℝ≥0∞)) _, mul_assoc,
          ENNReal.mul_inv_cancel hL hLt, mul_one]

/-- **The lower bound of Proposition 3.5 at scale `h`**, before the constants are
collected. -/
theorem discreteKernel_ge_volume_scaled
    {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {α Λ : ℝ}
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (hα : 0 < α) {θ : ℝ} (F : RefFamily Γ θ)
    (hmeas : CondMeas Γ) {h : ℝ} (hh : 0 < h) {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ scaledLattice d h) (hy : y ∈ scaledLattice d h)
    (hxy : Real.sqrt d * h < ‖x - y‖) (m n : EuclideanSpace ℝ (Fin d)) :
    ENNReal.ofReal ((h ^ (2 * d))⁻¹) *
        (ENNReal.ofReal Λ⁻¹ *
          ((indE (F.shrunkAt m (h * Real.sqrt d) x) y
            + indE (F.shrunkAt n (h * Real.sqrt d) y) x)
            * ENNReal.ofReal ((2 * Real.sqrt d) ^ (-(d:ℝ) - α) * ‖x - y‖ ^ (-(d:ℝ) - α)))
          * (volume (cubeCone Γ (F.cone m) h x) * volume (cubeCone Γ (F.cone n) h y)))
      ≤ discreteKernel d k h x y := by
  refine mul_le_mul' le_rfl ?_
  have hsub : cubeCone Γ (F.cone m) h x ×ˢ cubeCone Γ (F.cone n) h y
      ⊆ cube h x ×ˢ cube h y :=
    Set.prod_mono (cubeCone_subset_cube _ _ _ _) (cubeCone_subset_cube _ _ _ _)
  calc ENNReal.ofReal Λ⁻¹ *
        ((indE (F.shrunkAt m (h * Real.sqrt d) x) y
          + indE (F.shrunkAt n (h * Real.sqrt d) y) x)
          * ENNReal.ofReal ((2 * Real.sqrt d) ^ (-(d:ℝ) - α) * ‖x - y‖ ^ (-(d:ℝ) - α)))
        * (volume (cubeCone Γ (F.cone m) h x) * volume (cubeCone Γ (F.cone n) h y))
      = ∫⁻ _ in cubeCone Γ (F.cone m) h x ×ˢ cubeCone Γ (F.cone n) h y,
          ENNReal.ofReal Λ⁻¹ *
            ((indE (F.shrunkAt m (h * Real.sqrt d) x) y
              + indE (F.shrunkAt n (h * Real.sqrt d) y) x)
              * ENNReal.ofReal ((2 * Real.sqrt d) ^ (-(d:ℝ) - α)
                * ‖x - y‖ ^ (-(d:ℝ) - α))) := by
        rw [setLIntegral_const, Measure.volume_eq_prod, Measure.prod_prod]
    _ ≤ ∫⁻ p in cubeCone Γ (F.cone m) h x ×ˢ cubeCone Γ (F.cone n) h y, k p.1 p.2 := by
        refine lintegral_mono_ae (ae_restrict_of_forall_mem
          ((measurableSet_cubeCone hmeas _ hh x).prod
            (measurableSet_cubeCone hmeas _ hh y)) ?_)
        rintro ⟨s, t⟩ ⟨hs, ht⟩
        exact discreteKernel_integrand_ge_scaled hk hα F hh hx hy hxy hs ht
    _ ≤ ∫⁻ p in cube h x ×ˢ cube h y, k p.1 p.2 :=
        lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl

/-- **Corollary 3.6** of Bux–Kassmann–Schulze, for `d ≥ 2`, with the constant
where the paper puts it: `C` depends on `d`, `ϑ`, `α` and `Λ` only, and in
particular neither on the configuration nor on the kernel nor on the scale.
For every `h > 0` the discrete kernel `ω^k_h` satisfies assumption (4) on
`hℤ^d`, for a configuration `Γ^h` whose apex angles are bounded below by a `ϑ'`
independent of `h`. -/
theorem cor_rescaled_kernel_uniform {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) (hd : 2 ≤ d)
    {α : ℝ} (hα : 0 < α) (hα2 : α ≤ 2) :
    ∃ θ' : ℝ, 0 < θ' ∧ θ' ≤ π / 2 ∧
      ∀ Λ : ℝ, 1 ≤ Λ →
      ∃ C : ℝ, 0 < C ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ → CondMeas Γ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
        KernelBounds Γ α Λ k →
      ∀ h : ℝ, 0 < h →
      ∃ Γ' : Configuration (EuclideanSpace ℝ (Fin d)),
        (∀ u, (Γ' u).apex = θ') ∧ IsBounded Γ' θ' ∧
        ∀ x ∈ scaledLattice d h, ∀ y ∈ scaledLattice d h, Real.sqrt d * h < ‖x - y‖ →
          ENNReal.ofReal C⁻¹ *
              ((indE (coneAt Γ' x) y + indE (coneAt Γ' y) x) * jumpKernel d α x y)
            ≤ discreteKernel d k h x y ∧
          discreteKernel d k h x y ≤ ENNReal.ofReal C * jumpKernel d α x y := by
  classical
  have hd1 : 0 < d := by omega
  have hsd : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd1)
  have hθ0 : (0:ℝ) < ϑ / 3 := by positivity
  have hθle : ϑ / 3 ≤ π / 2 := by linarith [pi_pos]
  obtain ⟨S, hSdef⟩ : ∃ S : Finset (EuclideanSpace ℝ (Fin d)),
      S = (ref_cones (E := EuclideanSpace ℝ (Fin d)) hϑ hϑ').choose := ⟨_, rfl⟩
  have hSnorm : ∀ v ∈ S, ‖v‖ = 1 := by
    rw [hSdef]; exact (ref_cones (E := EuclideanSpace ℝ (Fin d)) hϑ hϑ').choose_spec.1
  obtain ⟨e, he⟩ : ∃ e : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 := by
    refine ⟨EuclideanSpace.single (⟨0, hd1⟩ : Fin d) (1:ℝ), ?_⟩
    simp
  have hSne : S.Nonempty := by
    obtain ⟨v, hv, -⟩ :=
      (ref_cones (E := EuclideanSpace ℝ (Fin d)) hϑ hϑ').choose_spec.2
        (fun _ => ⟨e, he, ϑ, hϑ, hϑ'⟩) ⟨hϑ, fun _ => le_rfl⟩ 0
    exact ⟨v, by rw [hSdef]; exact hv⟩
  obtain ⟨θ', hθ'0, hθ'le, hthin⟩ := lemma_new_config hd hsd hθ0 hθle S hSnorm
  refine ⟨θ', hθ'0, hθ'le, ?_⟩
  intro Λ hΛ1
  have hΛ0 : (0:ℝ) < Λ := lt_of_lt_of_le zero_lt_one hΛ1
  have hLpos : (0:ℝ) < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hSne
  obtain ⟨C₀, hC₀def⟩ : ∃ C : ℝ,
      C = (2 * Real.sqrt d) ^ (-(d:ℝ) - α) * ((S.card : ℝ)⁻¹ * (S.card : ℝ)⁻¹) := ⟨_, rfl⟩
  have hC₀0 : (0:ℝ) < C₀ := by rw [hC₀def]; positivity
  refine ⟨max (Λ * (2 * Real.sqrt d) ^ ((d:ℝ) + 2)) (C₀ * Λ⁻¹)⁻¹,
    lt_of_lt_of_le (by positivity) (le_max_left _ _), ?_⟩
  intro Γ hΓ hmeas k hk h hh
  obtain ⟨F, hFdef⟩ : ∃ F : RefFamily Γ (ϑ / 3), F = refFamily hϑ hϑ' Γ hΓ := ⟨_, rfl⟩
  have hFaxes : F.axes = S := by rw [hFdef, hSdef]; rfl
  choose fav hfav using (fun u => exists_isFavoured F h u)
  have haxex : ∀ u : EuclideanSpace ℝ (Fin d), ∃ w : EuclideanSpace ℝ (Fin d), ‖w‖ = 1 ∧
      (u ∈ S → doubleCone w θ' ∩ lattice d
        ⊆ shrink (doubleCone u (ϑ / 3)) (Real.sqrt d) ∩ lattice d) := by
    intro u
    by_cases hu : u ∈ S
    · obtain ⟨w, hw, hsub⟩ := hthin u hu
      exact ⟨w, hw, fun _ => hsub⟩
    · exact ⟨e, he, fun hc => absurd hc hu⟩
  choose ax hax haxsub using haxex
  obtain ⟨G, hG⟩ : ∃ G : Configuration (EuclideanSpace ℝ (Fin d)),
      G = fun u => (⟨ax (fav u), hax (fav u), θ', hθ'0, hθ'le⟩ :
        DCone (EuclideanSpace ℝ (Fin d))) := ⟨_, rfl⟩
  refine ⟨G, fun u => by rw [hG], ⟨hθ'0, fun u => by rw [hG]⟩, ?_⟩
  intro x hx y hy hxy
  refine ⟨?_, ?_⟩
  swap
  · exact le_trans (discreteKernel_le' hk hα hα2 hh hx hy hxy)
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl)
  -- the lower bound
  have hind : ∀ u w : EuclideanSpace ℝ (Fin d), u ∈ scaledLattice d h →
      w ∈ scaledLattice d h →
      indE (coneAt G u) w ≤ indE (F.shrunkAt (fav u) (h * Real.sqrt d) u) w := by
    intro u w hu hw
    refine indE_le_indE (fun hmem => ?_)
    rw [hG] at hmem
    refine thin_cone_subset_scaled ?_ (hax (fav u)) hθ'0 hθ'le hh
      (haxsub (fav u) (by rw [← hFaxes]; exact (hfav u).1))
      ⟨hmem, sub_mem_scaledLattice hw hu⟩
    exact fun t ht p hp => smul_mem_doubleCone (F.norm_axes _
      (by rw [hFaxes, ← hFaxes]; exact (hfav u).1)) hθ0 hθle ht hp
  have hvolx := inv_card_le_volume_cubeCone_scaled F (by rw [hFaxes]; exact hSne) hh (hfav x)
  have hvoly := inv_card_le_volume_cubeCone_scaled F (by rw [hFaxes]; exact hSne) hh (hfav y)
  refine le_trans ?_ (discreteKernel_ge_volume_scaled hk hα F hmeas hh hx hy hxy
    (fav x) (fav y))
  have hLinv : ENNReal.ofReal ((S.card : ℝ)⁻¹) = ((F.axes.card : ℝ≥0∞))⁻¹ := by
    rw [hFaxes, ← ENNReal.ofReal_natCast S.card, ← ENNReal.ofReal_inv_of_pos hLpos]
  have hCle : ENNReal.ofReal (max (Λ * (2 * Real.sqrt d) ^ ((d:ℝ) + 2)) (C₀ * Λ⁻¹)⁻¹)⁻¹
      ≤ ENNReal.ofReal (C₀ * Λ⁻¹) := by
    refine ENNReal.ofReal_le_ofReal ?_
    rw [inv_le_comm₀ (by positivity) (by positivity)]
    exact le_max_right _ _
  refine le_trans (mul_le_mul' hCle le_rfl) ?_
  obtain ⟨B, hB⟩ : ∃ B : ℝ≥0∞, B = indE (coneAt G x) y + indE (coneAt G y) x := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B' : ℝ≥0∞, B' = indE (F.shrunkAt (fav x) (h * Real.sqrt d) x) y
      + indE (F.shrunkAt (fav y) (h * Real.sqrt d) y) x := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : ℝ≥0∞, J = ENNReal.ofReal ((2 * Real.sqrt d) ^ (-(d:ℝ) - α)
      * ‖x - y‖ ^ (-(d:ℝ) - α)) := ⟨_, rfl⟩
  rw [← hB, ← hB', ← hJ]
  have hcancel := ofReal_inv_pow_mul (d := d) hh
  have hJeq : ENNReal.ofReal (C₀ * Λ⁻¹) * (B * jumpKernel d α x y)
      = ENNReal.ofReal Λ⁻¹ * (B * J)
        * (ENNReal.ofReal ((S.card : ℝ)⁻¹) * ENNReal.ofReal ((S.card : ℝ)⁻¹)) := by
    rw [hJ, hC₀def, jumpKernel,
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2 * Real.sqrt d) ^ (-(d:ℝ) - α)),
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2 * Real.sqrt d) ^ (-(d:ℝ) - α) *
        ((S.card : ℝ)⁻¹ * (S.card : ℝ)⁻¹)),
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2 * Real.sqrt d) ^ (-(d:ℝ) - α)),
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ((S.card : ℝ))⁻¹)]
    ring
  calc ENNReal.ofReal (C₀ * Λ⁻¹) * (B * jumpKernel d α x y)
      = ENNReal.ofReal Λ⁻¹ * (B * J)
          * (ENNReal.ofReal ((S.card : ℝ)⁻¹) * ENNReal.ofReal ((S.card : ℝ)⁻¹)) := hJeq
    _ = (ENNReal.ofReal ((h ^ (2 * d))⁻¹) *
          (ENNReal.ofReal (h ^ d) * ENNReal.ofReal (h ^ d))) *
        (ENNReal.ofReal Λ⁻¹ * (B * J)
          * (((F.axes.card : ℝ≥0∞))⁻¹ * ((F.axes.card : ℝ≥0∞))⁻¹)) := by
        rw [hcancel, one_mul, hLinv]
    _ = ENNReal.ofReal ((h ^ (2 * d))⁻¹) * (ENNReal.ofReal Λ⁻¹ * (B * J)
          * ((ENNReal.ofReal (h ^ d) * ((F.axes.card : ℝ≥0∞))⁻¹)
            * (ENNReal.ofReal (h ^ d) * ((F.axes.card : ℝ≥0∞))⁻¹))) := by ring
    _ ≤ ENNReal.ofReal ((h ^ (2 * d))⁻¹) * (ENNReal.ofReal Λ⁻¹ * (B' * J)
          * (volume (cubeCone Γ (F.cone (fav x)) h x)
            * volume (cubeCone Γ (F.cone (fav y)) h y))) := by
        refine mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' le_rfl (mul_le_mul' ?_ le_rfl))
          (mul_le_mul' hvolx hvoly))
        rw [hB, hB']
        exact add_le_add (hind x y hx hy) (hind y x hy hx)


/-- **Corollary 3.6** in the shape the paper states it: the constant is produced
after the configuration and the kernel. It is `cor_rescaled_kernel_uniform` with
the existential weakened; the proof there gives the stronger order. -/
theorem cor_rescaled_kernel {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) (hd : 2 ≤ d)
    {α : ℝ} (hα : 0 < α) (hα2 : α ≤ 2) :
    ∃ θ' : ℝ, 0 < θ' ∧ θ' ≤ π / 2 ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ → CondMeas Γ →
      ∀ (Λ : ℝ) (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞),
        KernelBounds Γ α Λ k →
      ∃ C : ℝ, 0 < C ∧
      ∀ h : ℝ, 0 < h →
      ∃ Γ' : Configuration (EuclideanSpace ℝ (Fin d)),
        (∀ u, (Γ' u).apex = θ') ∧ IsBounded Γ' θ' ∧
        ∀ x ∈ scaledLattice d h, ∀ y ∈ scaledLattice d h, Real.sqrt d * h < ‖x - y‖ →
          ENNReal.ofReal C⁻¹ *
              ((indE (coneAt Γ' x) y + indE (coneAt Γ' y) x) * jumpKernel d α x y)
            ≤ discreteKernel d k h x y ∧
          discreteKernel d k h x y ≤ ENNReal.ofReal C * jumpKernel d α x y := by
  obtain ⟨θ', hθ0, hθle, hmain⟩ := cor_rescaled_kernel_uniform hϑ hϑ' hd hα hα2
  refine ⟨θ', hθ0, hθle, fun Γ hΓ hmeas Λ k hk => ?_⟩
  obtain ⟨C, hC0, hCmain⟩ := hmain Λ hk.one_le
  exact ⟨C, hC0, fun h hh => hCmain Γ hΓ hmeas k hk h hh⟩

end QFS
