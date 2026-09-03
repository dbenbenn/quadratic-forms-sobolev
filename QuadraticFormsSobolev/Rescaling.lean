/-
Corollary 3.1 of Bux–Kassmann–Schulze: the `hℤ^d` version of Theorem 1.3.

"By scaling, we can deduce the following `hℤ^d`-version from Theorem 1.3." The
scaling is `x ↦ hx`, which carries `ℤ^d` onto `hℤ^d`, multiplies distances by
`h`, and therefore multiplies the jump kernel by `h^{-d-α}`; the paper's
observation that "every `ω ∈ M` is of the form `h^{-d-α} ω̃(h^{-1}x, h^{-1}y)`
for some `ω̃ ∈ N`" is `QFS.discreteKernelBounds_rescale` below.
-/
import QuadraticFormsSobolev.Section6

open Real Set Metric ENNReal

namespace QFS

variable {d : ℕ}

/-! ## The scaled lattice as an image of `ℤ^d` -/

lemma smul_mem_scaledLattice {h : ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ lattice d) : h • x ∈ scaledLattice d h := by
  intro i
  obtain ⟨n, hn⟩ := (mem_lattice_iff.mp hx) i
  refine ⟨n, ?_⟩
  have he : (h • x) i = h * x i := by simp
  rw [he, hn]
  ring

lemma inv_smul_mem_lattice {h : ℝ} (hh : h ≠ 0) {y : EuclideanSpace ℝ (Fin d)}
    (hy : y ∈ scaledLattice d h) : h⁻¹ • y ∈ lattice d := by
  rw [mem_lattice_iff]
  intro i
  obtain ⟨n, hn⟩ := hy i
  refine ⟨n, ?_⟩
  have he : (h⁻¹ • y) i = h⁻¹ * y i := by simp
  rw [he, hn]
  field_simp

/-- Scaling by `h > 0` as an equivalence of `ℝ^d`. -/
noncomputable def smulEquiv {h : ℝ} (hh : h ≠ 0) :
    EuclideanSpace ℝ (Fin d) ≃ EuclideanSpace ℝ (Fin d) where
  toFun x := h⁻¹ • x
  invFun y := h • y
  left_inv x := by
    simp only []
    rw [smul_smul, mul_inv_cancel₀ hh, one_smul]
  right_inv y := by
    simp only []
    rw [smul_smul, inv_mul_cancel₀ hh, one_smul]

@[simp] lemma smulEquiv_apply {h : ℝ} (hh : h ≠ 0) (x : EuclideanSpace ℝ (Fin d)) :
    smulEquiv hh x = h⁻¹ • x := rfl

@[simp] lemma smulEquiv_symm_apply {h : ℝ} (hh : h ≠ 0) (y : EuclideanSpace ℝ (Fin d)) :
    (smulEquiv hh).symm y = h • y := rfl

/-! ## Cones are invariant under positive scaling -/

lemma smul_mem_doubleCone {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) {ϑ : ℝ}
    (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {t : ℝ} (ht : 0 < t)
    {p : EuclideanSpace ℝ (Fin d)} (hp : p ∈ doubleCone v ϑ) :
    t • p ∈ doubleCone v ϑ := by
  rw [mem_doubleCone_iff] at hp ⊢
  rcases hp with hc | hc
  · exact Or.inl (smul_mem_cone hv hϑ hϑ' ht hc)
  · refine Or.inr ?_
    have he : -(t • p) = t • (-p) := by rw [smul_neg]
    rw [he]
    exact smul_mem_cone hv hϑ hϑ' ht hc

lemma smul_mem_doubleCone_iff {h : ℝ} (hh : 0 < h) {v : EuclideanSpace ℝ (Fin d)}
    (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    (p : EuclideanSpace ℝ (Fin d)) :
    h • p ∈ doubleCone v ϑ ↔ p ∈ doubleCone v ϑ := by
  constructor
  · intro hp
    have := smul_mem_doubleCone hv hϑ hϑ' (t := h⁻¹) (by positivity) hp
    rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt hh), one_smul] at this
  · exact fun hp => smul_mem_doubleCone hv hϑ hϑ' hh hp

/-! ## The discrete form over an arbitrary lattice -/

/-- The discrete quadratic form of Theorem 1.3, over an arbitrary lattice `L`.
Corollary 3.1 needs it for `L = hℤ^d`. -/
noncomputable def discreteFormOn (L S : Set (EuclideanSpace ℝ (Fin d))) (R₀ : ℝ)
    (ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  ∑' p : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
      p.1 ∈ S ∩ L ∧ p.2 ∈ S ∩ L ∧ R₀ < ‖p.1 - p.2‖},
    ENNReal.ofReal ((f p.1.1 - f p.1.2) ^ 2) * ω p.1.1 p.1.2

lemma discreteForm_eq_discreteFormOn (S : Set (EuclideanSpace ℝ (Fin d))) (R₀ : ℝ)
    (ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    discreteForm S R₀ ω f = discreteFormOn (lattice d) S R₀ ω f := rfl

/-- Pulling a constant out of the kernel. -/
lemma discreteFormOn_const_mul (L S : Set (EuclideanSpace ℝ (Fin d))) (R₀ : ℝ)
    (c : ℝ≥0∞) (ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    discreteFormOn L S R₀ (fun x y => c * ω x y) f = c * discreteFormOn L S R₀ ω f := by
  rw [discreteFormOn, discreteFormOn, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun p => by ring

/-- The scaling `x ↦ hx` carries the form over `ℤ^d` to the form over `hℤ^d`. -/
theorem discreteFormOn_smul {h : ℝ} (hh : 0 < h) (S : Set (EuclideanSpace ℝ (Fin d)))
    (R₀ : ℝ) (ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    discreteFormOn (scaledLattice d h) S (R₀ * h) ω f
      = discreteFormOn (lattice d) ((fun x => h • x) ⁻¹' S) R₀
          (fun x y => ω (h • x) (h • y)) (fun x => f (h • x)) := by
  have hh0 : h ≠ 0 := ne_of_gt hh
  have hnorm : ∀ x y : EuclideanSpace ℝ (Fin d), ‖h • x - h • y‖ = h * ‖x - y‖ := by
    intro x y
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
  refine (Equiv.tsum_eq (Equiv.subtypeEquiv
    (Equiv.prodCongr (smulEquiv hh0).symm (smulEquiv hh0).symm) (fun p => ?_)) _).symm
  constructor
  · rintro ⟨⟨hp1S, hp1L⟩, ⟨hp2S, hp2L⟩, hp3⟩
    refine ⟨⟨hp1S, smul_mem_scaledLattice hp1L⟩, ⟨hp2S, smul_mem_scaledLattice hp2L⟩, ?_⟩
    rw [show ((Equiv.prodCongr (smulEquiv hh0).symm (smulEquiv hh0).symm) p).1 = h • p.1 from rfl,
      show ((Equiv.prodCongr (smulEquiv hh0).symm (smulEquiv hh0).symm) p).2 = h • p.2 from rfl,
      hnorm]
    nlinarith
  · rintro ⟨⟨hp1S, hp1L⟩, ⟨hp2S, hp2L⟩, hp3⟩
    rw [show ((Equiv.prodCongr (smulEquiv hh0).symm (smulEquiv hh0).symm) p).1 = h • p.1 from rfl,
      show ((Equiv.prodCongr (smulEquiv hh0).symm (smulEquiv hh0).symm) p).2 = h • p.2 from rfl,
      hnorm] at hp3
    have hcancel : ∀ q : EuclideanSpace ℝ (Fin d), h • q ∈ scaledLattice d h →
        q ∈ lattice d := by
      intro q hq
      have hq' := inv_smul_mem_lattice hh0 hq
      rwa [smul_smul, inv_mul_cancel₀ hh0, one_smul] at hq'
    refine ⟨⟨hp1S, hcancel p.1 hp1L⟩, ⟨hp2S, hcancel p.2 hp2L⟩, ?_⟩
    nlinarith

/-! ## The kernel under scaling -/

lemma jumpKernel_smul {h : ℝ} (hh : 0 < h) (α : ℝ) (x y : EuclideanSpace ℝ (Fin d)) :
    jumpKernel d α (h • x) (h • y)
      = ENNReal.ofReal (h ^ (-(d:ℝ) - α)) * jumpKernel d α x y := by
  have hnorm : ‖h • x - h • y‖ = h * ‖x - y‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
  rw [jumpKernel, jumpKernel, hnorm, Real.mul_rpow hh.le (norm_nonneg _),
    ENNReal.ofReal_mul (Real.rpow_nonneg hh.le _)]

lemma ofReal_rpow_mul_jumpKernel {h : ℝ} (hh : 0 < h) (α : ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    ENNReal.ofReal (h ^ ((d:ℝ) + α)) * jumpKernel d α (h • x) (h • y)
      = jumpKernel d α x y := by
  rw [jumpKernel_smul hh, ← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hh.le _),
    ← Real.rpow_add hh]
  norm_num

lemma indE_congr {S T : Set (EuclideanSpace ℝ (Fin d))} {x y : EuclideanSpace ℝ (Fin d)}
    (h : x ∈ S ↔ y ∈ T) : indE S x = indE T y := by
  by_cases hx : x ∈ S
  · rw [indE, indE, Set.indicator_of_mem hx, Set.indicator_of_mem (h.mp hx)]
  · rw [indE, indE, Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (fun hc => hx (h.mpr hc))]

/-- **The paper's observation** that "every `ω ∈ M` is of the form
`h^{-d-α} ω̃(h^{-1}x, h^{-1}y)` for some `ω̃ ∈ N`", read backwards: rescaling a
kernel on `hℤ^d` gives a kernel on `ℤ^d` satisfying (1.7) with the same `Λ` and
`R₀`, for the rescaled configuration. -/
theorem discreteKernelBounds_rescale {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {α Λ R₀ h : ℝ} (hh : 0 < h)
    {ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hω : DiscreteKernelBounds Γ α Λ (R₀ * h) ω) :
    DiscreteKernelBounds (fun x => Γ (h • x)) α Λ R₀
      (fun x y => ENNReal.ofReal (h ^ ((d:ℝ) + α)) * ω (h • x) (h • y)) where
  one_le := hω.one_le
  symm := fun x y => by rw [hω.symm]
  lower := by
    intro x y hxy
    have hd : (R₀ * h) < ‖h • x - h • y‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
      have : ‖x - y‖ = ‖x - y‖ := rfl
      nlinarith [hω.one_le]
    have hcone : ∀ a b : EuclideanSpace ℝ (Fin d),
        indE (coneAt (fun z => Γ (h • z)) a) b = indE (coneAt Γ (h • a)) (h • b) := by
      intro a b
      refine indE_congr ?_
      simp only [mem_coneAt]
      have he : h • b - h • a = h • (b - a) := by rw [smul_sub]
      rw [he]
      exact (smul_mem_doubleCone_iff hh (Γ (h • a)).norm_axis (Γ (h • a)).apex_pos
        (Γ (h • a)).apex_le (b - a)).symm
    rw [hcone x y, hcone y x, ← ofReal_rpow_mul_jumpKernel hh α x y]
    have hlow := hω.lower (h • x) (h • y) hd
    calc ENNReal.ofReal Λ⁻¹ * ((indE (coneAt Γ (h • x)) (h • y)
            + indE (coneAt Γ (h • y)) (h • x))
          * (ENNReal.ofReal (h ^ ((d:ℝ) + α)) * jumpKernel d α (h • x) (h • y)))
        = ENNReal.ofReal (h ^ ((d:ℝ) + α)) * (ENNReal.ofReal Λ⁻¹ *
            ((indE (coneAt Γ (h • x)) (h • y) + indE (coneAt Γ (h • y)) (h • x))
              * jumpKernel d α (h • x) (h • y))) := by ring
      _ ≤ ENNReal.ofReal (h ^ ((d:ℝ) + α)) * ω (h • x) (h • y) := mul_le_mul' le_rfl hlow
  upper := by
    intro x y hxy
    have hd : (R₀ * h) < ‖h • x - h • y‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
      nlinarith [hω.one_le]
    have hup := hω.upper (h • x) (h • y) hd
    calc ENNReal.ofReal (h ^ ((d:ℝ) + α)) * ω (h • x) (h • y)
        ≤ ENNReal.ofReal (h ^ ((d:ℝ) + α)) *
            (ENNReal.ofReal Λ * jumpKernel d α (h • x) (h • y)) := mul_le_mul' le_rfl hup
      _ = ENNReal.ofReal Λ * (ENNReal.ofReal (h ^ ((d:ℝ) + α))
            * jumpKernel d α (h • x) (h • y)) := by ring
      _ = ENNReal.ofReal Λ * jumpKernel d α x y := by
          rw [ofReal_rpow_mul_jumpKernel hh]

/-! ## Balls under scaling -/

lemma preimage_smul_ball {h : ℝ} (hh : 0 < h) (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ) :
    (fun x => h • x) ⁻¹' (ball x₀ R) = ball (h⁻¹ • x₀) (R / h) := by
  ext x
  have he : h • x - x₀ = h • (x - h⁻¹ • x₀) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ (ne_of_gt hh), one_smul]
  simp only [Set.mem_preimage, mem_ball, dist_eq_norm, he, norm_smul, Real.norm_eq_abs,
    abs_of_pos hh]
  rw [lt_div_iff₀ hh]
  constructor <;> intro H <;> linarith

/-! ## Corollary 3.1 -/

lemma discreteFormOn_congr (L S : Set (EuclideanSpace ℝ (Fin d))) (R₀ : ℝ)
    {ω₁ ω₂ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (h : ∀ x y, ω₁ x y = ω₂ x y) (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    discreteFormOn L S R₀ ω₁ f = discreteFormOn L S R₀ ω₂ f :=
  tsum_congr fun p => by rw [h]

/-- **Corollary 3.1** of Bux–Kassmann–Schulze: the `hℤ^d` version of Theorem 1.3,
with the *same* constants `κ` and `c` — in particular independent of `h`, as the
paper asserts.

The paper writes the inequality with the constant on the left (`c Σ ≤ Σ`); it is
stated here in the same orientation as Theorem 1.3 (`Σ ≤ c Σ`), which is the
same assertion with `c` replaced by `c⁻¹`. -/
theorem corollaryThreeOne (ϑ Λ α R₀ : ℝ) (hϑ : 0 < ϑ) (hΛ : 1 ≤ Λ) (hα : 0 < α)
    (hα2 : α < 2) (hR₀ : 0 < R₀) :
    ∃ κ c : ℝ, 1 ≤ κ ∧ 1 ≤ c ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ →
      ∀ h : ℝ, 0 < h →
      ∀ ω, DiscreteKernelBounds Γ α Λ (R₀ * h) ω →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ),
        0 < R →
        discreteFormOn (scaledLattice d h) (ball x₀ R) (R₀ * h) (jumpKernel d α) f
          ≤ ENNReal.ofReal c *
            discreteFormOn (scaledLattice d h) (ball x₀ (κ * R)) (R₀ * h) ω f := by
  obtain ⟨κ, c, hκ, hc, hmain⟩ := theoremOneThree (d := d) ϑ Λ α R₀ hϑ hΛ hα hα2 hR₀
  refine ⟨κ, c, hκ, hc, ?_⟩
  intro Γ hΓ h hh ω hω x₀ R f hR
  have hΓh : IsBounded (fun x => Γ (h • x)) ϑ := ⟨hΓ.1, fun x => hΓ.2 _⟩
  have hmain' := hmain (fun x => Γ (h • x)) hΓh _ (discreteKernelBounds_rescale hh hω)
    (h⁻¹ • x₀) (R / h) (fun x => f (h • x)) (by positivity)
  rw [discreteForm_eq_discreteFormOn, discreteForm_eq_discreteFormOn] at hmain'
  -- the two sides, transported to `ℤ^d`
  have hL : discreteFormOn (scaledLattice d h) (ball x₀ R) (R₀ * h) (jumpKernel d α) f
      = ENNReal.ofReal (h ^ (-(d:ℝ) - α)) *
        discreteFormOn (lattice d) (ball (h⁻¹ • x₀) (R / h)) R₀ (jumpKernel d α)
          (fun x => f (h • x)) := by
    rw [discreteFormOn_smul hh, preimage_smul_ball hh,
      discreteFormOn_congr _ _ _ (fun x y => jumpKernel_smul hh α x y) _,
      discreteFormOn_const_mul]
  have hR' : discreteFormOn (scaledLattice d h) (ball x₀ (κ * R)) (R₀ * h) ω f
      = ENNReal.ofReal (h ^ (-(d:ℝ) - α)) *
        discreteFormOn (lattice d) (ball (h⁻¹ • x₀) (κ * (R / h))) R₀
          (fun x y => ENNReal.ofReal (h ^ ((d:ℝ) + α)) * ω (h • x) (h • y))
          (fun x => f (h • x)) := by
    have hmul : ∀ x y : EuclideanSpace ℝ (Fin d), ω (h • x) (h • y)
        = ENNReal.ofReal (h ^ (-(d:ℝ) - α)) *
          (ENNReal.ofReal (h ^ ((d:ℝ) + α)) * ω (h • x) (h • y)) := by
      intro x y
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hh.le _), ← Real.rpow_add hh]
      norm_num
    rw [discreteFormOn_smul hh, preimage_smul_ball hh,
      discreteFormOn_congr _ _ _ hmul _, discreteFormOn_const_mul,
      show κ * R / h = κ * (R / h) by ring]
  rw [hL, hR']
  calc ENNReal.ofReal (h ^ (-(d:ℝ) - α)) *
        discreteFormOn (lattice d) (ball (h⁻¹ • x₀) (R / h)) R₀ (jumpKernel d α)
          (fun x => f (h • x))
      ≤ ENNReal.ofReal (h ^ (-(d:ℝ) - α)) * (ENNReal.ofReal c *
          discreteFormOn (lattice d) (ball (h⁻¹ • x₀) (κ * (R / h))) R₀
            (fun x y => ENNReal.ofReal (h ^ ((d:ℝ) + α)) * ω (h • x) (h • y))
            (fun x => f (h • x))) := mul_le_mul' le_rfl hmain'
    _ = ENNReal.ofReal c * (ENNReal.ofReal (h ^ (-(d:ℝ) - α)) *
          discreteFormOn (lattice d) (ball (h⁻¹ • x₀) (κ * (R / h))) R₀
            (fun x y => ENNReal.ofReal (h ^ ((d:ℝ) + α)) * ω (h • x) (h • y))
            (fun x => f (h • x))) := by ring

end QFS
