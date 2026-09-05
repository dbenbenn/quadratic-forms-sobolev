/-
Witnesses: the hypotheses of the main theorems are satisfiable.

A formalisation of this size is worth checking against vacuity. Each of the
headline results quantifies over configurations `Γ` and kernels `k`/`ω`
constrained by (2) or (4); if those constraints were unsatisfiable the
theorems would be empty. They are not: for every `ϑ ∈ (0, π/2]` the constant
configuration is `ϑ`-bounded and satisfies condition (M) and the measurability
Proposition 3.5 assumes, and the plain jump kernel `|x − y|^{-d-α}` satisfies
both (2) and (4) with `Λ = 2`, because the indicator bracket never exceeds
`2`.
-/
import QuadraticFormsSobolev.Section3Kernel

open Real Set Metric MeasureTheory ENNReal

namespace QFS

variable {d : ℕ}

/-- The constant configuration with a fixed double cone. -/
def constConfig (V : DCone (EuclideanSpace ℝ (Fin d))) :
    Configuration (EuclideanSpace ℝ (Fin d)) := fun _ => V

lemma isBounded_constConfig {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) :
    IsBounded (constConfig ⟨v, hv, ϑ, hϑ, hϑ'⟩) ϑ := ⟨hϑ, fun _ => le_rfl⟩

/-- The constant configuration satisfies the measurability Proposition 3.5
assumes: `{x | V ⊆ Γ(x)}` is `∅` or everything. -/
lemma condMeas_constConfig (V : DCone (EuclideanSpace ℝ (Fin d))) :
    CondMeas (constConfig V) := by
  intro W
  by_cases h : W ⊆ V.carrier
  · have : {x : EuclideanSpace ℝ (Fin d) | W ⊆ (constConfig V x).carrier} = Set.univ := by
      ext x; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]; exact h
    rw [this]
    exact MeasurableSet.univ
  · have : {x : EuclideanSpace ℝ (Fin d) | W ⊆ (constConfig V x).carrier} = ∅ := by
      ext x; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]; exact h
    rw [this]
    exact MeasurableSet.empty

/-- The indicator bracket of (2) and (4) never exceeds `2`. -/
lemma indE_add_indE_le_two (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (x y : EuclideanSpace ℝ (Fin d)) :
    indE (coneAt Γ x) y + indE (coneAt Γ y) x ≤ 2 := by
  have h1 : indE (coneAt Γ x) y ≤ 1 := by
    by_cases h : y ∈ coneAt Γ x
    · rw [indE, Set.indicator_of_mem h]
    · rw [indE, Set.indicator_of_notMem h]; exact zero_le_one
  have h2 : indE (coneAt Γ y) x ≤ 1 := by
    by_cases h : x ∈ coneAt Γ y
    · rw [indE, Set.indicator_of_mem h]
    · rw [indE, Set.indicator_of_notMem h]; exact zero_le_one
  calc indE (coneAt Γ x) y + indE (coneAt Γ y) x ≤ 1 + 1 := add_le_add h1 h2
    _ = 2 := by norm_num

/-- **The hypotheses of (2) are satisfiable**: the plain jump kernel satisfies
assumption (2) for *every* configuration, with `Λ = 2`. -/
theorem kernelBounds_jumpKernel (Γ : Configuration (EuclideanSpace ℝ (Fin d))) (α : ℝ) :
    KernelBounds Γ α 2 (jumpKernel d α) where
  one_le := by norm_num
  symm := fun x y => by rw [jumpKernel, jumpKernel, norm_sub_rev]
  lower := by
    intro x y
    calc ENNReal.ofReal (2:ℝ)⁻¹ *
          ((indE (coneAt Γ x) y + indE (coneAt Γ y) x) * jumpKernel d α x y)
        ≤ ENNReal.ofReal (2:ℝ)⁻¹ * (2 * jumpKernel d α x y) :=
          mul_le_mul' le_rfl (mul_le_mul' (indE_add_indE_le_two Γ x y) le_rfl)
      _ = jumpKernel d α x y := by
          rw [← mul_assoc, show ENNReal.ofReal (2:ℝ)⁻¹ * 2 = 1 by
            rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by simp,
              ← ENNReal.ofReal_mul (by norm_num)]
            norm_num, one_mul]
  upper := by
    intro x y
    calc jumpKernel d α x y = 1 * jumpKernel d α x y := (one_mul _).symm
      _ ≤ ENNReal.ofReal (2:ℝ) * jumpKernel d α x y := by
          refine mul_le_mul' ?_ le_rfl
          rw [show (1:ℝ≥0∞) = ENNReal.ofReal (1:ℝ) by simp]
          exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- **The hypotheses of (4) are satisfiable**: the same kernel satisfies
assumption (4) for every configuration and every `R₀`, with `Λ = 2`. -/
theorem discreteKernelBounds_jumpKernel (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (α R₀ : ℝ) (L : Set (EuclideanSpace ℝ (Fin d))) :
    DiscreteKernelBounds Γ α 2 R₀ L (jumpKernel d α) where
  one_le := (kernelBounds_jumpKernel Γ α).one_le
  symm := fun x _ y _ => (kernelBounds_jumpKernel Γ α).symm x y
  lower := fun x _ y _ _ => (kernelBounds_jumpKernel Γ α).lower x y
  upper := fun x _ y _ _ => (kernelBounds_jumpKernel Γ α).upper x y

/-- **Theorem 1.3 is not vacuous**: its hypotheses are satisfiable for every
`ϑ ∈ (0, π/2]`, every `α ∈ (0,2)` and every `R₀ > 0`, in every dimension with a
unit vector. -/
theorem theoremOneThree_nonvacuous {ϑ α R₀ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) :
    ∃ (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
      (ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞),
      IsBounded Γ ϑ ∧ CondMeas Γ ∧ DiscreteKernelBounds Γ α 2 R₀ (lattice d) ω :=
  ⟨constConfig ⟨v, hv, ϑ, hϑ, hϑ'⟩, jumpKernel d α, isBounded_constConfig hϑ hϑ' hv,
    condMeas_constConfig _, discreteKernelBounds_jumpKernel _ α R₀ _⟩

end QFS
