/-
Section 1 of Bux–Kassmann–Schulze: the quadratic forms, the function spaces
`H_k(Ω)` and `H^{α/2}(Ω)`, assumption (1.4) on the kernel, the reverse
inequality of Theorem 1.1 (which "trivially holds"), and the inclusion (1.6).

The two main theorems are also *stated* here, as `Prop`s, so that the targets
are precise and type-checked. `QFS.TheoremOneThree` is proved in `Section6`;
`QFS.TheoremOneOne` is not, and the README records what it still needs.
-/
import QuadraticFormsSobolev.Section5

open Real Set Metric MeasureTheory ENNReal

namespace QFS

variable {d : ℕ}

/-! ## The kernels and the quadratic forms -/

/-- The kernel `|x − y|^{-d-α}` of the `H^{α/2}` seminorm (1.1). -/
noncomputable def jumpKernel (d : ℕ) (α : ℝ) (x y : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ENNReal.ofReal (‖x - y‖ ^ (-(d : ℝ) - α))

/-- The indicator of a set, valued in `ℝ≥0∞`. -/
noncomputable def indE (S : Set (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) :
    ℝ≥0∞ := S.indicator (fun _ => 1) x

/-- The quadratic form `∫_{Ω×Ω} (f(y) − f(x))² k(x,y) d(x,y)` of Section 1.

The paper writes this integral as `|f|_{H_k(Ω)}` and then uses `|f|²_{H_k(Ω)}`
in the definition of the norm; we name the integral itself, which is the
quantity both readings agree on. -/
noncomputable def form (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  ∫⁻ p in Ω ×ˢ Ω, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2

/-- The `H^{α/2}(Ω)` form, i.e. the seminorm (1.1) restricted to `Ω`. -/
noncomputable def formHs (Ω : Set (EuclideanSpace ℝ (Fin d))) (α : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  form Ω (jumpKernel d α) f

/-! ## Assumption (1.4) -/

/-- Assumption (1.4) of Theorem 1.1: `k` is symmetric and satisfies

  `Λ⁻¹ (1_{V^Γ[x]}(y) + 1_{V^Γ[y]}(x)) |x−y|^{-d-α} ≤ k(x,y) ≤ Λ |x−y|^{-d-α}`. -/
structure KernelBounds (Γ : Configuration (EuclideanSpace ℝ (Fin d))) (α Λ : ℝ)
    (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞) : Prop where
  /-- The constant `Λ` is at least one. -/
  one_le : 1 ≤ Λ
  /-- `k` is symmetric. -/
  symm : ∀ x y, k x y = k y x
  /-- The lower bound, which sees only the double cones of `Γ`. -/
  lower : ∀ x y, ENNReal.ofReal Λ⁻¹ *
      ((indE (coneAt Γ x) y + indE (coneAt Γ y) x) * jumpKernel d α x y) ≤ k x y
  /-- The upper bound. -/
  upper : ∀ x y, k x y ≤ ENNReal.ofReal Λ * jumpKernel d α x y

/-! ## The reverse inequality, and the inclusion (1.6) -/

/-- The upper bound in (1.4) makes the `H^{α/2}` form dominate the `H_k` form on
every set. This is both the "reverse inequality in (1.5)", which the paper notes
"trivially holds true", and the inequality behind the inclusion (1.6). -/
theorem form_le_formHs {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {α Λ : ℝ}
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    form Ω k f ≤ ENNReal.ofReal Λ * formHs Ω α f := by
  have hstep : ∀ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2
        ≤ ENNReal.ofReal Λ *
          (ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2) := by
    intro p
    calc ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2
        ≤ ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
            (ENNReal.ofReal Λ * jumpKernel d α p.1 p.2) :=
          mul_le_mul' (le_refl _) (hk.upper _ _)
      _ = ENNReal.ofReal Λ *
            (ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2) := by ring
  calc form Ω k f
      ≤ ∫⁻ p in Ω ×ˢ Ω, ENNReal.ofReal Λ *
          (ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2) :=
        lintegral_mono (fun p => hstep p)
    _ = ENNReal.ofReal Λ * formHs Ω α f :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- `H_k(Ω) = {f ∈ L²(Ω) | |f|_{H_k(Ω)} < ∞}`. -/
def Hk (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    Set (EuclideanSpace ℝ (Fin d) → ℝ) :=
  {f | MemLp f 2 (volume.restrict Ω) ∧ form Ω k f ≠ ⊤}

/-- `H^{α/2}(Ω) = {f ∈ L²(Ω) | |f|_{H^{α/2}(Ω)} < ∞}`. -/
def Hs (Ω : Set (EuclideanSpace ℝ (Fin d))) (α : ℝ) :
    Set (EuclideanSpace ℝ (Fin d) → ℝ) :=
  {f | MemLp f 2 (volume.restrict Ω) ∧ formHs Ω α f ≠ ⊤}

/-- **Equation (1.6)**: `H^{α/2}(Ω) ⊆ H_k(Ω)`. -/
theorem Hs_subset_Hk {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {α Λ : ℝ}
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    Hs Ω α ⊆ Hk Ω k := by
  rintro f ⟨hmem, hfin⟩
  refine ⟨hmem, ?_⟩
  refine ne_top_of_le_ne_top ?_ (form_le_formHs hk Ω f)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin

/-! ## The statements of Theorems 1.1 and 1.3

These are recorded as `Prop`s so that the targets are precise and type-checked.
`QFS.TheoremOneThree` is proved as `QFS.theoremOneThree` in `Section6`, on top
of Theorem 5.15. `QFS.TheoremOneOne` is not proved: it needs Section 3's
discrete kernel and limiting argument, and a final step the paper quotes from a
Whitney decomposition. See the README. -/

/-- The statement of **Theorem 1.1**. The constant `c` is quantified before `Γ`
and `k`, which is the paper's assertion that it depends only on `Λ`, `d` and
`ϑ`. -/
def TheoremOneOne (d : ℕ) : Prop :=
  ∀ ϑ Λ α : ℝ, 0 < ϑ → 1 ≤ Λ → 0 < α → α < 2 →
    ∃ c : ℝ, 1 ≤ c ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsAdmissible Γ ϑ →
      ∀ k, KernelBounds Γ α Λ k →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        MemLp f 2 (volume.restrict (ball x₀ R)) →
        formHs (ball x₀ R) α f ≤ ENNReal.ofReal c * form (ball x₀ R) k f

/-- The refinement recorded after Theorem 1.1: for `0 < α₀ ≤ α < 2` the constant
`c` depends on `α₀` but not on `α`. -/
def TheoremOneOneUniform (d : ℕ) : Prop :=
  ∀ ϑ Λ α₀ : ℝ, 0 < ϑ → 1 ≤ Λ → 0 < α₀ →
    ∃ c : ℝ, 1 ≤ c ∧
      ∀ α : ℝ, α₀ ≤ α → α < 2 →
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsAdmissible Γ ϑ →
      ∀ k, KernelBounds Γ α Λ k →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        MemLp f 2 (volume.restrict (ball x₀ R)) →
        formHs (ball x₀ R) α f ≤ ENNReal.ofReal c * form (ball x₀ R) k f

/-- The comparability **with an enlarged ball**, which is what Section 3.2's
limiting argument delivers:

  `|f|_{H^{α/2}(B_R)} ≤ c |f|_{H_k(B_{κR})}`.

Theorem 1.1 is this with `κ = 1`, and the paper gets there by the appendix lemma
(its version of [DyKa15, Lemma 6.9]), whose proof rests on a Whitney
decomposition and on inequality (13) of [Dyda06] — neither proved in the paper.
Recording the enlarged-ball form separately pins down what Section 3 alone
would give. -/
def TheoremOneOneBall (d : ℕ) : Prop :=
  ∀ ϑ Λ α : ℝ, 0 < ϑ → 1 ≤ Λ → 0 < α → α < 2 →
    ∃ κ c : ℝ, 1 ≤ κ ∧ 1 ≤ c ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsAdmissible Γ ϑ →
      ∀ k, KernelBounds Γ α Λ k →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        MemLp f 2 (volume.restrict (ball x₀ (κ * R))) →
        formHs (ball x₀ R) α f ≤ ENNReal.ofReal c * form (ball x₀ (κ * R)) k f

/-- The discrete quadratic form of Theorem 1.3: the sum over pairs of lattice
points of `S` at distance more than `R₀`. -/
noncomputable def discreteForm (S : Set (EuclideanSpace ℝ (Fin d))) (R₀ : ℝ)
    (ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  ∑' p : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
      p.1 ∈ S ∩ lattice d ∧ p.2 ∈ S ∩ lattice d ∧ R₀ < ‖p.1 - p.2‖},
    ENNReal.ofReal ((f p.1.1 - f p.1.2) ^ 2) * ω p.1.1 p.1.2

/-- Assumption (1.7) of Theorem 1.3: the two-sided bound on `ω`, imposed only for
`|x − y| > R₀`. -/
structure DiscreteKernelBounds (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (α Λ R₀ : ℝ) (ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    Prop where
  /-- The constant `Λ` is at least one. -/
  one_le : 1 ≤ Λ
  /-- `ω` is symmetric. -/
  symm : ∀ x y, ω x y = ω y x
  /-- The lower bound, for `|x − y| > R₀`. -/
  lower : ∀ x y, R₀ < ‖x - y‖ → ENNReal.ofReal Λ⁻¹ *
      ((indE (coneAt Γ x) y + indE (coneAt Γ y) x) * jumpKernel d α x y) ≤ ω x y
  /-- The upper bound, for `|x − y| > R₀`. -/
  upper : ∀ x y, R₀ < ‖x - y‖ → ω x y ≤ ENNReal.ofReal Λ * jumpKernel d α x y

/-- The statement of **Theorem 1.3**, the discrete main theorem. The paper
quantifies over functions on `B_{κR}(x₀) ∩ ℤ^d`; since both forms read `f` only
at lattice points of the relevant balls, quantifying over functions on all of
`ℝ^d` is equivalent. -/
def TheoremOneThree (d : ℕ) : Prop :=
  ∀ ϑ Λ α R₀ : ℝ, 0 < ϑ → 1 ≤ Λ → 0 < α → α < 2 → 0 < R₀ →
    ∃ κ c : ℝ, 1 ≤ κ ∧ 1 ≤ c ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ →
      ∀ ω, DiscreteKernelBounds Γ α Λ R₀ ω →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ), 0 < R →
        discreteForm (ball x₀ R) R₀ (jumpKernel d α) f
          ≤ ENNReal.ofReal c * discreteForm (ball x₀ (κ * R)) R₀ ω f

end QFS
