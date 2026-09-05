/-
Section 1 of Bux–Kassmann–Schulze: the quadratic forms, the function spaces
`H_k(Ω)` and `H^{α/2}(Ω)`, assumption (2) on the kernel, the reverse
inequality of Theorem 1.1 (which "trivially holds"), and the inclusion (5).

The two main theorems are also *stated* here, as `Prop`s, so that the targets
are precise and type-checked. `QFS.TheoremOneThree` is proved in `Section6`;
`QFS.TheoremOneOne` is not, and the README records what it still needs.

Theorem 1.4 on `ℝ^d` closes the file. The paper obtains it from Lemma 3.7 "in
the limit `R → ∞` using monotone convergence", the point being that the
comparability constant does not depend on the ball. That deduction needs nothing
from Section 3.2 beyond Theorem 1.1 itself, so it is proved here, conditionally
(`QFS.theoremOneFourUniv_of_theoremOneOne`).
-/
import QuadraticFormsSobolev.Section5

open Real Set Metric MeasureTheory ENNReal

namespace QFS

variable {d : ℕ}

/-! ## The kernels and the quadratic forms -/

/-- The kernel `|x − y|^{-d-α}` of the `H^{α/2}` seminorm (1). -/
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

/-- The `H^{α/2}(Ω)` form, i.e. the seminorm (1) restricted to `Ω`. -/
noncomputable def formHs (Ω : Set (EuclideanSpace ℝ (Fin d))) (α : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  form Ω (jumpKernel d α) f

/-! ## Assumption (2) -/

/-- Assumption (2) of Theorem 1.1: `k` is symmetric and satisfies

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

/-! ## The reverse inequality, and the inclusion (5) -/

/-- The upper bound in (2) makes the `H^{α/2}` form dominate the `H_k` form on
every set. This is both the "reverse inequality in (3)", which the paper notes
"trivially holds true", and the inequality behind the inclusion (5). -/
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

/-- **Equation (5)**: `H^{α/2}(Ω) ⊆ H_k(Ω)`. -/
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

/-- Assumption (4) of Theorem 1.3: the two-sided bound on `ω`, imposed only for
`|x − y| > R₀` **and only at pairs of points of the lattice `L`**. The paper's `ω`
is a function on `ℤ^d × ℤ^d` (on `hℤ^d × hℤ^d` in Corollary 3.1), so asking the
bounds off the lattice would be a genuine strengthening of the hypothesis: at a
pair where both indicators fire the two bounds force `Λ ≥ √2`, so for
`Λ ∈ [1, √2)` an off-lattice mutually-coned pair would make the hypothesis
unsatisfiable. -/
structure DiscreteKernelBounds (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (α Λ R₀ : ℝ) (L : Set (EuclideanSpace ℝ (Fin d)))
    (ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    Prop where
  /-- The constant `Λ` is at least one. -/
  one_le : 1 ≤ Λ
  /-- `ω` is symmetric on `L`. -/
  symm : ∀ x ∈ L, ∀ y ∈ L, ω x y = ω y x
  /-- The lower bound, for `|x − y| > R₀`. -/
  lower : ∀ x ∈ L, ∀ y ∈ L, R₀ < ‖x - y‖ → ENNReal.ofReal Λ⁻¹ *
      ((indE (coneAt Γ x) y + indE (coneAt Γ y) x) * jumpKernel d α x y) ≤ ω x y
  /-- The upper bound, for `|x − y| > R₀`. -/
  upper : ∀ x ∈ L, ∀ y ∈ L, R₀ < ‖x - y‖ → ω x y ≤ ENNReal.ofReal Λ * jumpKernel d α x y

/-- The statement of **Theorem 1.3**, the discrete main theorem. The paper
quantifies over functions on `B_{κR}(x₀) ∩ ℤ^d`; since both forms read `f` only
at lattice points of the relevant balls, quantifying over functions on all of
`ℝ^d` is equivalent. -/
def TheoremOneThree (d : ℕ) : Prop :=
  ∀ ϑ Λ α R₀ : ℝ, 0 < ϑ → 1 ≤ Λ → 0 < α → α < 2 → 0 < R₀ →
    ∃ κ c : ℝ, 1 ≤ κ ∧ 1 ≤ c ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ →
      ∀ ω, DiscreteKernelBounds Γ α Λ R₀ (lattice d) ω →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ), 0 < R →
        discreteForm (ball x₀ R) R₀ (jumpKernel d α) f
          ≤ ENNReal.ofReal c * discreteForm (ball x₀ (κ * R)) R₀ ω f

/-! ## Theorem 1.4 on `ℝ^d` -/

/-- Theorem 1.4 for `Ω = ℝ^d`: the seminorms `|·|_{H^{α/2}(ℝ^d)}` and
`|·|_{H_k(ℝ^d)}` are comparable. The paper deduces this from Lemma 3.7 by
letting `R → ∞`, which is legitimate exactly because the constant there does not
depend on the ball. -/
def TheoremOneFourUniv (d : ℕ) : Prop :=
  ∀ ϑ Λ α : ℝ, 0 < ϑ → 1 ≤ Λ → 0 < α → α < 2 →
    ∃ c : ℝ, 1 ≤ c ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsAdmissible Γ ϑ →
      ∀ k, KernelBounds Γ α Λ k →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
          MemLp f 2 (volume.restrict (ball x₀ R))) →
        formHs Set.univ α f ≤ ENNReal.ofReal c * form Set.univ k f

/-- An integral over `ℝ^d × ℝ^d` is the supremum of the integrals over
`B_n(0) × B_n(0)`. -/
theorem lintegral_univ_prod_eq_iSup
    (F : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    ∫⁻ p in Set.univ ×ˢ Set.univ, F p
      = ⨆ n : ℕ, ∫⁻ p in ball (0 : EuclideanSpace ℝ (Fin d)) (n + 1) ×ˢ
          ball (0 : EuclideanSpace ℝ (Fin d)) (n + 1), F p := by
  have hdir : Directed (· ⊆ ·) (fun n : ℕ =>
      ball (0 : EuclideanSpace ℝ (Fin d)) (n + 1) ×ˢ
        ball (0 : EuclideanSpace ℝ (Fin d)) (n + 1)) := by
    intro m n
    have hm : (m : ℝ) + 1 ≤ ((max m n : ℕ) : ℝ) + 1 := by
      have : (m : ℝ) ≤ ((max m n : ℕ) : ℝ) := by exact_mod_cast Nat.le_max_left m n
      linarith
    have hn : (n : ℝ) + 1 ≤ ((max m n : ℕ) : ℝ) + 1 := by
      have : (n : ℝ) ≤ ((max m n : ℕ) : ℝ) := by exact_mod_cast Nat.le_max_right m n
      linarith
    exact ⟨max m n, Set.prod_mono (ball_subset_ball hm) (ball_subset_ball hm),
      Set.prod_mono (ball_subset_ball hn) (ball_subset_ball hn)⟩
  have hcover : (⋃ n : ℕ, ball (0 : EuclideanSpace ℝ (Fin d)) (n + 1) ×ˢ
      ball (0 : EuclideanSpace ℝ (Fin d)) (n + 1)) = Set.univ ×ˢ Set.univ := by
    rw [Set.univ_prod_univ]
    refine Set.eq_univ_of_forall fun p => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt (max ‖p.1‖ ‖p.2‖)
    refine Set.mem_iUnion.mpr ⟨n, ?_, ?_⟩ <;>
      simp only [mem_ball, dist_zero_right] <;>
      [exact lt_of_le_of_lt (le_max_left _ _) (by push_cast; linarith);
       exact lt_of_le_of_lt (le_max_right _ _) (by push_cast; linarith)]
  rw [← hcover, setLIntegral_iUnion_of_directed _ hdir]

/-- The `H_k` form on `ℝ^d` is the supremum of the forms on balls about the
origin. -/
theorem form_univ_eq_iSup (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    form Set.univ k f = ⨆ n : ℕ, form (ball (0 : EuclideanSpace ℝ (Fin d)) ((n : ℝ) + 1)) k f :=
  lintegral_univ_prod_eq_iSup _

/-- **Theorem 1.4 on `ℝ^d`, granted Theorem 1.1.** -/
theorem theoremOneFourUniv_of_theoremOneOne (h : TheoremOneOne d) : TheoremOneFourUniv d := by
  intro ϑ Λ α hϑ hΛ hα hα2
  obtain ⟨c, hc, H⟩ := h ϑ Λ α hϑ hΛ hα hα2
  refine ⟨c, hc, ?_⟩
  intro Γ hΓ k hk f hf
  simp only [formHs]
  rw [form_univ_eq_iSup, form_univ_eq_iSup, ENNReal.mul_iSup]
  refine iSup_mono fun n => ?_
  have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact H Γ hΓ k hk 0 ((n : ℝ) + 1) hR f (hf 0 _ hR)

/-- The reverse comparison on `ℝ^d` is the reverse inequality of (3). -/
theorem form_univ_le_formHs_univ {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {α Λ : ℝ}
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    form Set.univ k f ≤ ENNReal.ofReal Λ * formHs Set.univ α f :=
  form_le_formHs hk _ _

end QFS
