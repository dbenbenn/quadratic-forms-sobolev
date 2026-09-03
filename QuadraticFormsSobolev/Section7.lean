import QuadraticFormsSobolev.Section32

/-!
# Section 7: the auxiliary lemmas, and Theorem 1.4 on `ℝ^d`

Two results downstream of Theorem 1.1 that do not need Section 3.2's open step.

* **Theorem 1.4 on the whole space.** The paper obtains it from Lemma 3.7 "in
  the limit `R → ∞` using monotone convergence", the point being that the
  comparability constant does not depend on the ball. That deduction is proved
  here, conditionally on Theorem 1.1 (`theoremOneFourUniv_of_theoremOneOne`).

* **The chain (6.14) inside Lemma 7.1.** Lemma 7.1 passes from balls to a
  bounded Lipschitz domain using a Whitney family and Dyda's inequality (13),
  both quoted rather than proved. The one step the paper carries out itself is
  the finite-overlap estimate, and it is proved here
  (`tsum_setLIntegral_le_of_overlap`); `lemma_ball_to_domain` then assembles the
  whole chain with the two quoted inputs as explicit hypotheses.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology

namespace QFS

variable {d : ℕ}

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

/-- The reverse comparison on `ℝ^d` is the reverse inequality of (1.5). -/
theorem form_univ_le_formHs_univ {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {α Λ : ℝ}
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    form Set.univ k f ≤ ENNReal.ofReal Λ * formHs Set.univ α f :=
  form_le_formHs hk _ _

/-! ## The finite-overlap step of Lemma 7.1

Lemma 7.1's proof runs the chain (6.14). Its first inequality is the only step
carried out in the paper rather than quoted: if the enlarged Whitney balls `B*`
lie in `Ω` and no point lies in more than `M` of them, the sum of the forms over
the `B*` is controlled by the form over `Ω`. -/

/-- **Finite overlap.** If each `S i` lies in `Ω` and no point of `ℝ^d` lies in
more than `M` of the `S i`, then `∑ᵢ ∫_{Sᵢ×Sᵢ} F ≤ M ∫_{Ω×Ω} F`.

The paper's display (6.14) uses the factor `M²`; `M` already suffices, since a
pair `(x,y)` lies in `Sᵢ × Sᵢ` only for those `i` with `x ∈ Sᵢ`, of which there
are at most `M`. See `tsum_setLIntegral_le_of_overlap_sq` for the paper's form. -/
theorem tsum_setLIntegral_le_of_overlap {ι : Type} [Countable ι]
    {S : ι → Set (EuclideanSpace ℝ (Fin d))} {Ω : Set (EuclideanSpace ℝ (Fin d))} {M : ℕ}
    (hSm : ∀ i, MeasurableSet (S i)) (hΩ : MeasurableSet Ω) (hsub : ∀ i, S i ⊆ Ω)
    (hM : ∀ x, {i | x ∈ S i}.encard ≤ (M : ℕ∞))
    {F : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hF : Measurable F) :
    ∑' i, ∫⁻ p in S i ×ˢ S i, F p ≤ (M : ℝ≥0∞) * ∫⁻ p in Ω ×ˢ Ω, F p := by
  have hprodm : ∀ i, MeasurableSet (S i ×ˢ S i) := fun i => (hSm i).prod (hSm i)
  -- rewrite each set integral as an integral of an indicator, and exchange
  have hswap : ∑' i, ∫⁻ p in S i ×ˢ S i, F p
      = ∫⁻ p, ∑' i, (S i ×ˢ S i).indicator F p := by
    rw [lintegral_tsum (fun i => ((hF.indicator (hprodm i)).aemeasurable))]
    exact tsum_congr fun i => (lintegral_indicator (hprodm i) _).symm
  -- the pointwise bound
  have hpt : ∀ p, ∑' i, (S i ×ˢ S i).indicator F p ≤ (M : ℝ≥0∞) * (Ω ×ˢ Ω).indicator F p := by
    intro p
    set T : Set ι := {i | p ∈ S i ×ˢ S i} with hT
    have hTsub : T ⊆ {i | p.1 ∈ S i} := fun i hi => hi.1
    have hTcard : T.encard ≤ (M : ℕ∞) := le_trans (Set.encard_mono hTsub) (hM p.1)
    have hsupp : Function.support (fun i => (S i ×ˢ S i).indicator F p) ⊆ T := by
      intro i hi
      by_contra hiT
      have hp : p ∉ S i ×ˢ S i := hiT
      exact hi (Set.indicator_of_notMem hp F)
    have hval : ∀ i : T, (S i.1 ×ˢ S i.1).indicator F p = F p := by
      rintro ⟨i, hi⟩
      have hp : p ∈ S i ×ˢ S i := hi
      exact Set.indicator_of_mem hp F
    have hsum : ∑' i, (S i ×ˢ S i).indicator F p = (T.encard : ℝ≥0∞) * F p := by
      rw [← tsum_subtype_eq_of_support_subset hsupp, tsum_congr hval,
        ENNReal.tsum_set_const]
    rcases Set.eq_empty_or_nonempty T with hTe | ⟨i₀, hi₀⟩
    · simp [hsum, hTe]
    · have hpΩ : p ∈ Ω ×ˢ Ω := ⟨hsub i₀ hi₀.1, hsub i₀ hi₀.2⟩
      rw [hsum, Set.indicator_of_mem hpΩ F]
      exact mul_le_mul' (by exact_mod_cast hTcard) le_rfl
  calc ∑' i, ∫⁻ p in S i ×ˢ S i, F p
      = ∫⁻ p, ∑' i, (S i ×ˢ S i).indicator F p := hswap
    _ ≤ ∫⁻ p, (M : ℝ≥0∞) * (Ω ×ˢ Ω).indicator F p := lintegral_mono hpt
    _ = (M : ℝ≥0∞) * ∫⁻ p in Ω ×ˢ Ω, F p := by
        rw [lintegral_const_mul _ (hF.indicator (hΩ.prod hΩ)), lintegral_indicator (hΩ.prod hΩ)]


/-- The paper's form of the finite-overlap estimate, with the factor `M²` of
display (6.14). -/
theorem tsum_setLIntegral_le_of_overlap_sq {ι : Type} [Countable ι]
    {S : ι → Set (EuclideanSpace ℝ (Fin d))} {Ω : Set (EuclideanSpace ℝ (Fin d))} {M : ℕ}
    (hSm : ∀ i, MeasurableSet (S i)) (hΩ : MeasurableSet Ω) (hsub : ∀ i, S i ⊆ Ω)
    (hM : ∀ x, {i | x ∈ S i}.encard ≤ (M : ℕ∞)) (hM1 : 1 ≤ M)
    {F : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hF : Measurable F) :
    ∑' i, ∫⁻ p in S i ×ˢ S i, F p ≤ ((M : ℝ≥0∞)) ^ 2 * ∫⁻ p in Ω ×ˢ Ω, F p := by
  refine le_trans (tsum_setLIntegral_le_of_overlap hSm hΩ hsub hM hF) ?_
  refine mul_le_mul' ?_ le_rfl
  have : (M : ℝ≥0∞) * 1 ≤ (M : ℝ≥0∞) * (M : ℝ≥0∞) :=
    mul_le_mul' le_rfl (by exact_mod_cast hM1)
  simpa [sq] using this

/-- **The chain (6.14) of Lemma 7.1**, the one part of that lemma the paper
carries out rather than quotes.

The two quoted inputs appear as hypotheses: `hsub` and `hM` are properties (ii)
and (iii) of the Whitney family, and `hdyda` is inequality (13) of [Dyda06].
`hball` is the comparability on balls that Lemma 7.1 assumes. The conclusion is
the comparability on `Ω`, with the constant `c·c'/M` that (6.14) produces. -/
theorem lemma_ball_to_domain {ι : Type} [Countable ι]
    {S S' : ι → Set (EuclideanSpace ℝ (Fin d))} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {M : ℕ} {α c c' : ℝ}
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hS'm : ∀ i, MeasurableSet (S' i)) (hΩ : MeasurableSet Ω)
    (hsub : ∀ i, S' i ⊆ Ω)
    (hM : ∀ x, {i | x ∈ S' i}.encard ≤ (M : ℕ∞))
    (hF : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2)
    (hball : ∀ i, ENNReal.ofReal c * formHs (S i) α f ≤ form (S' i) k f)
    (hdyda : ENNReal.ofReal c' * formHs Ω α f ≤ ∑' i, formHs (S i) α f) :
    ENNReal.ofReal c * (ENNReal.ofReal c' * formHs Ω α f) ≤ (M : ℝ≥0∞) * form Ω k f := by
  calc ENNReal.ofReal c * (ENNReal.ofReal c' * formHs Ω α f)
      ≤ ENNReal.ofReal c * ∑' i, formHs (S i) α f := mul_le_mul' le_rfl hdyda
    _ = ∑' i, ENNReal.ofReal c * formHs (S i) α f := ENNReal.tsum_mul_left.symm
    _ ≤ ∑' i, form (S' i) k f := ENNReal.tsum_le_tsum hball
    _ ≤ (M : ℝ≥0∞) * form Ω k f :=
        tsum_setLIntegral_le_of_overlap hS'm hΩ hsub hM hF

end QFS
