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


/-! ## The last link: from the enlarged ball to Theorem 1.1

Section 3.2 ends by applying Lemma 7.1 with `Ω = B` a ball, turning the
enlarged-ball comparability `|f|_{H^{α/2}(B)} ≲ |f|_{H_k(B*)}` into the
same-ball one. That step is proved here, so the only unproved links in the
chain from the discrete theory to Theorem 1.1 are the ones the paper does not
prove either — plus §3.2's remaining inclusion. -/

/-- The input Lemma 7.1 quotes, specialised to `Ω` a ball: a countable Whitney
family whose `κ`-enlargements lie inside the ball and overlap at most
`overlapBound` times, together with the constant of Dyda's inequality (13). The
paper proves none of this — the family is produced by "the Whitney decomposition
technique" and the inequality is quoted from [Dyda06] — so it is carried as data
rather than derived. -/
structure WhitneyBallData (d : ℕ) (α κ : ℝ) where
  /-- The index set of the family; a Whitney family is countable. -/
  idx : Type
  /-- Countability of the index set. -/
  countable : Countable idx
  /-- The bound `M` of the finite-overlap property (iii). -/
  overlapBound : ℕ
  /-- A nonempty family overlaps at least once. -/
  overlapBound_pos : 0 < overlapBound
  /-- The constant of Dyda's inequality (13). -/
  dydaConst : ℝ
  /-- Dyda's constant is positive. -/
  dydaConst_pos : 0 < dydaConst
  /-- The centres of the Whitney balls for the ball `B_R(x₀)`. -/
  ctr : EuclideanSpace ℝ (Fin d) → ℝ → idx → EuclideanSpace ℝ (Fin d)
  /-- The radii of the Whitney balls for the ball `B_R(x₀)`. -/
  rad : EuclideanSpace ℝ (Fin d) → ℝ → idx → ℝ
  /-- Property (ii): the enlarged balls stay inside `Ω`. -/
  enlarged_subset : ∀ x₀ R, 0 < R → ∀ i,
    ball (ctr x₀ R i) (κ * rad x₀ R i) ⊆ ball x₀ R
  /-- Property (iii): the enlarged balls overlap at most `overlapBound` times. -/
  overlap : ∀ x₀ R, 0 < R → ∀ y,
    {i | y ∈ ball (ctr x₀ R i) (κ * rad x₀ R i)}.encard ≤ (overlapBound : ℕ∞)
  /-- Inequality (13) of [Dyda06], as used in the last step of (6.14). -/
  dyda : ∀ x₀ R, 0 < R → ∀ f, ENNReal.ofReal dydaConst * formHs (ball x₀ R) α f
    ≤ ∑' i, formHs (ball (ctr x₀ R i) (rad x₀ R i)) α f

/-- **The chain (6.14) for a single ball**, taking the enlarged-ball
comparability as an input for one fixed kernel and one fixed function.

This is the content of the passage from `B*` to `B`; the two theorems below are
instances of it, one for the paper's `QFS.TheoremOneOneBall` and one for the
variant this formalisation proves.

The measurability hypothesis on the integrand is where the paper's assumption
that `k` be measurable — which `QFS.KernelBounds` drops, see Deviation 20 — is
actually needed: without it the family of integrals over the Whitney balls
cannot be summed. -/
theorem formHs_le_form_of_ballComparability {α κ c₀ : ℝ} (hκ : 1 ≤ κ) (hc₀ : 1 ≤ c₀)
    (W : WhitneyBallData d α κ)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (H : ∀ (y₀ : EuclideanSpace ℝ (Fin d)) (S : ℝ), 0 < S →
      MemLp f 2 (volume.restrict (ball y₀ (κ * S))) →
      formHs (ball y₀ S) α f ≤ ENNReal.ofReal c₀ * form (ball y₀ (κ * S)) k f)
    (hf : ∀ (y₀ : EuclideanSpace ℝ (Fin d)) (S : ℝ), 0 < S →
      MemLp f 2 (volume.restrict (ball y₀ S)))
    (hFmeas : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2)
    (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ) (hR : 0 < R) :
    ENNReal.ofReal (c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ)) * formHs (ball x₀ R) α f
      ≤ form (ball x₀ R) k f := by
  have hcount := W.countable
  have hc₀pos : (0 : ℝ) < c₀ := lt_of_lt_of_le zero_lt_one hc₀
  have hMR : (0 : ℝ) < (W.overlapBound : ℝ) := by exact_mod_cast W.overlapBound_pos
  have hM0 : W.overlapBound ≠ 0 := by have := W.overlapBound_pos; omega
  have hMne : ((W.overlapBound : ℕ) : ℝ≥0∞) ≠ 0 := by simpa using hM0
  have hMtop : ((W.overlapBound : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  -- the enlarged-ball comparability, renormalised so the constant sits on the left
  have hball : ∀ i, ENNReal.ofReal c₀⁻¹ * formHs (ball (W.ctr x₀ R i) (W.rad x₀ R i)) α f
      ≤ form (ball (W.ctr x₀ R i) (κ * W.rad x₀ R i)) k f := by
    intro i
    by_cases hri : 0 < W.rad x₀ R i
    · have h2 := H (W.ctr x₀ R i) (W.rad x₀ R i) hri (hf _ _ (by nlinarith))
      calc ENNReal.ofReal c₀⁻¹ * formHs (ball (W.ctr x₀ R i) (W.rad x₀ R i)) α f
          ≤ ENNReal.ofReal c₀⁻¹ * (ENNReal.ofReal c₀ *
              form (ball (W.ctr x₀ R i) (κ * W.rad x₀ R i)) k f) := mul_le_mul' le_rfl h2
        _ = form (ball (W.ctr x₀ R i) (κ * W.rad x₀ R i)) k f := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hc₀pos)),
              inv_mul_cancel₀ (ne_of_gt hc₀pos), ENNReal.ofReal_one, one_mul]
    · have hempty : ball (W.ctr x₀ R i) (W.rad x₀ R i) = ∅ :=
        ball_eq_empty.mpr (not_lt.mp hri)
      simp [formHs, form, hempty]
  -- the chain (6.14)
  have hchain := lemma_ball_to_domain (S := fun i => ball (W.ctr x₀ R i) (W.rad x₀ R i))
    (S' := fun i => ball (W.ctr x₀ R i) (κ * W.rad x₀ R i)) (Ω := ball x₀ R)
    (M := W.overlapBound) (α := α) (c := c₀⁻¹) (c' := W.dydaConst) (k := k) (f := f)
    (fun i => measurableSet_ball) measurableSet_ball
    (W.enlarged_subset x₀ R hR) (W.overlap x₀ R hR) hFmeas hball (W.dyda x₀ R hR f)
  -- divide by the overlap bound
  have hdiv := mul_le_mul' (le_refl (((W.overlapBound : ℕ) : ℝ≥0∞)⁻¹)) hchain
  have hRHS : ((W.overlapBound : ℕ) : ℝ≥0∞)⁻¹ *
      (((W.overlapBound : ℕ) : ℝ≥0∞) * form (ball x₀ R) k f) = form (ball x₀ R) k f := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel hMne hMtop, one_mul]
  rw [hRHS] at hdiv
  refine le_trans (le_of_eq ?_) hdiv
  rw [ENNReal.ofReal_div_of_pos hMR, ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hc₀pos)),
    ENNReal.ofReal_natCast, div_eq_mul_inv]
  ring
/-- **Theorem 1.1 from its enlarged-ball form**, by Lemma 7.1 applied to a ball. -/
theorem formHs_le_form_of_theoremOneOneBall (h : TheoremOneOneBall d)
    {ϑ Λ α : ℝ} (hϑ : 0 < ϑ) (hΛ : 1 ≤ Λ) (hα : 0 < α) (hα2 : α < 2)
    (hW : ∀ κ : ℝ, 1 ≤ κ → Nonempty (WhitneyBallData d α κ)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsAdmissible Γ ϑ →
      ∀ k, KernelBounds Γ α Λ k →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ (y₀ : EuclideanSpace ℝ (Fin d)) (S : ℝ), 0 < S →
          MemLp f 2 (volume.restrict (ball y₀ S))) →
        (Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
        ENNReal.ofReal c * formHs (ball x₀ R) α f ≤ form (ball x₀ R) k f := by
  obtain ⟨κ, c₀, hκ, hc₀, H⟩ := h ϑ Λ α hϑ hΛ hα hα2
  obtain ⟨W⟩ := hW κ hκ
  have hc₀pos : (0 : ℝ) < c₀ := lt_of_lt_of_le zero_lt_one hc₀
  have hMR : (0 : ℝ) < (W.overlapBound : ℝ) := by exact_mod_cast W.overlapBound_pos
  refine ⟨c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ),
    div_pos (mul_pos (inv_pos.mpr hc₀pos) W.dydaConst_pos) hMR, ?_⟩
  intro Γ hΓ k hk f hf hFmeas x₀ R hR
  exact formHs_le_form_of_ballComparability hκ hc₀ W
    (fun y₀ S hS hmem => H Γ hΓ k hk y₀ S hS f hmem) hf hFmeas x₀ R hR


/-- **The Whitney data is satisfiable**, so the theorem above is not vacuous: for
`κ = 1` the one-element family consisting of the ball itself has all the required
properties, with overlap `1` and Dyda constant `1`.

For `κ > 1` a genuine Whitney decomposition is needed, and that is precisely what
the paper quotes rather than proves. -/
noncomputable def whitneyBallData_one (d : ℕ) (α : ℝ) : WhitneyBallData d α 1 where
  idx := Unit
  countable := inferInstance
  overlapBound := 1
  overlapBound_pos := one_pos
  dydaConst := 1
  dydaConst_pos := one_pos
  ctr := fun x₀ _ _ => x₀
  rad := fun _ R _ => R
  enlarged_subset := by intro x₀ R _ i; simp
  overlap := by
    intro x₀ R _ y
    refine le_trans (Set.encard_le_encard (Set.subset_univ _)) ?_
    simp [Set.encard_univ]
  dyda := by intro x₀ R _ f; simp

end QFS
