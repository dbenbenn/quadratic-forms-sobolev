/-
Section 5.3 of Bux–Kassmann–Schulze, "Connecting Points at Scale": the scale
step `Δ`, and Lemma 5.16, which connects an arbitrary point to a whole block of
the town at the appropriate scale.
-/
import QuadraticFormsSobolev.Renormalization

open Real Set Metric

namespace QFS

variable {d : ℕ}

/-! ## The scale step

The paper picks an even integer `Δ` larger than `max(δ, R₀)` and divisible by the
number `L` of reference cones, so that every town
`T_n = T(Δⁿ, Δⁿ⁻¹)` is `ϑ`-sparsely populated. -/

/-- An admissible scale step for the renormalisation. -/
structure ScaleStep (d : ℕ) (ϑ R₀ : ℝ) (L : ℕ) where
  /-- The step, an integer. -/
  val : ℕ
  /-- It is even. -/
  even : Even val
  /-- It exceeds the constant `δ` of Lemma 5.9. -/
  gt_delta : apexShrinkConst d ϑ < (val : ℝ)
  /-- It exceeds the minimal jump distance. -/
  gt_R₀ : R₀ < (val : ℝ)
  /-- It is divisible by the number of reference cones. -/
  dvd : L ∣ val

/-- Admissible scale steps exist. -/
theorem exists_scaleStep (d : ℕ) (ϑ R₀ : ℝ) (L : ℕ) (hL : 0 < L) :
    Nonempty (ScaleStep d ϑ R₀ L) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max (apexShrinkConst d ϑ) R₀)
  refine ⟨⟨2 * L * (m + 1), ⟨L * (m + 1), by ring⟩, ?_, ?_, ⟨2 * (m + 1), by ring⟩⟩⟩ <;>
  · have h1 : (m : ℝ) < (2 * L * (m + 1) : ℕ) := by
      push_cast
      have : (1:ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have h2 := le_max_left (apexShrinkConst d ϑ) R₀
    have h3 := le_max_right (apexShrinkConst d ϑ) R₀
    linarith

/-- Every town at a scale built from an admissible step is sparsely populated. -/
theorem sparselyPopulated_of_scaleStep {ϑ R₀ : ℝ} {L : ℕ} (Δ : ScaleStep d ϑ R₀ L)
    (hΔ0 : 0 < (Δ.val : ℝ)) (n : ℕ) :
    SparselyPopulated d ϑ ((Δ.val : ℝ) ^ (n + 1)) ((Δ.val : ℝ) ^ n) := by
  have h : (Δ.val : ℝ) ^ (n + 1) / (Δ.val : ℝ) ^ n = (Δ.val : ℝ) := by
    rw [pow_succ]
    field_simp
  rw [SparselyPopulated, h]
  exact Δ.gt_delta

/-! ## Lemma 5.16: the first jump -/

/-- **Lemma 5.16** of Bux–Kassmann–Schulze. There is a constant `R₁ ≥ 1`,
independent of the configuration, such that every point `x` and every scale `n`
admit a block of the town `T(Δⁿ⁺¹, Δⁿ)` lying entirely inside
`B_{Δⁿ⁺¹R₁}(x) ∩ (x + Γ(x))` — so `x` is joined by a single edge to *every* point
of that block. -/
theorem connect_first_jump {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    {Δ : ℝ} (hΔδ : apexShrinkConst d ϑ < Δ) (hΔ1 : 1 ≤ Δ) :
    ∃ R₁ : ℝ, 1 ≤ R₁ ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ →
      ∀ (x : EuclideanSpace ℝ (Fin d)) (n : ℕ),
        ∃ w ∈ lattice d,
          block (Δ ^ n) (Δ ^ (n + 1) • w) ⊆ ball x (Δ ^ (n + 1) * R₁) ∩ coneAt Γ x ∧
          ∀ q ∈ block (Δ ^ n) (Δ ^ (n + 1) • w), Δ ^ n ≤ ‖q - x‖ := by
  have hϑ2 : (0:ℝ) < ϑ / 2 := by positivity
  have hϑ2' : ϑ / 2 ≤ π / 2 := by linarith [pi_pos]
  have hs2 : 0 < Real.sin (ϑ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hϑ2 (by linarith [pi_pos])
  have hD : (0:ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hδ0 : 0 < apexShrinkConst d ϑ := apexShrinkConst_pos hϑ hϑ'
  have hΔ0 : (0:ℝ) < Δ := by linarith
  -- the shrink radius, chosen so that the rescaled distance clears Lemma 5.9
  obtain ⟨ρ, hρ⟩ : ∃ t : ℝ, t = apexShrinkConst d ϑ / Δ := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  obtain ⟨R', hR'⟩ : ∃ t : ℝ, t = (ρ + Real.sqrt d) / Real.sin (ϑ / 2) + 1 := ⟨_, rfl⟩
  have hR'gt : (ρ + Real.sqrt d) / Real.sin (ϑ / 2) < R' := by rw [hR']; linarith
  have hR'1 : 1 ≤ R' := by
    have : 0 < (ρ + Real.sqrt d) / Real.sin (ϑ / 2) := by positivity
    rw [hR']; linarith
  refine ⟨R' + Real.sqrt d, by linarith, ?_⟩
  intro Γ hΓ x n
  have hΔn : (0:ℝ) < Δ ^ (n + 1) := by positivity
  have hΔnn : (0:ℝ) < Δ ^ n := by positivity
  -- rescale
  obtain ⟨z, hz⟩ : ∃ z : EuclideanSpace ℝ (Fin d), z = (Δ ^ (n + 1))⁻¹ • x := ⟨_, rfl⟩
  have hxz : Δ ^ (n + 1) • z = x := by
    rw [hz, smul_smul, mul_inv_cancel₀ (ne_of_gt hΔn), one_smul]
  -- a lattice point deep in the half-cone at `z`
  obtain ⟨w, hwlat, hwz, hwc, hwball⟩ :=
    exists_lattice_mem_cone (v := (Γ x).axis) (Γ x).norm_axis hϑ2 (le_refl (ϑ / 2)) hϑ2'
      hρ0 hR'gt z
  have hfar : ρ < ‖w - z‖ := by
    by_contra hc
    rw [not_lt] at hc
    have hzmem : z ∈ closedBall w ρ := by
      rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
      exact hc
    have := hwball hzmem
    rw [mem_shift, sub_self] at this
    exact zero_notMem_cone _ _ this
  refine ⟨w, hwlat, ?_⟩
  -- the block's centre, back at scale
  have hcx : Δ ^ (n + 1) • w - x = Δ ^ (n + 1) • (w - z) := by
    rw [← hxz, ← smul_sub]
  have hcxnorm : ‖Δ ^ (n + 1) • w - x‖ = Δ ^ (n + 1) * ‖w - z‖ := by
    rw [hcx, norm_smul, Real.norm_eq_abs, abs_of_pos hΔn]
  -- Lemma 5.9 applies at scale
  have hdist : apexShrinkConst d ϑ * Δ ^ n ≤ ‖x - Δ ^ (n + 1) • w‖ := by
    rw [norm_sub_rev, hcxnorm]
    have h1 : apexShrinkConst d ϑ * Δ ^ n = Δ ^ (n + 1) * ρ := by
      rw [hρ, pow_succ]
      field_simp
    rw [h1]
    exact le_of_lt (by nlinarith)
  have hincone : Δ ^ (n + 1) • w ∈ shift (cone (Γ x).axis (ϑ / 2)) x := by
    rw [mem_shift, hcx]
    exact smul_mem_cone (Γ x).norm_axis hϑ2 hϑ2' hΔn hwc
  have hcube := renormalization_apex_shrink hϑ hϑ' (Γ x).norm_axis hΔnn hdist hincone
  have hxcube : x ∈ closedCube (Δ ^ n) x := by
    have he : infNorm (x - x) = 0 :=
      le_antisymm (infNorm_le le_rfl (fun i => by rw [sub_self]; simp)) (infNorm_nonneg _)
    simp only [closedCube, Set.mem_ofPred_eq, he]
    positivity
  -- the block is far from `x`: the shrink radius forces it
  have hfarc : apexShrinkConst d ϑ * Δ ^ n < ‖Δ ^ (n + 1) • w - x‖ := by
    rw [hcxnorm]
    have h1 : apexShrinkConst d ϑ * Δ ^ n = Δ ^ (n + 1) * ρ := by
      rw [hρ, pow_succ]
      field_simp
    rw [h1]
    nlinarith
  have hδd : Real.sqrt d / 2 + 1 ≤ apexShrinkConst d ϑ := by
    rw [apexShrinkConst, le_div_iff₀ hs2]
    have hs1 := Real.sin_le_one (ϑ / 2)
    nlinarith
  have hqc : ∀ q ∈ block (Δ ^ n) (Δ ^ (n + 1) • w),
      ‖q - Δ ^ (n + 1) • w‖ ≤ Δ ^ n / 2 * Real.sqrt d := by
    intro q hq
    have := closedCube_subset_closedBall (le_of_lt hΔnn) (Δ ^ (n + 1) • w) hq.2
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  refine ⟨fun q hq => ⟨?_, ?_⟩, fun q hq => ?_⟩
  · -- inside the ball
    rw [mem_ball, dist_eq_norm]
    have h1 := hqc q hq
    have h2 : ‖Δ ^ (n + 1) • w - x‖ < Δ ^ (n + 1) * R' := by
      rw [hcxnorm]
      nlinarith
    have h3 : ‖q - x‖ ≤ ‖q - Δ ^ (n + 1) • w‖ + ‖Δ ^ (n + 1) • w - x‖ := by
      have he : q - x = (q - Δ ^ (n + 1) • w) + (Δ ^ (n + 1) • w - x) := by abel
      rw [he]
      exact norm_add_le _ _
    have h4 : Δ ^ n / 2 * Real.sqrt d ≤ Δ ^ (n + 1) * Real.sqrt d := by
      have h5 : Δ ^ n / 2 ≤ Δ ^ (n + 1) := by
        rw [pow_succ]
        nlinarith
      nlinarith
    nlinarith
  · -- inside the cone at `x`
    rw [mem_coneAt]
    exact doubleCone_mono (le_of_lt hϑ) (Γ x).apex_le_pi (hΓ.2 x)
      (Set.mem_union_left _ (Set.mem_iInter₂.mp (hcube hq.2) x hxcube))
  · -- and far from `x`
    have h1 := hqc q hq
    have h2 : ‖Δ ^ (n + 1) • w - x‖ ≤ ‖q - x‖ + ‖q - Δ ^ (n + 1) • w‖ := by
      have he : Δ ^ (n + 1) • w - x = (q - x) - (q - Δ ^ (n + 1) • w) := by abel
      rw [he]
      exact norm_sub_le _ _
    nlinarith

/-! ## The graph `G` as a simple graph, and the statement of Theorem 5.15

Theorem 5.15's claims (2)–(4) count edges and measure their lengths, which the
`Relation.ReflTransGen` used in Sections 4 and 5.1 cannot express: it records
that a path exists, not which one. So the paths of Theorem 5.15 are Mathlib
`SimpleGraph.Walk`s, which carry a length, a list of darts and a list of edges. -/

/-- Adjacency in the graph `G`: distinct lattice points, one in the other's
cone. -/
def latticeAdj (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (x y : EuclideanSpace ℝ (Fin d)) : Prop :=
  x ∈ lattice d ∧ y ∈ lattice d ∧ (y ∈ coneAt Γ x ∨ x ∈ coneAt Γ y)

instance latticeAdj_symm (Γ : Configuration (EuclideanSpace ℝ (Fin d))) :
    Std.Symm (latticeAdj Γ) :=
  ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩

instance latticeAdj_irrefl (Γ : Configuration (EuclideanSpace ℝ (Fin d))) :
    Std.Irrefl (latticeAdj Γ) :=
  ⟨fun x h => by rcases h.2.2 with h' | h' <;> exact notMem_coneAt_self Γ x h'⟩

/-- The graph `G` of a configuration, restricted to the lattice. -/
def latticeGraph (Γ : Configuration (EuclideanSpace ℝ (Fin d))) :
    SimpleGraph (EuclideanSpace ℝ (Fin d)) :=
  ⟨latticeAdj Γ, latticeAdj_symm Γ, latticeAdj_irrefl Γ⟩

/-- The lattice, as a type. -/
abbrev LatticePt (d : ℕ) := {v : EuclideanSpace ℝ (Fin d) // v ∈ lattice d}

/-- The statement of **Theorem 5.15**, the main result of Section 5.

Claim (1) — that `p x y` runs from `x` to `y` — is carried by the type of the
walk. Claim (2) bounds its length by `N`, claim (3) bounds by `M` the number of
pairs whose walk uses a given edge, and claim (4) says every edge of `p x y` has
length comparable to `‖x − y‖` with constant `lam`. The three constants are
independent of `Γ`, which is why they are quantified before it in
`PathPropsHolds`. -/
def PathProps (Γ : Configuration (EuclideanSpace ℝ (Fin d))) (N M : ℕ) (lam : ℝ) : Prop :=
  ∃ p : ∀ x y : LatticePt d, (latticeGraph Γ).Walk x.1 y.1,
    (∀ x y, (p x y).length ≤ N) ∧
    (∀ e : Sym2 (EuclideanSpace ℝ (Fin d)),
      {q : LatticePt d × LatticePt d | e ∈ (p q.1 q.2).edges}.encard ≤ (M : ℕ∞)) ∧
    (∀ x y, ∀ e ∈ (p x y).darts,
      lam⁻¹ * ‖x.1 - y.1‖ ≤ ‖e.toProd.1 - e.toProd.2‖ ∧
        ‖e.toProd.1 - e.toProd.2‖ ≤ lam * ‖x.1 - y.1‖)

/-- **Theorem 5.15** of Bux–Kassmann–Schulze, as a statement. Not proved here:
see the README for what its proof needs. -/
def PathPropsHolds (d : ℕ) (ϑ R₀ : ℝ) : Prop :=
  ∃ (N M : ℕ) (lam : ℝ), 0 < N ∧ 0 < M ∧ R₀ ≤ lam ∧
    ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ → PathProps Γ N M lam

end QFS
