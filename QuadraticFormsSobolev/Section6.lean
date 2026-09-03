/-
Section 6 of Bux–Kassmann–Schulze: the proof of Theorem 1.3 from Theorem 5.15.

The argument chains along `p_xy`: Cauchy–Schwarz turns `(f(x) − f(y))²` into the
sum of the squared increments along the path, claim (4) of Theorem 5.15 turns
`|x − y|^{-d-α}` into `λ^{d+α}|z_{i+1} − z_i|^{-d-α}`, assumption (1.7) turns
that into `Λ ω(z_i, z_{i+1})` — this is where every edge must be longer than
`R₀`, hence `PathPropsLong` — and claim (3) turns the sum over pairs of sums over
edges back into a sum over pairs, at the cost of the multiplicity `M`.
-/
import QuadraticFormsSobolev.BlockPaths
import QuadraticFormsSobolev.Section1

open Real Set Metric ENNReal

namespace QFS

variable {d : ℕ}

/-! ## Chaining along a walk

Three facts about walks in an arbitrary graph on `ℝ^d`. -/

/-- The increments along a walk telescope. -/
lemma walk_telescope {G : SimpleGraph (EuclideanSpace ℝ (Fin d))}
    (f : EuclideanSpace ℝ (Fin d) → ℝ) {x y : EuclideanSpace ℝ (Fin d)} (w : G.Walk x y) :
    (w.darts.map (fun D => f D.toProd.1 - f D.toProd.2)).sum = f x - f y := by
  induction w with
  | nil => simp
  | cons h p ih =>
      rw [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons, ih]
      ring

/-- Cauchy–Schwarz for a list: `(∑ aᵢ)² ≤ n ∑ aᵢ²`. -/
lemma list_sq_sum_le (l : List ℝ) :
    l.sum ^ 2 ≤ l.length * (l.map (fun a => a ^ 2)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have hs : (0:ℝ) ≤ (t.map (fun a => a ^ 2)).sum := by
        refine List.sum_nonneg (fun x hx => ?_)
        obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
        positivity
      rw [List.sum_cons, List.length_cons, List.map_cons, List.sum_cons]
      push_cast
      rcases Nat.eq_zero_or_pos t.length with hz | hpos
      · have ht : t = [] := List.length_eq_zero_iff.mp hz
        subst ht
        simp
      · have hn : (1:ℝ) ≤ (t.length : ℝ) := by exact_mod_cast hpos
        nlinarith [ih, sq_nonneg ((t.length : ℝ) * a - t.sum), hs, hn]

/-- Cauchy–Schwarz along a walk: the squared total increment is at most the
length times the sum of the squared increments. -/
lemma walk_sq_le {G : SimpleGraph (EuclideanSpace ℝ (Fin d))}
    (f : EuclideanSpace ℝ (Fin d) → ℝ) {x y : EuclideanSpace ℝ (Fin d)} (w : G.Walk x y) :
    (f x - f y) ^ 2
      ≤ w.length * (w.darts.map (fun D => (f D.toProd.1 - f D.toProd.2) ^ 2)).sum := by
  have h := list_sq_sum_le (w.darts.map (fun D => f D.toProd.1 - f D.toProd.2))
  rw [walk_telescope f w, List.length_map, SimpleGraph.Walk.length_darts,
    List.map_map] at h
  exact h

/-- Every vertex of a walk is within the walk's total length of its start. -/
lemma norm_sub_start_le {G : SimpleGraph (EuclideanSpace ℝ (Fin d))}
    {x y : EuclideanSpace ℝ (Fin d)} (w : G.Walk x y) :
    ∀ v ∈ w.support, ‖v - x‖ ≤ (w.darts.map (fun D => ‖D.toProd.1 - D.toProd.2‖)).sum := by
  induction w with
  | nil => intro v hv; simp at hv; simp [hv]
  | @cons u m z hadj p ih =>
      intro v hv
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
      rw [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons]
      have hnn : (0:ℝ) ≤ (p.darts.map (fun D => ‖D.toProd.1 - D.toProd.2‖)).sum := by
        refine List.sum_nonneg (fun t ht => ?_)
        obtain ⟨D, -, rfl⟩ := List.mem_map.mp ht
        exact norm_nonneg _
      have hum : (0:ℝ) ≤ ‖u - m‖ := norm_nonneg _
      rcases hv with hv | hv
      · rw [hv]
        simp only [sub_self, norm_zero]
        linarith
      · have h1 := ih v hv
        have h2 : ‖v - u‖ ≤ ‖v - m‖ + ‖m - u‖ := by
          have he : v - u = (v - m) + (m - u) := by abel
          rw [he]; exact norm_add_le _ _
        have h3 : ‖m - u‖ = ‖u - m‖ := norm_sub_rev _ _
        linarith

/-! ## Lifting a real list sum to `ℝ≥0∞` -/

lemma ofReal_list_sum {l : List ℝ} (h : ∀ a ∈ l, 0 ≤ a) :
    ENNReal.ofReal l.sum = (l.map ENNReal.ofReal).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ht : ∀ x ∈ t, (0:ℝ) ≤ x := fun x hx => h x (List.mem_cons_of_mem _ hx)
      rw [List.sum_cons, List.map_cons, List.sum_cons,
        ENNReal.ofReal_add (h a List.mem_cons_self) (List.sum_nonneg ht), ih ht]

/-! ## The kernel along an edge

Assumption (1.7) at an edge of `G`: the indicator is `1` because the edge means
one endpoint lies in the other's cone, and the edge is longer than `R₀` because
of `PathPropsLong`. -/

/-- At an edge of `G` longer than `R₀`, the jump kernel is at most `Λ ω`. -/
theorem jumpKernel_le_of_dart {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {α Λ R₀ : ℝ} {ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hω : DiscreteKernelBounds Γ α Λ R₀ ω) (D : (latticeGraph Γ).Dart)
    (hD : R₀ < ‖D.toProd.1 - D.toProd.2‖) :
    jumpKernel d α D.toProd.1 D.toProd.2 ≤ ENNReal.ofReal Λ * ω D.toProd.1 D.toProd.2 := by
  have hΛ0 : (0:ℝ) < Λ := lt_of_lt_of_le zero_lt_one hω.one_le
  -- the indicator is at least one
  have hind : (1:ℝ≥0∞) ≤ indE (coneAt Γ D.toProd.1) D.toProd.2
      + indE (coneAt Γ D.toProd.2) D.toProd.1 := by
    rcases D.adj.2.2 with h | h
    · have h1 : indE (coneAt Γ D.toProd.1) D.toProd.2 = 1 := Set.indicator_of_mem h _
      rw [h1]
      exact le_self_add
    · have h1 : indE (coneAt Γ D.toProd.2) D.toProd.1 = 1 := Set.indicator_of_mem h _
      rw [h1]
      exact le_add_self
  have hlow := hω.lower D.toProd.1 D.toProd.2 hD
  have hstep : ENNReal.ofReal Λ⁻¹ * jumpKernel d α D.toProd.1 D.toProd.2
      ≤ ω D.toProd.1 D.toProd.2 := by
    refine le_trans ?_ hlow
    refine mul_le_mul' le_rfl ?_
    calc jumpKernel d α D.toProd.1 D.toProd.2
        = 1 * jumpKernel d α D.toProd.1 D.toProd.2 := (one_mul _).symm
      _ ≤ (indE (coneAt Γ D.toProd.1) D.toProd.2
            + indE (coneAt Γ D.toProd.2) D.toProd.1)
              * jumpKernel d α D.toProd.1 D.toProd.2 := mul_le_mul' hind le_rfl
  -- multiply through by `Λ`
  calc jumpKernel d α D.toProd.1 D.toProd.2
      = ENNReal.ofReal Λ * (ENNReal.ofReal Λ⁻¹ * jumpKernel d α D.toProd.1 D.toProd.2) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hΛ0.le, mul_inv_cancel₀ (ne_of_gt hΛ0),
          ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal Λ * ω D.toProd.1 D.toProd.2 := mul_le_mul' le_rfl hstep

/-! ## The chain estimate

The displayed computation of Section 6, for a single pair. -/

/-- **The chain estimate.** If `x` and `y` are joined by a walk whose edges are at
most `λ‖x − y‖` long and all longer than `R₀`, then the `H^{α/2}` term of the pair
is controlled by the `ω`-terms of the walk's edges. -/
theorem chain_estimate {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {α Λ R₀ lam : ℝ} {ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hω : DiscreteKernelBounds Γ α Λ R₀ ω) (hα : 0 < α) (hlam : 1 ≤ lam)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) {x y : EuclideanSpace ℝ (Fin d)}
    (w : (latticeGraph Γ).Walk x y)
    (hb : ∀ D ∈ w.darts, ‖D.toProd.1 - D.toProd.2‖ ≤ lam * ‖x - y‖ ∧
      R₀ < ‖D.toProd.1 - D.toProd.2‖) :
    ENNReal.ofReal ((f x - f y) ^ 2) * jumpKernel d α x y
      ≤ ENNReal.ofReal ((w.length : ℝ) * lam ^ ((d : ℝ) + α) * Λ) *
        (w.darts.map (fun D => ENNReal.ofReal ((f D.toProd.1 - f D.toProd.2) ^ 2)
          * ω D.toProd.1 D.toProd.2)).sum := by
  have hΛ0 : (0:ℝ) < Λ := lt_of_lt_of_le zero_lt_one hω.one_le
  have hlam0 : (0:ℝ) < lam := by linarith
  have hexp : (-(d:ℝ) - α) ≤ 0 := by
    have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    linarith
  have hpow0 : (0:ℝ) < lam ^ ((d:ℝ) + α) := Real.rpow_pos_of_pos hlam0 _
  -- the kernel comparison at each edge
  have hterm : ∀ D ∈ w.darts, ‖x - y‖ ^ (-(d:ℝ) - α)
      ≤ lam ^ ((d:ℝ) + α) * ‖D.toProd.1 - D.toProd.2‖ ^ (-(d:ℝ) - α) := by
    intro D hD
    obtain ⟨hup, hlong⟩ := hb D hD
    have hD0 : (0:ℝ) < ‖D.toProd.1 - D.toProd.2‖ := norm_sub_pos_iff.mpr D.adj.ne
    have hdiv : (0:ℝ) < ‖D.toProd.1 - D.toProd.2‖ / lam := by positivity
    have hle : ‖D.toProd.1 - D.toProd.2‖ / lam ≤ ‖x - y‖ := by
      rw [div_le_iff₀ hlam0]
      linarith [hup]
    have h1 := Real.rpow_le_rpow_of_nonpos hdiv hle hexp
    have h2 : (‖D.toProd.1 - D.toProd.2‖ / lam) ^ (-(d:ℝ) - α)
        = lam ^ ((d:ℝ) + α) * ‖D.toProd.1 - D.toProd.2‖ ^ (-(d:ℝ) - α) := by
      rw [Real.div_rpow (norm_nonneg _) hlam0.le]
      have hneg : (-(d:ℝ) - α) = -((d:ℝ) + α) := by ring
      rw [hneg, Real.rpow_neg hlam0.le]
      field_simp
    linarith [h1, h2.le, h2.ge]
  -- the real inequality
  have hnn : ∀ t ∈ w.darts.map (fun D => (f D.toProd.1 - f D.toProd.2) ^ 2
      * ‖D.toProd.1 - D.toProd.2‖ ^ (-(d:ℝ) - α)), (0:ℝ) ≤ t := by
    intro t ht
    obtain ⟨D, -, rfl⟩ := List.mem_map.mp ht
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hreal : (f x - f y) ^ 2 * ‖x - y‖ ^ (-(d:ℝ) - α)
      ≤ (w.length : ℝ) * lam ^ ((d:ℝ) + α) *
        (w.darts.map (fun D => (f D.toProd.1 - f D.toProd.2) ^ 2
          * ‖D.toProd.1 - D.toProd.2‖ ^ (-(d:ℝ) - α))).sum := by
    have hJ0 : (0:ℝ) ≤ ‖x - y‖ ^ (-(d:ℝ) - α) := Real.rpow_nonneg (norm_nonneg _) _
    have h1 := mul_le_mul_of_nonneg_right (walk_sq_le f w) hJ0
    have h2 : (w.darts.map (fun D => (f D.toProd.1 - f D.toProd.2) ^ 2)).sum
          * ‖x - y‖ ^ (-(d:ℝ) - α)
        = (w.darts.map (fun D => (f D.toProd.1 - f D.toProd.2) ^ 2
            * ‖x - y‖ ^ (-(d:ℝ) - α))).sum := (List.sum_map_mul_right _ _ _).symm
    have h3 : (w.darts.map (fun D => (f D.toProd.1 - f D.toProd.2) ^ 2
          * ‖x - y‖ ^ (-(d:ℝ) - α))).sum
        ≤ (w.darts.map (fun D => lam ^ ((d:ℝ) + α) *
            ((f D.toProd.1 - f D.toProd.2) ^ 2
              * ‖D.toProd.1 - D.toProd.2‖ ^ (-(d:ℝ) - α)))).sum := by
      refine List.sum_le_sum (fun D hD => ?_)
      have hA : (0:ℝ) ≤ (f D.toProd.1 - f D.toProd.2) ^ 2 := sq_nonneg _
      nlinarith [hterm D hD]
    have h4 : (w.darts.map (fun D => lam ^ ((d:ℝ) + α) *
          ((f D.toProd.1 - f D.toProd.2) ^ 2
            * ‖D.toProd.1 - D.toProd.2‖ ^ (-(d:ℝ) - α)))).sum
        = lam ^ ((d:ℝ) + α) * (w.darts.map (fun D => (f D.toProd.1 - f D.toProd.2) ^ 2
            * ‖D.toProd.1 - D.toProd.2‖ ^ (-(d:ℝ) - α))).sum := List.sum_map_mul_left _ _ _
    have hlen : (0:ℝ) ≤ (w.length : ℝ) := Nat.cast_nonneg _
    nlinarith [h1, h3, hlen]
  -- lift to `ℝ≥0∞`
  calc ENNReal.ofReal ((f x - f y) ^ 2) * jumpKernel d α x y
      = ENNReal.ofReal ((f x - f y) ^ 2 * ‖x - y‖ ^ (-(d:ℝ) - α)) := by
        rw [jumpKernel, ← ENNReal.ofReal_mul (sq_nonneg _)]
    _ ≤ ENNReal.ofReal ((w.length : ℝ) * lam ^ ((d:ℝ) + α) *
          (w.darts.map (fun D => (f D.toProd.1 - f D.toProd.2) ^ 2
            * ‖D.toProd.1 - D.toProd.2‖ ^ (-(d:ℝ) - α))).sum) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal ((w.length : ℝ) * lam ^ ((d:ℝ) + α)) *
          (w.darts.map (fun D => ENNReal.ofReal ((f D.toProd.1 - f D.toProd.2) ^ 2
            * ‖D.toProd.1 - D.toProd.2‖ ^ (-(d:ℝ) - α)))).sum := by
        rw [ENNReal.ofReal_mul (by positivity), ofReal_list_sum hnn, List.map_map]
        rfl
    _ ≤ ENNReal.ofReal ((w.length : ℝ) * lam ^ ((d:ℝ) + α)) *
          (w.darts.map (fun D => ENNReal.ofReal Λ *
            (ENNReal.ofReal ((f D.toProd.1 - f D.toProd.2) ^ 2)
              * ω D.toProd.1 D.toProd.2))).sum := by
        refine mul_le_mul' le_rfl (List.sum_le_sum (fun D hD => ?_))
        rw [ENNReal.ofReal_mul (sq_nonneg _)]
        calc ENNReal.ofReal ((f D.toProd.1 - f D.toProd.2) ^ 2)
              * ENNReal.ofReal (‖D.toProd.1 - D.toProd.2‖ ^ (-(d:ℝ) - α))
            ≤ ENNReal.ofReal ((f D.toProd.1 - f D.toProd.2) ^ 2)
              * (ENNReal.ofReal Λ * ω D.toProd.1 D.toProd.2) :=
              mul_le_mul' le_rfl (jumpKernel_le_of_dart hω D (hb D hD).2)
          _ = ENNReal.ofReal Λ * (ENNReal.ofReal ((f D.toProd.1 - f D.toProd.2) ^ 2)
              * ω D.toProd.1 D.toProd.2) := by ring
    _ = ENNReal.ofReal ((w.length : ℝ) * lam ^ ((d:ℝ) + α) * Λ) *
          (w.darts.map (fun D => ENNReal.ofReal ((f D.toProd.1 - f D.toProd.2) ^ 2)
            * ω D.toProd.1 D.toProd.2)).sum := by
        rw [List.sum_map_mul_left, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]

end QFS
