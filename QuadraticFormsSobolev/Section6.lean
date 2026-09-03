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

/-! ## The discrete form as a finite sum

Both balls hold finitely many lattice points, so both sides of Theorem 1.3 are
finite sums and the double counting of Step 6 can be done with `Finset.sum_comm`. -/

lemma tsum_subtype_eq_finset_sum {α : Type*} {s : Set α} (hs : s.Finite) (g : α → ℝ≥0∞) :
    ∑' x : s, g x = ∑ x ∈ hs.toFinset, g x := by
  classical
  rw [tsum_subtype, tsum_eq_sum (s := hs.toFinset)]
  · exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem (hs.mem_toFinset.mp hx) _
  · exact fun b hb => Set.indicator_of_notMem (fun hc => hb (hs.mem_toFinset.mpr hc)) _

/-- The set of pairs `discreteForm` sums over. -/
def pairSet (S : Set (EuclideanSpace ℝ (Fin d))) (R₀ : ℝ) :
    Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  {p | p.1 ∈ S ∩ lattice d ∧ p.2 ∈ S ∩ lattice d ∧ R₀ < ‖p.1 - p.2‖}

lemma pairSet_finite (x₀ : EuclideanSpace ℝ (Fin d)) (R R₀ : ℝ) :
    (pairSet (ball x₀ R) R₀).Finite := by
  have hfin : (lattice d ∩ closedBall x₀ R).Finite := lattice_inter_closedBall_finite x₀ R
  refine ((hfin.prod hfin).subset ?_)
  rintro ⟨u, v⟩ ⟨⟨hu1, hu2⟩, ⟨hv1, hv2⟩, -⟩
  exact ⟨⟨hu2, ball_subset_closedBall hu1⟩, ⟨hv2, ball_subset_closedBall hv1⟩⟩

lemma discreteForm_eq_sum {S : Set (EuclideanSpace ℝ (Fin d))} {R₀ : ℝ}
    (hfin : (pairSet S R₀).Finite)
    (ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    discreteForm S R₀ ω f
      = ∑ p ∈ hfin.toFinset, ENNReal.ofReal ((f p.1 - f p.2) ^ 2) * ω p.1 p.2 :=
  tsum_subtype_eq_finset_sum hfin
    (fun p => ENNReal.ofReal ((f p.1 - f p.2) ^ 2) * ω p.1 p.2)

/-! ## Bounding a list sum by the sum over the values it takes -/

/-- A list of at most `n` terms, each a value of `g` at a point of `T`, sums to at
most `n` times the sum of `g` over `T`. -/
lemma list_sum_le_card_mul_sum {ι β : Type*} (l : List ι) (key : ι → β)
    (g : β → ℝ≥0∞) {T : Finset β} (hT : ∀ i ∈ l, key i ∈ T) {n : ℕ} (hn : l.length ≤ n) :
    (l.map (fun i => g (key i))).sum ≤ (n : ℝ≥0∞) * ∑ b ∈ T, g b := by
  have hnn : ∀ b ∈ T, (0:ℝ≥0∞) ≤ g b := fun b _ => zero_le
  have hstep : (l.map (fun i => g (key i))).sum ≤ (l.map (fun _ => ∑ b ∈ T, g b)).sum :=
    List.sum_le_sum fun i hi => Finset.single_le_sum hnn (hT i hi)
  refine le_trans hstep ?_
  rw [List.map_const', List.sum_replicate, nsmul_eq_mul]
  exact mul_le_mul' (by exact_mod_cast hn) le_rfl

/-! ## Double counting

Step 6's multiplicity bound, in the form the summation needs. -/

/-- If every `q ∈ FA` selects a set `U q ⊆ FB`, and no element of `FB` is selected
by more than `M` elements of `FA`, then summing over the selected sets costs a
factor `M`. -/
lemma sum_select_le {α β : Type*} [DecidableEq β] {FA : Finset α} {FB : Finset β}
    (U : α → Finset β) (hU : ∀ q ∈ FA, U q ⊆ FB) (g : β → ℝ≥0∞) {M : ℕ}
    (hM : ∀ b ∈ FB, (FA.filter fun q => b ∈ U q).card ≤ M) :
    ∑ q ∈ FA, ∑ b ∈ U q, g b ≤ (M : ℝ≥0∞) * ∑ b ∈ FB, g b := by
  classical
  have h1 : ∀ q ∈ FA, ∑ b ∈ U q, g b = ∑ b ∈ FB, (if b ∈ U q then g b else 0) := by
    intro q hq
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hU q hq)]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum (fun b hb => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul' (by exact_mod_cast hM b hb) le_rfl

/-- A `Finset` that injects into a set of `encard` at most `M` has at most `M`
elements. -/
lemma card_le_of_encard_le {α β : Type*} {F : Finset α} {S : Set β} {M : ℕ}
    (ψ : α → β) (hmem : ∀ a ∈ F, ψ a ∈ S) (hinj : Set.InjOn ψ (F : Set α))
    (hS : S.encard ≤ (M : ℕ∞)) : F.card ≤ M := by
  classical
  have h2 : ((F.image ψ : Finset β) : Set β) ⊆ S := by
    intro b hb
    rw [Finset.coe_image] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact hmem a ha
  have h3 : (((F.image ψ).card : ℕ) : ℕ∞) ≤ S.encard := by
    rw [← Set.encard_coe_eq_coe_finsetCard]
    exact Set.encard_le_encard h2
  rw [Finset.card_image_of_injOn hinj] at h3
  exact_mod_cast le_trans h3 hS

/-! ## Theorem 1.3

The proof of Section 6: chain each pair along its path, then double count. -/

/-- In dimension `0` the space is a single point, so no two points are at distance
more than `R₀` and both sides of Theorem 1.3 vanish. -/
lemma discreteForm_dim_zero {S : Set (EuclideanSpace ℝ (Fin 0))} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (ω : EuclideanSpace ℝ (Fin 0) → EuclideanSpace ℝ (Fin 0) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin 0) → ℝ) : discreteForm S R₀ ω f = 0 := by
  have hempty : IsEmpty {p : EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 0) //
      p.1 ∈ S ∩ lattice 0 ∧ p.2 ∈ S ∩ lattice 0 ∧ R₀ < ‖p.1 - p.2‖} := by
    refine ⟨fun q => ?_⟩
    obtain ⟨⟨u, v⟩, -, -, huv⟩ := q
    have h : u = v := euclidean_ext (fun i => i.elim0)
    rw [h, sub_self, norm_zero] at huv
    linarith
  have := hempty
  rw [discreteForm]
  exact tsum_empty

/-- **Theorem 1.3** of Bux–Kassmann–Schulze. -/
theorem theoremOneThree : TheoremOneThree d := by
  classical
  intro ϑ Λ α R₀ hϑ hΛ hα hα2 hR₀
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨1, 1, le_refl 1, le_refl 1, fun Γ hΓ ω hω x₀ R f hR => ?_⟩
    rw [discreteForm_dim_zero hR₀]
    exact zero_le
  have hpi : (0:ℝ) < π / 2 := by positivity
  -- apex angles may be capped at `π/2`
  have hmono : ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ →
      IsBounded Γ (min ϑ (π / 2)) :=
    fun Γ hΓ => ⟨lt_min hϑ hpi, fun x => le_trans (min_le_left _ _) (hΓ.2 x)⟩
  obtain ⟨N, M, lam0, hN, hM, hlamR₀, hprop⟩ :=
    path_props_long hd (lt_min hϑ hpi) (min_le_right ϑ (π / 2)) R₀
  obtain ⟨lam, hlam1, hlamge⟩ : ∃ lam : ℝ, 1 ≤ lam ∧ lam0 ≤ lam :=
    ⟨max lam0 1, le_max_right _ _, le_max_left _ _⟩
  have hlamP : (0:ℝ) < lam := by linarith
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hMR : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hpow1 : (1:ℝ) ≤ lam ^ ((d:ℝ) + α) := by
    have h0 : lam ^ (0:ℝ) ≤ lam ^ ((d:ℝ) + α) := by
      refine Real.rpow_le_rpow_of_exponent_le hlam1 ?_
      have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
      linarith
    rwa [Real.rpow_zero] at h0
  have hc1 : (1:ℝ) ≤ (N:ℝ) * lam ^ ((d:ℝ) + α) := by nlinarith
  have hc2 : (1:ℝ) ≤ (N:ℝ) * lam ^ ((d:ℝ) + α) * Λ := by nlinarith
  have hc3 : (1:ℝ) ≤ (N:ℝ) * (M:ℝ) := by nlinarith
  have hc4 : (1:ℝ) ≤ (N:ℝ) * lam ^ ((d:ℝ) + α) * Λ * ((N:ℝ) * M) := by nlinarith
  refine ⟨1 + 2 * N * lam, (N:ℝ) * lam ^ ((d:ℝ) + α) * Λ * ((N:ℝ) * M), by nlinarith,
    hc4, ?_⟩
  intro Γ hΓ ω hω x₀ R f hR
  obtain ⟨p, hlen, hfib, hdart⟩ := hprop Γ (hmono Γ hΓ)
  have hfinA := pairSet_finite x₀ R R₀
  have hfinB := pairSet_finite x₀ ((1 + 2 * N * lam) * R) R₀
  rw [discreteForm_eq_sum hfinA, discreteForm_eq_sum hfinB]
  -- a total lift of a lattice point to the subtype
  obtain ⟨lift, hlift⟩ : ∃ lift : EuclideanSpace ℝ (Fin d) → LatticePt d,
      ∀ u ∈ lattice d, (lift u).1 = u := by
    refine ⟨fun u => if h : u ∈ lattice d then ⟨u, h⟩ else ⟨0, zero_mem_lattice⟩, ?_⟩
    intro u hu
    simp [dif_pos hu]
  -- the edges used by a pair
  obtain ⟨Used, hUsed⟩ : ∃ Used : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) →
      Finset (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)),
      ∀ q, Used q = (((p (lift q.1) (lift q.2)).darts.map
        (fun D => (D.toProd.1, D.toProd.2))).toFinset) := ⟨_, fun _ => rfl⟩
  -- **Every vertex of a pair's walk lies in the big ball.**
  have hballpt : ∀ q ∈ hfinA.toFinset, ∀ v ∈ (p (lift q.1) (lift q.2)).support,
      v ∈ ball x₀ ((1 + 2 * N * lam) * R) := by
    intro q hq v hv
    rw [hfinA.mem_toFinset] at hq
    obtain ⟨⟨hq1b, hq1l⟩, ⟨hq2b, hq2l⟩, -⟩ := hq
    have he1 := hlift q.1 hq1l
    have he2 := hlift q.2 hq2l
    rw [mem_ball, dist_eq_norm] at hq1b hq2b
    have hlt : ‖q.1 - q.2‖ < 2 * R := by
      have he : q.1 - q.2 = (q.1 - x₀) + (x₀ - q.2) := by abel
      have h2 : ‖x₀ - q.2‖ = ‖q.2 - x₀‖ := norm_sub_rev _ _
      calc ‖q.1 - q.2‖ = ‖(q.1 - x₀) + (x₀ - q.2)‖ := by rw [he]
        _ ≤ ‖q.1 - x₀‖ + ‖x₀ - q.2‖ := norm_add_le _ _
        _ < 2 * R := by rw [h2]; linarith
    obtain ⟨Ssum, hS⟩ : ∃ t : ℝ, t = (((p (lift q.1) (lift q.2)).darts).map
        (fun D => ‖D.toProd.1 - D.toProd.2‖)).sum := ⟨_, rfl⟩
    have h1 : ‖v - q.1‖ ≤ Ssum := by
      have h : ‖v - (lift q.1).1‖ ≤ Ssum := by
        rw [hS]; exact norm_sub_start_le (p (lift q.1) (lift q.2)) v hv
      rwa [he1] at h
    have h2 : Ssum ≤ ((p (lift q.1) (lift q.2)).length : ℝ) * (lam * (2 * R)) := by
      have hbnd : (((p (lift q.1) (lift q.2)).darts).map
          (fun D => ‖D.toProd.1 - D.toProd.2‖)).sum
          ≤ ((p (lift q.1) (lift q.2)).darts.map
            (fun D => ‖D.toProd.1 - D.toProd.2‖)).length • (lam * (2 * R)) := by
        refine List.sum_le_card_nsmul _ _ ?_
        intro t ht
        obtain ⟨D', hD', rfl⟩ := List.mem_map.mp ht
        have hdd := hdart (lift q.1) (lift q.2) D' hD'
        rw [he1, he2] at hdd
        nlinarith [hdd.2.1, hlt, norm_nonneg (q.1 - q.2)]
      rw [List.length_map, SimpleGraph.Walk.length_darts, nsmul_eq_mul] at hbnd
      rw [hS]
      exact hbnd
    have h3 : ((p (lift q.1) (lift q.2)).length : ℝ) ≤ (N:ℝ) := by
      exact_mod_cast hlen (lift q.1) (lift q.2)
    have h4 : ‖v - x₀‖ ≤ ‖v - q.1‖ + ‖q.1 - x₀‖ := by
      have he : v - x₀ = (v - q.1) + (q.1 - x₀) := by abel
      rw [he]; exact norm_add_le _ _
    rw [mem_ball, dist_eq_norm]
    have h5 : ((p (lift q.1) (lift q.2)).length : ℝ) * (lam * (2 * R))
        ≤ (N:ℝ) * (lam * (2 * R)) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    nlinarith [h1, h2, h4, h5, hq1b]
  -- **(A)** the edges of a pair's walk are pairs of the big ball
  have hUsub : ∀ q ∈ hfinA.toFinset, Used q ⊆ hfinB.toFinset := by
    intro q hq b hb
    have hq' := hq
    rw [hfinA.mem_toFinset] at hq'
    obtain ⟨⟨-, hq1l⟩, ⟨-, hq2l⟩, -⟩ := hq'
    rw [hUsed, List.mem_toFinset] at hb
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hb
    have hdd := hdart (lift q.1) (lift q.2) D hD
    rw [hfinB.mem_toFinset]
    exact ⟨⟨hballpt q hq _ (SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts _ hD),
        D.adj.1⟩,
      ⟨hballpt q hq _ (SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts _ hD),
        D.adj.2.1⟩, hdd.2.2⟩
  -- **(B)** no edge is used by more than `M` pairs
  have hUcount : ∀ b ∈ hfinB.toFinset,
      (hfinA.toFinset.filter fun q => b ∈ Used q).card ≤ M := by
    intro b _
    refine card_le_of_encard_le (fun q => (lift q.1, lift q.2)) ?_ ?_ (hfib s(b.1, b.2))
    · intro q hq
      rw [Finset.mem_filter] at hq
      rw [hUsed, List.mem_toFinset] at hq
      obtain ⟨D, hD, hDb⟩ := List.mem_map.mp hq.2
      have hbe : D.edge = s(b.1, b.2) := by rw [← hDb]; rfl
      change s(b.1, b.2) ∈ (p (lift q.1) (lift q.2)).edges
      rw [← hbe]
      exact dart_edge_mem_edges hD
    · intro q₁ h₁ q₂ h₂ heq
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at h₁ h₂
      rw [hfinA.mem_toFinset] at h₁ h₂
      obtain ⟨⟨-, h₁a⟩, ⟨-, h₁b⟩, -⟩ := h₁.1
      obtain ⟨⟨-, h₂a⟩, ⟨-, h₂b⟩, -⟩ := h₂.1
      have hh1 : lift q₁.1 = lift q₂.1 := congrArg Prod.fst heq
      have hh2 : lift q₁.2 = lift q₂.2 := congrArg Prod.snd heq
      have e1 : q₁.1 = q₂.1 := by rw [← hlift q₁.1 h₁a, ← hlift q₂.1 h₂a, hh1]
      have e2 : q₁.2 = q₂.2 := by rw [← hlift q₁.2 h₁b, ← hlift q₂.2 h₂b, hh2]
      exact Prod.ext e1 e2
  -- **(C)** the chain estimate for each pair
  have hkey : ∀ q ∈ hfinA.toFinset,
      ENNReal.ofReal ((f q.1 - f q.2) ^ 2) * jumpKernel d α q.1 q.2
        ≤ ENNReal.ofReal ((N:ℝ) * lam ^ ((d:ℝ) + α) * Λ) *
          ((N:ℝ≥0∞) * ∑ b ∈ Used q,
            ENNReal.ofReal ((f b.1 - f b.2) ^ 2) * ω b.1 b.2) := by
    intro q hq
    have hq' := hq
    rw [hfinA.mem_toFinset] at hq'
    obtain ⟨⟨-, hq1l⟩, ⟨-, hq2l⟩, -⟩ := hq'
    have he1 := hlift q.1 hq1l
    have he2 := hlift q.2 hq2l
    have hb : ∀ D ∈ (p (lift q.1) (lift q.2)).darts,
        ‖D.toProd.1 - D.toProd.2‖ ≤ lam * ‖(lift q.1).1 - (lift q.2).1‖ ∧
          R₀ < ‖D.toProd.1 - D.toProd.2‖ := by
      intro D hD
      obtain ⟨-, hup, hlong⟩ := hdart (lift q.1) (lift q.2) D hD
      exact ⟨le_trans hup (by
        nlinarith [norm_nonneg ((lift q.1).1 - (lift q.2).1)]), hlong⟩
    have hce := chain_estimate hω hα hlam1 f (p (lift q.1) (lift q.2)) hb
    have hstep : ENNReal.ofReal (((p (lift q.1) (lift q.2)).length : ℝ)
          * lam ^ ((d:ℝ) + α) * Λ) *
        ((p (lift q.1) (lift q.2)).darts.map
          (fun D => ENNReal.ofReal ((f D.toProd.1 - f D.toProd.2) ^ 2)
            * ω D.toProd.1 D.toProd.2)).sum
        ≤ ENNReal.ofReal ((N:ℝ) * lam ^ ((d:ℝ) + α) * Λ) *
          ((N:ℝ≥0∞) * ∑ b ∈ Used q,
            ENNReal.ofReal ((f b.1 - f b.2) ^ 2) * ω b.1 b.2) := by
      refine mul_le_mul' ?_ ?_
      · refine ENNReal.ofReal_le_ofReal ?_
        have h3 : ((p (lift q.1) (lift q.2)).length : ℝ) ≤ (N:ℝ) := by
          exact_mod_cast hlen (lift q.1) (lift q.2)
        have hpos : (0:ℝ) < lam ^ ((d:ℝ) + α) * Λ := by positivity
        nlinarith
      · refine list_sum_le_card_mul_sum (p (lift q.1) (lift q.2)).darts
          (fun D => (D.toProd.1, D.toProd.2))
          (fun b => ENNReal.ofReal ((f b.1 - f b.2) ^ 2) * ω b.1 b.2) ?_
          (by rw [SimpleGraph.Walk.length_darts]; exact hlen (lift q.1) (lift q.2))
        intro D hD
        rw [hUsed, List.mem_toFinset]
        exact List.mem_map_of_mem hD
    have hce2 := le_trans hce hstep
    rwa [he1, he2] at hce2
  -- **assembly**
  calc ∑ q ∈ hfinA.toFinset,
        ENNReal.ofReal ((f q.1 - f q.2) ^ 2) * jumpKernel d α q.1 q.2
      ≤ ∑ q ∈ hfinA.toFinset, ENNReal.ofReal ((N:ℝ) * lam ^ ((d:ℝ) + α) * Λ) *
          ((N:ℝ≥0∞) * ∑ b ∈ Used q,
            ENNReal.ofReal ((f b.1 - f b.2) ^ 2) * ω b.1 b.2) :=
        Finset.sum_le_sum hkey
    _ = (ENNReal.ofReal ((N:ℝ) * lam ^ ((d:ℝ) + α) * Λ) * (N:ℝ≥0∞)) *
          ∑ q ∈ hfinA.toFinset, ∑ b ∈ Used q,
            ENNReal.ofReal ((f b.1 - f b.2) ^ 2) * ω b.1 b.2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun q _ => by ring)
    _ ≤ (ENNReal.ofReal ((N:ℝ) * lam ^ ((d:ℝ) + α) * Λ) * (N:ℝ≥0∞)) *
          ((M:ℝ≥0∞) * ∑ b ∈ hfinB.toFinset,
            ENNReal.ofReal ((f b.1 - f b.2) ^ 2) * ω b.1 b.2) :=
        mul_le_mul' le_rfl (sum_select_le Used hUsub _ hUcount)
    _ = ENNReal.ofReal ((N:ℝ) * lam ^ ((d:ℝ) + α) * Λ * ((N:ℝ) * M)) *
          ∑ b ∈ hfinB.toFinset,
            ENNReal.ofReal ((f b.1 - f b.2) ^ 2) * ω b.1 b.2 := by
        have hA : ENNReal.ofReal ((N:ℝ) * lam ^ ((d:ℝ) + α) * Λ * ((N:ℝ) * M))
            = ENNReal.ofReal ((N:ℝ) * lam ^ ((d:ℝ) + α) * Λ) * ((N:ℝ≥0∞) * (M:ℝ≥0∞)) := by
          rw [ENNReal.ofReal_mul
            (by positivity : (0:ℝ) ≤ (N:ℝ) * lam ^ ((d:ℝ) + α) * Λ)]
          congr 1
          rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (N:ℝ)),
            ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
        rw [hA]
        ring

end QFS
