/-
Packaging Theorem 5.15: from the local data of Steps 1–2 to `PathPropsHolds`.

Steps 1 and 2 of the paper's proof are local: they fix a logarithmic scale `n`
and a centre `z ∈ Δ^n ℤ^d` and produce a walk in `G` for every pair `(x, y)` of
lattice points lying in `B_{2√d Δ^n}(z)` at distance in `[Δ^{n-1}, Δ^n)`, with
bounded length, edges of length in `[Δ^{n-1}, 2Δ^n R)` sitting inside
`B_{Δ^n R}(z)`, and the fibre bound `#φ_z^{-1}(p) ≤ K`.

Steps 3–6 are the assembly, and they are what this file proves: given that local
data at *every* scale and centre, Theorem 5.15 follows. Step 3 is the selection
`exists_scale_and_centre`, Step 4 is immediate, Step 5 converts the absolute edge
bounds into bounds relative to `‖x − y‖`, and Step 6 is the multiplicity count —
boundedly many scales (`scale_separation`), boundedly many centres
(`ncard_lattice_scaled_ball_le`), and `K` pairs each.
-/
import QuadraticFormsSobolev.Assembly

open Real Set Metric

namespace QFS

variable {d : ℕ}

/-! ## The length of an unoriented edge

Claim (4) of Theorem 5.15 is about unoriented edges, so their length must be a
function on `Sym2`; it descends because the norm of a difference is symmetric. -/

/-- The length of an unoriented edge. -/
noncomputable def edgeLen : Sym2 (EuclideanSpace ℝ (Fin d)) → ℝ :=
  Sym2.lift ⟨fun a b => ‖a - b‖, fun a b => norm_sub_rev a b⟩

@[simp] lemma edgeLen_mk (a b : EuclideanSpace ℝ (Fin d)) :
    edgeLen s(a, b) = ‖a - b‖ := rfl

@[simp] lemma edgeLen_dart_edge {G : SimpleGraph (EuclideanSpace ℝ (Fin d))} (D : G.Dart) :
    edgeLen D.edge = ‖D.toProd.1 - D.toProd.2‖ := rfl

lemma dart_edge_mem_edges {G : SimpleGraph (EuclideanSpace ℝ (Fin d))}
    {x y : EuclideanSpace ℝ (Fin d)} {w : G.Walk x y} {D : G.Dart} (hD : D ∈ w.darts) :
    D.edge ∈ w.edges :=
  List.mem_map_of_mem hD

/-- Conversely, every edge of a walk comes from a dart. -/
lemma exists_dart_edge {G : SimpleGraph (EuclideanSpace ℝ (Fin d))}
    {x y : EuclideanSpace ℝ (Fin d)} {w : G.Walk x y}
    {e : Sym2 (EuclideanSpace ℝ (Fin d))} (he : e ∈ w.edges) :
    ∃ D ∈ w.darts, D.edge = e := List.mem_map.mp he

/-! ## The pairs handled at a given scale and centre

This is the set `A` of Step 2 of the paper's proof. -/

/-- The set `A` of Step 2: pairs of lattice points inside the ball
`B_{2√d Δ^{m+1}}(Δ^{m+1} z)` whose distance lies in the window
`[Δ^{m-1}, Δ^m)`, with `m ≥ 1`.

The paper's window is `[Δ^{n-1}, Δ^n)` for the town `T(Δ^n, Δ^{n-1})`, i.e. one
scale lower: a pair at distance in `[1, Δ)` would be routed through the town
`T(Δ, 1)`, whose edges can be as short as `1`. Section 6 needs every edge of
`p_xy` to be **longer than `R₀`** — the lower bound in assumption (4) applies
only to such pairs — and claim (4) of Theorem 5.15 does not give that, since it
only bounds an edge below by `λ^{-1}‖x − y‖`. Routing one scale up costs a
factor `Δ` in `λ` and makes every edge at least `Δ > R₀` long. See the README,
Deviation 17. -/
def Admissible (Δ : ℝ) (m : ℕ) (z x y : EuclideanSpace ℝ (Fin d)) : Prop :=
  x ∈ lattice d ∧ y ∈ lattice d ∧ 1 ≤ m ∧
    Δ ^ m ≤ Δ * ‖x - y‖ ∧ ‖x - y‖ < Δ ^ m ∧
    ‖x - Δ ^ (m + 1) • z‖ ≤ 2 * Real.sqrt d * Δ ^ (m + 1) ∧
    ‖y - Δ ^ (m + 1) • z‖ ≤ 2 * Real.sqrt d * Δ ^ (m + 1)

/-- Step 3's selection, at the shifted scale: distinct lattice points are
admissible at some scale `m ≥ 1` and some centre. -/
theorem exists_admissible {Δ : ℝ} (hΔ : 2 ≤ Δ) (hd : 1 ≤ d)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ lattice d) (hy : y ∈ lattice d)
    (hne : x ≠ y) :
    ∃ (m : ℕ) (z : EuclideanSpace ℝ (Fin d)), z ∈ lattice d ∧ Admissible Δ m z x y := by
  have hΔ1 : (1:ℝ) < Δ := by linarith
  have hΔ0 : (0:ℝ) < Δ := by linarith
  obtain ⟨m₀, h1, h2⟩ := exists_scale_of_lattice hΔ1 hx hy hne
  have hs : (0:ℝ) < Δ ^ (m₀ + 1 + 1) := by positivity
  obtain ⟨z, hzlat, hz⟩ := exists_centre (d := d) hs x
  have hsd : (1:ℝ) ≤ Real.sqrt d := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
  have hpow : Δ ^ (m₀ + 1 + 1) = Δ * Δ ^ (m₀ + 1) := by rw [pow_succ]; ring
  have hp0 : (0:ℝ) < Δ ^ (m₀ + 1) := by positivity
  refine ⟨m₀ + 1, z, hzlat, hx, hy, by omega, ?_, h2, ?_, ?_⟩
  · rw [pow_succ]
    nlinarith
  · calc ‖x - Δ ^ (m₀ + 1 + 1) • z‖ ≤ Δ ^ (m₀ + 1 + 1) / 2 * Real.sqrt d := hz
      _ ≤ 2 * Real.sqrt d * Δ ^ (m₀ + 1 + 1) := by nlinarith
  · have htri : ‖y - Δ ^ (m₀ + 1 + 1) • z‖ ≤ ‖x - y‖ + ‖x - Δ ^ (m₀ + 1 + 1) • z‖ := by
      have he : y - Δ ^ (m₀ + 1 + 1) • z
          = -(x - y) + (x - Δ ^ (m₀ + 1 + 1) • z) := by abel
      calc ‖y - Δ ^ (m₀ + 1 + 1) • z‖
          = ‖-(x - y) + (x - Δ ^ (m₀ + 1 + 1) • z)‖ := by rw [he]
        _ ≤ ‖-(x - y)‖ + ‖x - Δ ^ (m₀ + 1 + 1) • z‖ := norm_add_le _ _
        _ = ‖x - y‖ + ‖x - Δ ^ (m₀ + 1 + 1) • z‖ := by rw [norm_neg]
    have hxz : ‖x - Δ ^ (m₀ + 1 + 1) • z‖ ≤ Δ ^ (m₀ + 1 + 1) / 2 * Real.sqrt d := hz
    rw [hpow] at hxz htri ⊢
    nlinarith

/-! ## The local data of Steps 1–2 -/

/-- The output of Steps 1 and 2 at one scale `m` and one centre `z`: a walk in
`G` for every admissible pair, with

* `length_le`: at most `t` edges (Step 1's block count, times the two first jumps);
* `edge_lb`: every edge has length at least `Δ^m` (Step 5's lower bound — it
  holds because favored-graph-adjacent blocks of the town `T(Δ^{m+1}, Δ^m)` are
  separated by at least `Δ^{m+1} − Δ^m ≥ Δ^m`);
* `edge_near`: every endpoint of every edge lies in `B_{Δ^{m+1}R}(Δ^{m+1}z)`, so
  the centre is recoverable from the edge (Step 6) and Step 5's upper bound
  `2Δ^{m+1}R` follows (`ScaleData.edgeLen_lt`);
* `fibre_le`: at most `K` admissible pairs share a walk through a given edge —
  the fibre bound on `φ_z` of Step 2, composed with the injectivity of the cyclic
  scheme.

Bundling the local data this way is what lets Steps 3–6 be proved separately from
Steps 1–2: `pathProps_of_scaleData` below consumes exactly these fields. -/
structure ScaleData (Γ : Configuration (EuclideanSpace ℝ (Fin d))) (Δ R : ℝ)
    (t K m : ℕ) (z : EuclideanSpace ℝ (Fin d)) where
  /-- The walk attached to an admissible pair. -/
  path : ∀ x y : EuclideanSpace ℝ (Fin d), Admissible Δ m z x y →
    (latticeGraph Γ).Walk x y
  length_le : ∀ x y h, (path x y h).length ≤ t
  edge_lb : ∀ x y h, ∀ e ∈ (path x y h).edges, Δ ^ m ≤ edgeLen e
  edge_near : ∀ x y h, ∀ e ∈ (path x y h).edges, ∀ u ∈ e,
    ‖Δ ^ (m + 1) • z - u‖ < Δ ^ (m + 1) * R
  fibre_le : ∀ e : Sym2 (EuclideanSpace ℝ (Fin d)),
    {q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      ∃ h : Admissible Δ m z q.1 q.2, e ∈ ((path q.1 q.2 h)).edges}.encard ≤ (K : ℕ∞)

variable {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {Δ R : ℝ} {t K m : ℕ}
  {z : EuclideanSpace ℝ (Fin d)}

/-- The upper bound of Step 5 is not extra data: both endpoints of an edge lie in
the open ball `B_{Δ^{m+1}R}(Δ^{m+1}z)`, so the edge is shorter than its diameter.
This is how the paper gets the bound `2Δ^n R` too. -/
theorem ScaleData.edgeLen_lt (D : ScaleData Γ Δ R t K m z)
    (x y : EuclideanSpace ℝ (Fin d)) (h : Admissible Δ m z x y) :
    ∀ e ∈ (D.path x y h).edges, edgeLen e < 2 * Δ ^ (m + 1) * R := by
  intro e
  induction e using Sym2.ind with
  | _ u v =>
    intro he
    have hu := D.edge_near x y h _ he u (Sym2.mem_mk_left u v)
    have hv := D.edge_near x y h _ he v (Sym2.mem_mk_right u v)
    have htri : ‖u - v‖ ≤ ‖Δ ^ (m + 1) • z - u‖ + ‖Δ ^ (m + 1) • z - v‖ := by
      have he2 : u - v = -(Δ ^ (m + 1) • z - u) + (Δ ^ (m + 1) • z - v) := by abel
      calc ‖u - v‖ = ‖-(Δ ^ (m + 1) • z - u) + (Δ ^ (m + 1) • z - v)‖ := by rw [he2]
        _ ≤ ‖-(Δ ^ (m + 1) • z - u)‖ + ‖Δ ^ (m + 1) • z - v‖ := norm_add_le _ _
        _ = ‖Δ ^ (m + 1) • z - u‖ + ‖Δ ^ (m + 1) • z - v‖ := by rw [norm_neg]
    rw [edgeLen_mk]
    linarith

/-- The fibre bound of a `ScaleData`, transported to pairs of points of the
lattice as a type — which is how `PathProps` indexes its family. -/
theorem ScaleData.fibre_le_latticePt (D : ScaleData Γ Δ R t K m z)
    (e : Sym2 (EuclideanSpace ℝ (Fin d))) :
    {q : LatticePt d × LatticePt d |
      ∃ h : Admissible Δ m z q.1.1 q.2.1,
        e ∈ (D.path q.1.1 q.2.1 h).edges}.encard ≤ (K : ℕ∞) := by
  have hinj : Function.Injective
      (fun q : LatticePt d × LatticePt d => (q.1.1, q.2.1)) := by
    intro q q' hq
    simp only [Prod.mk.injEq] at hq
    exact Prod.ext (Subtype.ext hq.1) (Subtype.ext hq.2)
  calc {q : LatticePt d × LatticePt d | ∃ h : Admissible Δ m z q.1.1 q.2.1,
            e ∈ (D.path q.1.1 q.2.1 h).edges}.encard
      = ((fun q : LatticePt d × LatticePt d => (q.1.1, q.2.1)) ''
          {q : LatticePt d × LatticePt d | ∃ h : Admissible Δ m z q.1.1 q.2.1,
            e ∈ (D.path q.1.1 q.2.1 h).edges}).encard := (hinj.injOn.encard_image).symm
    _ ≤ {q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
          ∃ h : Admissible Δ m z q.1 q.2, e ∈ (D.path q.1 q.2 h).edges}.encard := by
        refine Set.encard_le_encard ?_
        rintro ⟨u, v⟩ ⟨q, hq, hqe⟩
        rw [← hqe]
        exact hq
    _ ≤ (K : ℕ∞) := D.fibre_le e

/-! ## Shrinking the configuration

Theorem 5.15 is proved for a configuration with boundedly many types, obtained
from `ref_config_uniform`; since that configuration's cones sit inside the
original's, its graph is a subgraph and its walks are walks of the original. -/

/-- A pointwise smaller configuration has a smaller graph. -/
theorem latticeGraph_mono {Γ Γ' : Configuration (EuclideanSpace ℝ (Fin d))}
    (hsub : ∀ x, (Γ' x).carrier ⊆ (Γ x).carrier) : latticeGraph Γ' ≤ latticeGraph Γ :=
  fun _ _ h => ⟨h.1, h.2.1, h.2.2.imp (fun hc => hsub _ hc) (fun hc => hsub _ hc)⟩

/-- **Theorem 5.15 transfers upwards along `Γ' ≤ Γ`.** -/
theorem PathProps.mono_config {Γ Γ' : Configuration (EuclideanSpace ℝ (Fin d))}
    (hsub : ∀ x, (Γ' x).carrier ⊆ (Γ x).carrier) {N M : ℕ} {lam : ℝ}
    (h : PathProps Γ' N M lam) : PathProps Γ N M lam := by
  obtain ⟨p, hlen, hfib, hdart⟩ := h
  have hle := latticeGraph_mono hsub
  have hedge : ∀ x y : LatticePt d, ∀ e ∈ (p x y).edges, e ∈ (latticeGraph Γ).edgeSet :=
    fun x y e he => SimpleGraph.edgeSet_mono hle ((p x y).edges_subset_edgeSet he)
  refine ⟨fun x y => (p x y).transfer (latticeGraph Γ) (hedge x y), fun x y => ?_,
    fun e => ?_, fun x y D hD => ?_⟩
  · rw [SimpleGraph.Walk.length_transfer]; exact hlen x y
  · refine le_trans (le_of_eq ?_) (hfib e)
    congr 1
    ext q
    simp only [Set.mem_ofPred_eq, SimpleGraph.Walk.edges_transfer]
  · have hDe : D.edge ∈ (p x y).edges := by
      rw [← SimpleGraph.Walk.edges_transfer (p x y) (hedge x y)]
      exact dart_edge_mem_edges hD
    obtain ⟨D', hD', hD'e⟩ := exists_dart_edge hDe
    have hnorm : ‖D.toProd.1 - D.toProd.2‖ = ‖D'.toProd.1 - D'.toProd.2‖ := by
      rw [← edgeLen_dart_edge D, ← edgeLen_dart_edge D', hD'e]
    rw [hnorm]
    exact hdart x y D' hD'

/-! ## A strengthening of claim (4)

Section 6 chains along `p_xy` and, at each edge, applies the *lower* bound of
assumption (4), which holds only for pairs at distance more than `R₀`. Claim
(4) of Theorem 5.15 bounds an edge below only by `λ^{-1}‖x − y‖`, which for
`‖x − y‖` just above `R₀` is far less than `R₀`. `PathPropsLong` records the
extra fact the construction actually delivers: every edge is longer than `R₀`.
See the README, Deviation 17. -/

/-- Theorem 5.15 with the extra clause Section 6 needs. -/
def PathPropsLong (Γ : Configuration (EuclideanSpace ℝ (Fin d))) (N M : ℕ)
    (lam R₀ : ℝ) : Prop :=
  ∃ p : ∀ x y : LatticePt d, (latticeGraph Γ).Walk x.1 y.1,
    (∀ x y, (p x y).length ≤ N) ∧
    (∀ e : Sym2 (EuclideanSpace ℝ (Fin d)),
      {q : LatticePt d × LatticePt d | e ∈ (p q.1 q.2).edges}.encard ≤ (M : ℕ∞)) ∧
    (∀ x y, ∀ e ∈ (p x y).darts,
      lam⁻¹ * ‖x.1 - y.1‖ ≤ ‖e.toProd.1 - e.toProd.2‖ ∧
        ‖e.toProd.1 - e.toProd.2‖ ≤ lam * ‖x.1 - y.1‖ ∧
        R₀ < ‖e.toProd.1 - e.toProd.2‖)

/-- Forgetting the extra clause gives the paper's statement. -/
theorem PathPropsLong.toPathProps {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {N M : ℕ} {lam R₀ : ℝ} (h : PathPropsLong Γ N M lam R₀) : PathProps Γ N M lam := by
  obtain ⟨p, h1, h2, h3⟩ := h
  exact ⟨p, h1, h2, fun x y D hD => ⟨(h3 x y D hD).1, (h3 x y D hD).2.1⟩⟩

/-- Theorem 5.15 in the strengthened form, with constants independent of `Γ`. -/
def PathPropsLongHolds (d : ℕ) (ϑ R₀ : ℝ) : Prop :=
  ∃ (N M : ℕ) (lam : ℝ), 0 < N ∧ 0 < M ∧ R₀ ≤ lam ∧
    ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ →
      PathPropsLong Γ N M lam R₀

theorem PathPropsLongHolds.toPathPropsHolds {ϑ R₀ : ℝ}
    (h : PathPropsLongHolds d ϑ R₀) : PathPropsHolds d ϑ R₀ := by
  obtain ⟨N, M, lam, hN, hM, hlam, hp⟩ := h
  exact ⟨N, M, lam, hN, hM, hlam, fun Γ hΓ => (hp Γ hΓ).toPathProps⟩

/-- `PathPropsLong` transfers upwards along `Γ' ≤ Γ` too. -/
theorem PathPropsLong.mono_config {Γ Γ' : Configuration (EuclideanSpace ℝ (Fin d))}
    (hsub : ∀ x, (Γ' x).carrier ⊆ (Γ x).carrier) {N M : ℕ} {lam R₀ : ℝ}
    (h : PathPropsLong Γ' N M lam R₀) : PathPropsLong Γ N M lam R₀ := by
  obtain ⟨p, hlen, hfib, hdart⟩ := h
  have hle := latticeGraph_mono hsub
  have hedge : ∀ x y : LatticePt d, ∀ e ∈ (p x y).edges, e ∈ (latticeGraph Γ).edgeSet :=
    fun x y e he => SimpleGraph.edgeSet_mono hle ((p x y).edges_subset_edgeSet he)
  refine ⟨fun x y => (p x y).transfer (latticeGraph Γ) (hedge x y), fun x y => ?_,
    fun e => ?_, fun x y D hD => ?_⟩
  · rw [SimpleGraph.Walk.length_transfer]; exact hlen x y
  · refine le_trans (le_of_eq ?_) (hfib e)
    congr 1
    ext q
    simp only [Set.mem_ofPred_eq, SimpleGraph.Walk.edges_transfer]
  · have hDe : D.edge ∈ (p x y).edges := by
      rw [← SimpleGraph.Walk.edges_transfer (p x y) (hedge x y)]
      exact dart_edge_mem_edges hD
    obtain ⟨D', hD', hD'e⟩ := exists_dart_edge hDe
    have hnorm : ‖D.toProd.1 - D.toProd.2‖ = ‖D'.toProd.1 - D'.toProd.2‖ := by
      rw [← edgeLen_dart_edge D, ← edgeLen_dart_edge D', hD'e]
    rw [hnorm]
    exact hdart x y D' hD'

/-! ## Steps 3–6: the assembly

Given the local data at every scale and centre, Theorem 5.15 follows. The
constants are the paper's: `N = t` is Step 1's block count, `λ = 2ΔR` is Step 5's,
and `M = (2C+1)(2⌈R⌉+1)^d K` is Step 6's product of the three bounds — at most
`2C+1` scales carry a given edge length, at most `(2⌈R⌉+1)^d` centres have their
ball containing the edge, and each `(scale, centre)` contributes at most `K`
pairs. -/

/-- **Steps 3–6 of Theorem 5.15.** The local data of Steps 1–2, available at every
scale and centre, assembles into the global path family of Theorem 5.15 — in the
strengthened form `PathPropsLong`, which also records that every edge is longer
than `R₀`. -/
theorem pathPropsLong_of_scaleData {C : ℕ} {R₀ : ℝ} (hd : 1 ≤ d) (hΔ : 2 ≤ Δ)
    (hR : 1 ≤ R) (hR₀ : R₀ < Δ) (hC : 2 * Δ * R ≤ 2 ^ C)
    (data : ∀ (m : ℕ) (z : EuclideanSpace ℝ (Fin d)), z ∈ lattice d →
      ScaleData Γ Δ R t K m z) :
    PathPropsLong Γ t ((2 * C + 1) * (2 * ⌈R⌉₊ + 1) ^ d * K) (2 * Δ ^ 2 * R) R₀ := by
  classical
  have hΔ1 : (1:ℝ) < Δ := by linarith
  have hΔ0 : (0:ℝ) < Δ := by linarith
  have hR0 : (0:ℝ) < R := by linarith
  have hlam : (0:ℝ) < 2 * Δ ^ 2 * R := by positivity
  -- **Step 3.** Attach to every pair a walk together with the label `(m, z)` of
  -- the scale and centre it was built at, and everything Steps 4–6 need.
  have key : ∀ x y : LatticePt d, ∃ (mz : ℕ × EuclideanSpace ℝ (Fin d))
      (w : (latticeGraph Γ).Walk x.1 y.1), w.length ≤ t ∧
      ∀ e ∈ w.edges,
        Δ ^ mz.1 ≤ edgeLen e ∧ edgeLen e < 2 * Δ ^ (mz.1 + 1) * R ∧
        (∀ u ∈ e, ‖Δ ^ (mz.1 + 1) • mz.2 - u‖ < Δ ^ (mz.1 + 1) * R) ∧
        mz.2 ∈ lattice d ∧ 1 ≤ mz.1 ∧
        Δ ^ mz.1 ≤ Δ * ‖x.1 - y.1‖ ∧ ‖x.1 - y.1‖ < Δ ^ mz.1 ∧
        (∃ (hz : mz.2 ∈ lattice d) (h : Admissible Δ mz.1 mz.2 x.1 y.1),
          e ∈ ((data mz.1 mz.2 hz).path x.1 y.1 h).edges) := by
    intro x y
    by_cases hxy : x.1 = y.1
    · refine ⟨(0, 0), (SimpleGraph.Walk.nil (u := x.1)).copy rfl hxy, ?_, ?_⟩
      · simp
      · intro e he
        simp [SimpleGraph.Walk.edges_copy] at he
    · obtain ⟨m, z, hzlat, hadm⟩ := exists_admissible hΔ hd x.2 y.2 hxy
      refine ⟨(m, z), (data m z hzlat).path x.1 y.1 hadm,
        (data m z hzlat).length_le _ _ _, ?_⟩
      intro e he
      exact ⟨(data m z hzlat).edge_lb _ _ _ e he,
        (data m z hzlat).edgeLen_lt _ _ _ e he,
        (data m z hzlat).edge_near _ _ _ e he, hzlat,
        hadm.2.2.1, hadm.2.2.2.1, hadm.2.2.2.2.1, ⟨hzlat, hadm, he⟩⟩
  choose sel p hlen hedge using key
  refine ⟨p, hlen, ?_, ?_⟩
  · -- **Step 6: the multiplicity bound.**
    intro e
    induction e using Sym2.ind with
    | _ a b =>
    rcases Set.eq_empty_or_nonempty
        {q : LatticePt d × LatticePt d | s(a, b) ∈ (p q.1 q.2).edges} with hT | ⟨q₀, hq₀⟩
    · rw [hT]; simp
    -- The reference scale, from any one pair using the edge.
    obtain ⟨hlb₀, hub₀, -, -, -, -, -, -⟩ := hedge q₀.1 q₀.2 s(a, b) hq₀
    -- The two index sets: `2C+1` scales and, at each, `(2⌈R⌉+1)^d` centres.
    refine le_trans (Set.encard_le_encard (?_ :
      {q : LatticePt d × LatticePt d | s(a, b) ∈ (p q.1 q.2).edges} ⊆
        ⋃ n ∈ Finset.Icc ((sel q₀.1 q₀.2).1 - C) ((sel q₀.1 q₀.2).1 + C),
          ⋃ w ∈ (lattice_scaled_ball_finite (s := Δ ^ (n + 1)) (R := R)
              (pow_pos hΔ0 _) a).toFinset,
            {q : LatticePt d × LatticePt d | ∃ (hw : w ∈ lattice d)
              (h : Admissible Δ n w q.1.1 q.2.1),
              s(a, b) ∈ ((data n w hw).path q.1.1 q.2.1 h).edges})) ?_
    · -- Every pair using the edge is indexed by its own scale and centre.
      rintro q hq
      obtain ⟨hlb, hub, hnear, hwlat, -, -, -, hex⟩ := hedge q.1 q.2 s(a, b) hq
      refine Set.mem_biUnion (Finset.mem_Icc.mpr ⟨?_, ?_⟩)
        (Set.mem_biUnion (Set.Finite.mem_toFinset _ |>.mpr ⟨hwlat, ?_⟩) hex)
      · have := scale_separation hΔ hR0 hC (L := edgeLen s(a, b)) hub hlb₀
        omega
      · exact scale_separation hΔ hR0 hC (L := edgeLen s(a, b)) hub₀ hlb
      · exact hnear a (Sym2.mem_mk_left a b)
    · -- Multiply the three bounds.
      have hZ : ∀ n : ℕ, ((lattice_scaled_ball_finite (s := Δ ^ (n + 1)) (R := R)
          (pow_pos hΔ0 _) a).toFinset.card) ≤ (2 * ⌈R⌉₊ + 1) ^ d := by
        intro n
        rw [← Set.ncard_eq_toFinset_card _ (lattice_scaled_ball_finite _ a)]
        exacts [ncard_lattice_scaled_ball_le (pow_pos hΔ0 _) a, pow_pos hΔ0 _]
      have hI : (Finset.Icc ((sel q₀.1 q₀.2).1 - C) ((sel q₀.1 q₀.2).1 + C)).card
          ≤ 2 * C + 1 := by
        rw [Nat.card_Icc]; omega
      calc (⋃ n ∈ Finset.Icc ((sel q₀.1 q₀.2).1 - C) ((sel q₀.1 q₀.2).1 + C),
              ⋃ w ∈ (lattice_scaled_ball_finite (s := Δ ^ (n + 1)) (R := R)
                  (pow_pos hΔ0 _) a).toFinset,
                {q : LatticePt d × LatticePt d | ∃ (hw : w ∈ lattice d)
                  (h : Admissible Δ n w q.1.1 q.2.1),
                  s(a, b) ∈ ((data n w hw).path q.1.1 q.2.1 h).edges}).encard
          ≤ ∑ n ∈ Finset.Icc ((sel q₀.1 q₀.2).1 - C) ((sel q₀.1 q₀.2).1 + C),
              (⋃ w ∈ (lattice_scaled_ball_finite (s := Δ ^ (n + 1)) (R := R)
                  (pow_pos hΔ0 _) a).toFinset,
                {q : LatticePt d × LatticePt d | ∃ (hw : w ∈ lattice d)
                  (h : Admissible Δ n w q.1.1 q.2.1),
                  s(a, b) ∈ ((data n w hw).path q.1.1 q.2.1 h).edges}).encard :=
            Finset.set_encard_biUnion_le _ _
        _ ≤ ∑ n ∈ Finset.Icc ((sel q₀.1 q₀.2).1 - C) ((sel q₀.1 q₀.2).1 + C),
              ∑ _w ∈ (lattice_scaled_ball_finite (s := Δ ^ (n + 1)) (R := R)
                  (pow_pos hΔ0 _) a).toFinset, (K : ℕ∞) := by
            refine Finset.sum_le_sum (fun n _ => ?_)
            refine le_trans (Finset.set_encard_biUnion_le _ _) (Finset.sum_le_sum ?_)
            intro w hw
            have hwlat : w ∈ lattice d :=
              ((Set.Finite.mem_toFinset _).mp hw).1
            refine le_trans (Set.encard_le_encard ?_)
              ((data n w hwlat).fibre_le_latticePt s(a, b))
            rintro q ⟨hw', h, hq⟩
            exact ⟨h, hq⟩
        _ = ∑ n ∈ Finset.Icc ((sel q₀.1 q₀.2).1 - C) ((sel q₀.1 q₀.2).1 + C),
              (((lattice_scaled_ball_finite (s := Δ ^ (n + 1)) (R := R)
                (pow_pos hΔ0 _) a).toFinset.card * K : ℕ) : ℕ∞) := by
            refine Finset.sum_congr rfl (fun n _ => ?_)
            rw [Finset.sum_const, nsmul_eq_mul]
            push_cast
            ring
        _ ≤ ∑ _n ∈ Finset.Icc ((sel q₀.1 q₀.2).1 - C) ((sel q₀.1 q₀.2).1 + C),
              (((2 * ⌈R⌉₊ + 1) ^ d * K : ℕ) : ℕ∞) := by
            refine Finset.sum_le_sum (fun n _ => ?_)
            exact_mod_cast Nat.mul_le_mul_right K (hZ n)
        _ = (((Finset.Icc ((sel q₀.1 q₀.2).1 - C) ((sel q₀.1 q₀.2).1 + C)).card *
              ((2 * ⌈R⌉₊ + 1) ^ d * K) : ℕ) : ℕ∞) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            push_cast
            ring
        _ ≤ (((2 * C + 1) * (2 * ⌈R⌉₊ + 1) ^ d * K : ℕ) : ℕ∞) := by
            have := Nat.mul_le_mul_right ((2 * ⌈R⌉₊ + 1) ^ d * K) hI
            exact_mod_cast le_trans this (by rw [Nat.mul_assoc])
  · -- **Steps 4 and 5: the length of each edge, relative to `‖x − y‖`.**
    intro x y D hD
    obtain ⟨hlb, hub, -, -, hm1, hxlb, hxub, -⟩ :=
      hedge x y D.edge (dart_edge_mem_edges hD)
    rw [edgeLen_dart_edge] at hlb hub
    have hpow : Δ ^ ((sel x y).1 + 1) = Δ * Δ ^ (sel x y).1 := by rw [pow_succ]; ring
    have hp0 : (0:ℝ) < Δ ^ (sel x y).1 := pow_pos hΔ0 _
    have hΔm : Δ ≤ Δ ^ (sel x y).1 := le_self_pow₀ hΔ1.le (by omega)
    have hxy0 : (0:ℝ) ≤ ‖x.1 - y.1‖ := norm_nonneg _
    have hDn : (0:ℝ) ≤ ‖D.toProd.1 - D.toProd.2‖ := norm_nonneg _
    have hle : ‖x.1 - y.1‖ ≤ ‖D.toProd.1 - D.toProd.2‖ := le_of_lt (lt_of_lt_of_le hxub hlb)
    have hone : (1:ℝ) ≤ 2 * Δ ^ 2 * R := by nlinarith
    refine ⟨?_, ?_, ?_⟩
    · rw [inv_mul_le_iff₀ hlam]
      nlinarith
    · have hmul : 2 * Δ * R * Δ ^ (sel x y).1 ≤ 2 * Δ * R * (Δ * ‖x.1 - y.1‖) :=
        mul_le_mul_of_nonneg_left hxlb (by positivity)
      nlinarith
    · linarith

/-- **Theorem 5.15, packaged.** If the local data of Steps 1–2 is available at
every scale and every centre, uniformly in the configuration, then the theorem
holds with the paper's constants — in the strengthened form.

The three constants are quantified before `Γ`, as the paper requires: they are
built from `Δ`, `R`, `t`, `K` and `C` alone. -/
theorem pathPropsLongHolds_of_scaleData {ϑ R₀ : ℝ} {C : ℕ} (hd : 1 ≤ d) (hΔ : 2 ≤ Δ)
    (hR : 1 ≤ R) (hC : 2 * Δ * R ≤ 2 ^ C) (ht : 0 < t) (hK : 0 < K)
    (hR₀ : R₀ < Δ)
    (data : ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ →
      ∀ (m : ℕ) (z : EuclideanSpace ℝ (Fin d)), z ∈ lattice d →
        ScaleData Γ Δ R t K m z) :
    PathPropsLongHolds d ϑ R₀ := by
  have hΔ0 : (0:ℝ) < Δ := by linarith
  have hR0 : (0:ℝ) < R := by linarith
  refine ⟨t, (2 * C + 1) * (2 * ⌈R⌉₊ + 1) ^ d * K, 2 * Δ ^ 2 * R, ht, ?_, by nlinarith,
    fun Γ hΓ => pathPropsLong_of_scaleData (R₀ := R₀) hd hΔ hR hR₀ hC (data Γ hΓ)⟩
  exact Nat.mul_pos (Nat.mul_pos (by omega) (Nat.pow_pos (by omega))) hK

/-- The same, in the paper's form. -/
theorem pathPropsHolds_of_scaleData {ϑ R₀ : ℝ} {C : ℕ} (hd : 1 ≤ d) (hΔ : 2 ≤ Δ)
    (hR : 1 ≤ R) (hC : 2 * Δ * R ≤ 2 ^ C) (ht : 0 < t) (hK : 0 < K)
    (hR₀ : R₀ < Δ)
    (data : ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ →
      ∀ (m : ℕ) (z : EuclideanSpace ℝ (Fin d)), z ∈ lattice d →
        ScaleData Γ Δ R t K m z) :
    PathPropsHolds d ϑ R₀ :=
  (pathPropsLongHolds_of_scaleData hd hΔ hR hC ht hK hR₀ data).toPathPropsHolds

end QFS
