/-
Steps 1 and 2 of the proof of Theorem 5.15: the local path family.

The two steps together produce, at one logarithmic scale and one centre, a walk
in `G` for every admissible pair — the `QFS.ScaleData` that `PathAssembly`
consumes. This file builds the ingredients: the indexing of the majority sets by
`ZMod a`, and the two balanced hashes that choose the scheme's parameters.

*Why hashes.* The paper's `φ_z : A → M` is only required to be balanced
globally, `#φ_z⁻¹(p) ≤ K`. That is not enough for Step 6. A first-jump edge
`{x, q}` is used by every partner `y` of `x` whose assigned walk carries the
index of `q` at `x`'s position along the block walk; the walks with a fixed index
at a fixed position number `a`, so their capacity `K·a` exceeds the `≍ Δ^{nd}`
partners of `x`, and an adversarial balanced `φ_z` may route all of them through
`q`. The multiplicity of that edge is then unbounded.

The repair stays inside the paper's scheme and only fixes its parameters: take
`i = f(y) + g(x)` and `i + j = g(x)`, where `f` and `g` are balanced maps of the
ball to `ZMod a`. The alternating labels are then `α = f(y) + g(x)` and
`β = g(x)`, so

* every consecutive pair `{α, β}` determines both `f(y)` and `g(x)`, bounding an
  interior edge's multiplicity by `#f⁻¹ · #g⁻¹` — this is `cyclic_pair_injective`
  again;
* `α` is, for fixed `x`, a translate of `f` and hence balanced in `y`, which
  bounds the first-jump edge at `x`;
* both `α` and `β` are, for fixed `y`, translates of `g` and hence balanced in
  `x`, which bounds the first-jump edge at `y` — whatever the parity of the block
  walk's length.

The last point is why `α` carries *both* hashes: with `α = f(y)` and `β = g(x)`
an even-length block walk would end on `α`, which is constant in `x`.
-/
import QuadraticFormsSobolev.PathAssembly

open Real Set Metric

namespace QFS

variable {d : ℕ}

/-! ## Balanced hashes

`exists_fun_fiber_le` with `M = ZMod a` and no constraint on where each element
goes. -/

/-- **A balanced hash.** If `#A ≤ K a`, the elements of `A` can be labelled by
`ZMod a` with no label used more than `K` times. -/
theorem exists_hash {α : Type*} {a K : ℕ} [NeZero a] (A : Finset α)
    (hA : A.card ≤ K * a) :
    ∃ f : α → ZMod a, ∀ γ : ZMod a, (A.filter fun x => f x = γ).card ≤ K := by
  classical
  obtain ⟨f, -, hfib⟩ :=
    exists_fun_fiber_le (K := K) a (Finset.univ : Finset (ZMod a)) (by simp [ZMod.card])
      ⟨0, Finset.mem_univ _⟩ A hA
  exact ⟨f, hfib⟩

/-! ## Indexing a majority set by `ZMod a`

The paper writes "WLOG we assume that every majority set contains exactly `a`
different elements" and then treats a block as the tuple `(q^k_i)_{1 ≤ i ≤ a}`.
Formally that is an injection `ZMod a ↪ S`, which exists as soon as `a ≤ #S`. -/

/-- **The paper's "WLOG".** A finite set with at least `a` elements can be indexed
injectively by `ZMod a`. -/
theorem exists_indexed_rep {α : Type*} {a : ℕ} [NeZero a] {S : Set α}
    (hcard : a ≤ S.ncard) :
    ∃ ρ : ZMod a → α, Function.Injective ρ ∧ ∀ i, ρ i ∈ S := by
  classical
  -- `S` is finite: `ncard` is `0` on infinite sets, and `a ≠ 0`.
  have hSfin : S.Finite := by
    by_contra hinf
    rw [Set.Infinite.ncard hinf] at hcard
    exact NeZero.ne a (Nat.le_zero.mp hcard)
  obtain ⟨T, hTS, hT⟩ := Set.exists_subset_card_eq hcard
  have hTfin : T.Finite := hSfin.subset hTS
  have hcardF : hTfin.toFinset.card = a := by
    rw [← Set.ncard_eq_toFinset_card T hTfin]; exact hT
  have e1 : ZMod a ≃ Fin a := Fintype.equivFinOfCardEq (ZMod.card a)
  have e2 : Fin a ≃ {x // x ∈ hTfin.toFinset} :=
    (hTfin.toFinset.equivFin.trans (finCongr hcardF)).symm
  refine ⟨fun i => ((e2 (e1 i)) : α), ?_, fun i => ?_⟩
  · intro i j hij
    exact e1.injective (e2.injective (Subtype.ext hij))
  · exact hTS (hTfin.mem_toFinset.mp (e2 (e1 i)).2)

/-! ## The one-point part of admissibility -/

/-- A lattice point in the ball `B_{2√d Δ^{m+1}}(Δ^{m+1}z)` — the condition each
of `x` and `y` satisfies separately in `Admissible`. -/
def AdmissiblePt (Δ : ℝ) (m : ℕ) (z x : EuclideanSpace ℝ (Fin d)) : Prop :=
  x ∈ lattice d ∧ ‖x - Δ ^ (m + 1) • z‖ ≤ 2 * Real.sqrt d * Δ ^ (m + 1)

lemma Admissible.left {Δ : ℝ} {m : ℕ} {z x y : EuclideanSpace ℝ (Fin d)}
    (h : Admissible Δ m z x y) : AdmissiblePt Δ m z x := ⟨h.1, h.2.2.2.2.1⟩

lemma Admissible.right {Δ : ℝ} {m : ℕ} {z x y : EuclideanSpace ℝ (Fin d)}
    (h : Admissible Δ m z x y) : AdmissiblePt Δ m z y := ⟨h.2.1, h.2.2.2.2.2⟩

/-! ## What an edge reveals

An edge of the assembled walk is the first jump, the last jump, or an interior
edge of the lift. In each case it pins down enough of `g x` and `f y` for the
multiplicity count. -/

/-- The information an edge of the assembled walk carries about the pair that
used it: it is the first jump (an endpoint *is* `x`, and the other endpoint's
index is `α = f y + g x`), the last jump (an endpoint is `y`, and the other
endpoint's index is `α` or `β = g x`), or an interior edge (one endpoint's index
is `β` and the other's is `α`). -/
def Reveals {a : ℕ} (f g idx : EuclideanSpace ℝ (Fin d) → ZMod a)
    (e : Sym2 (EuclideanSpace ℝ (Fin d))) (x y : EuclideanSpace ℝ (Fin d)) : Prop :=
  (∃ p ∈ e, ∃ q ∈ e, p = x ∧ f y + g x = idx q) ∨
  (∃ p ∈ e, ∃ q ∈ e, p = y ∧ (g x = idx q ∨ f y + g x = idx q)) ∨
  (∃ p ∈ e, ∃ q ∈ e, g x = idx q ∧ f y + g x = idx p)

/-- **Step 6's input.** Whatever an edge reveals, it confines `g x` to one of
eight values and `f y` to one of nine, all computed from the edge alone. So if
`f` and `g` have fibres of size at most `K₁` on the admissible points, at most
`72 K₁²` admissible pairs can have used the edge. -/
theorem encard_reveals_le {a K₁ : ℕ} (f g idx : EuclideanSpace ℝ (Fin d) → ZMod a)
    (P : EuclideanSpace ℝ (Fin d) → Prop)
    (hf : ∀ γ, {y | P y ∧ f y = γ}.encard ≤ (K₁ : ℕ∞))
    (hg : ∀ γ, {x | P x ∧ g x = γ}.encard ≤ (K₁ : ℕ∞))
    (e : Sym2 (EuclideanSpace ℝ (Fin d))) :
    {q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      P q.1 ∧ P q.2 ∧ Reveals f g idx e q.1 q.2}.encard ≤ ((72 * K₁ * K₁ : ℕ) : ℕ∞) := by
  classical
  induction e using Sym2.ind with
  | _ u v =>
  set G : Finset (ZMod a) :=
    {g u, g v, idx u, idx v, idx u - f u, idx u - f v, idx v - f u, idx v - f v} with hG
  set F : Finset (ZMod a) :=
    {f u, f v, idx u - g u, idx u - g v, idx v - g u, idx v - g v, 0,
      idx u - idx v, idx v - idx u} with hF
  have hGcard : G.card ≤ 8 := by
    rw [hG]
    exact le_trans (Finset.card_insert_le _ _) (by
      refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_))
      refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
      refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
      refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
      refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
      exact le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (by simp)))
  have hFcard : F.card ≤ 9 := by
    rw [hF]
    refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
    refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
    refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
    refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
    refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
    refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
    refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
    exact le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (by simp))
  -- what the edge reveals, read off as membership in `G` and `F`
  have hkey : ∀ x y : EuclideanSpace ℝ (Fin d), Reveals f g idx s(u, v) x y →
      g x ∈ G ∧ f y ∈ F := by
    intro x y hrev
    rcases hrev with ⟨p, hp, q, hq, hpx, hfy⟩ | ⟨p, hp, q, hq, hpy, hgx⟩ |
      ⟨p, hp, q, hq, hgx, hfy⟩
    · rw [Sym2.mem_iff] at hp hq
      rw [hpx] at hp
      have hfy' : f y = idx q - g x := eq_sub_of_add_eq hfy
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
        rw [hG, hF] <;> rw [hfy'] <;> simp
    · rw [Sym2.mem_iff] at hp hq
      rw [hpy] at hp
      refine ⟨?_, ?_⟩
      · rcases hgx with hgx | hgx
        · rcases hq with rfl | rfl <;> rw [hG, hgx] <;> simp
        · have : g x = idx q - f y := by rw [← hgx]; ring
          rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> rw [hG, this] <;> simp
      · rcases hp with rfl | rfl <;> rw [hF] <;> simp
    · rw [Sym2.mem_iff] at hp hq
      have hfy' : f y = idx p - idx q := by
        rw [← hfy, hgx]; ring
      refine ⟨?_, ?_⟩
      · rcases hq with rfl | rfl <;> rw [hG, hgx] <;> simp
      · rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> rw [hF, hfy'] <;> simp
  -- the pairs sit in a product of two small unions of fibres
  have hsub : {q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      P q.1 ∧ P q.2 ∧ Reveals f g idx s(u, v) q.1 q.2} ⊆
      (⋃ c ∈ G, {x | P x ∧ g x = c}) ×ˢ (⋃ c ∈ F, {y | P y ∧ f y = c}) := by
    rintro ⟨x, y⟩ ⟨hPx, hPy, hrev⟩
    obtain ⟨hgG, hfF⟩ := hkey x y hrev
    exact ⟨Set.mem_biUnion hgG ⟨hPx, rfl⟩, Set.mem_biUnion hfF ⟨hPy, rfl⟩⟩
  refine le_trans (Set.encard_le_encard hsub) ?_
  rw [Set.encard_prod]
  have hX : (⋃ c ∈ G, {x | P x ∧ g x = c}).encard ≤ ((8 * K₁ : ℕ) : ℕ∞) := by
    refine le_trans (Finset.set_encard_biUnion_le G _) ?_
    refine le_trans (Finset.sum_le_sum (fun c _ => hg c)) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact_mod_cast Nat.mul_le_mul hGcard (le_refl K₁)
  have hY : (⋃ c ∈ F, {y | P y ∧ f y = c}).encard ≤ ((9 * K₁ : ℕ) : ℕ∞) := by
    refine le_trans (Finset.set_encard_biUnion_le F _) ?_
    refine le_trans (Finset.sum_le_sum (fun c _ => hf c)) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact_mod_cast Nat.mul_le_mul hFcard (le_refl K₁)
  calc (⋃ c ∈ G, {x | P x ∧ g x = c}).encard * (⋃ c ∈ F, {y | P y ∧ f y = c}).encard
      ≤ ((8 * K₁ : ℕ) : ℕ∞) * ((9 * K₁ : ℕ) : ℕ∞) := mul_le_mul' hX hY
    _ = ((72 * K₁ * K₁ : ℕ) : ℕ∞) := by push_cast; ring

/-! ## The local data of Steps 1 and 2, packaged

Everything the assembly consumes, at one scale `m` and one centre `z`. Each field
is supplied by a result already proved: `walk` by Proposition 5.14 for the choice
graph, `jump` by Lemma 5.16, `rep`/`idx` by `exists_indexed_rep` and the
pigeonhole of Step 2, and `hf`/`hg` by `exists_hash`. -/

/-- The output of Steps 1 and 2 at one scale and one centre, before assembly. -/
structure BlockData (Γ : Configuration (EuclideanSpace ℝ (Fin d))) (Δ R : ℝ)
    (a K₁ N₀ m : ℕ) (z : EuclideanSpace ℝ (Fin d)) where
  /-- The cone chosen in each block. -/
  W : ConeChoice d
  /-- The blocks in play. -/
  Blk : Set (Set (EuclideanSpace ℝ (Fin d)))
  /-- The blocks a point may jump into. -/
  Jmp : Set (Set (EuclideanSpace ℝ (Fin d)))
  jmp_sub : Jmp ⊆ Blk
  /-- The `a` indexed representatives of each block's majority set. -/
  rep : Set (EuclideanSpace ℝ (Fin d)) → ZMod a → EuclideanSpace ℝ (Fin d)
  rep_mem : ∀ B i, rep B i ∈ blockFibre Γ B (W B)
  rep_lat : ∀ B i, rep B i ∈ lattice d
  /-- The index, recoverable from the representative. -/
  idx : EuclideanSpace ℝ (Fin d) → ZMod a
  idx_rep : ∀ B ∈ Blk, ∀ i, idx (rep B i) = i
  /-- **Step 1.** Two blocks a point may jump into are joined in the choice graph
  by a walk of at most `N₀` edges through blocks in play. -/
  walk : ∀ B ∈ Jmp, ∀ B' ∈ Jmp, ∃ Wk : (choiceGraph Γ W).Walk B B',
    Wk.length ≤ N₀ ∧ ∀ C ∈ Wk.support, C ∈ Blk
  /-- **Lemma 5.16.** Every admissible point is joined in `G` to every point of
  some block it may jump into, by an edge at least `Δ^m` long. -/
  jump : ∀ x, AdmissiblePt Δ m z x → ∃ B ∈ Jmp,
    ∀ q ∈ B, (latticeGraph Γ).Adj x q ∧ Δ ^ m ≤ ‖q - x‖
  /-- Distinct blocks in play are at least `Δ^m` apart. -/
  sep : ∀ B ∈ Blk, ∀ B' ∈ Blk, B ≠ B' → ∀ p ∈ B, ∀ q ∈ B', Δ ^ m ≤ ‖p - q‖
  /-- Every point of every block in play lies in `B_{Δ^{m+1}R}(Δ^{m+1}z)`. -/
  near : ∀ B ∈ Blk, ∀ q ∈ B, ‖Δ ^ (m + 1) • z - q‖ < Δ ^ (m + 1) * R
  /-- The hash of `y`, which chooses the scheme's `i`. -/
  hf : EuclideanSpace ℝ (Fin d) → ZMod a
  /-- The hash of `x`, which chooses the scheme's `i + j`. -/
  hg : EuclideanSpace ℝ (Fin d) → ZMod a
  hf_bal : ∀ γ, {y | AdmissiblePt Δ m z y ∧ hf y = γ}.encard ≤ (K₁ : ℕ∞)
  hg_bal : ∀ γ, {x | AdmissiblePt Δ m z x ∧ hg x = γ}.encard ≤ (K₁ : ℕ∞)

/-! ## Step 2: the assembly

For an admissible pair, jump `x` into a block, run the alternating lift of a
block walk with `α = f y + g x` and `β = g x`, and jump out to `y`. -/

/-- **Steps 1 and 2 assembled.** The local data produces the `ScaleData` that
`pathProps_of_scaleData` consumes. -/
noncomputable def scaleData_of_blockData {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {Δ R : ℝ} {a K₁ N₀ m : ℕ} [NeZero a] {z : EuclideanSpace ℝ (Fin d)}
    (hΔ : 0 < Δ) (hR : 2 * Real.sqrt d < R) (D : BlockData Γ Δ R a K₁ N₀ m z) :
    ScaleData Γ Δ R (N₀ + 2) (72 * K₁ * K₁) m z := by
  classical
  have hΔm : (0:ℝ) < Δ ^ (m + 1) := pow_pos hΔ _
  -- an admissible point is itself well inside the ball
  have hnearpt : ∀ p : EuclideanSpace ℝ (Fin d), AdmissiblePt Δ m z p →
      ‖Δ ^ (m + 1) • z - p‖ < Δ ^ (m + 1) * R := by
    intro p hp
    rw [norm_sub_rev]
    calc ‖p - Δ ^ (m + 1) • z‖ ≤ 2 * Real.sqrt d * Δ ^ (m + 1) := hp.2
      _ < Δ ^ (m + 1) * R := by nlinarith
  have key : ∀ x y : EuclideanSpace ℝ (Fin d), Admissible Δ m z x y →
      ∃ w : (latticeGraph Γ).Walk x y, w.length ≤ N₀ + 2 ∧
        (∀ e ∈ w.edges, Δ ^ m ≤ edgeLen e) ∧
        (∀ e ∈ w.edges, ∀ u ∈ e, ‖Δ ^ (m + 1) • z - u‖ < Δ ^ (m + 1) * R) ∧
        (∀ e ∈ w.edges, Reveals D.hf D.hg D.idx e x y) := by
    intro x y hadm
    obtain ⟨Bx, hBxJ, hBx⟩ := D.jump x hadm.left
    obtain ⟨By, hByJ, hBy⟩ := D.jump y hadm.right
    have hBxB : Bx ∈ D.Blk := D.jmp_sub hBxJ
    have hByB : By ∈ D.Blk := D.jmp_sub hByJ
    obtain ⟨Wk, hWklen, hWksup⟩ := D.walk Bx hBxJ By hByJ
    obtain ⟨lift, hliftlen, hlifte⟩ :=
      exists_alternating_walk D.rep D.rep_mem D.rep_lat Wk (D.hf y + D.hg x) (D.hg x)
    have hax : (latticeGraph Γ).Adj x (D.rep Bx (D.hf y + D.hg x)) :=
      (hBx _ (D.rep_mem Bx _).1).1
    have hay : (latticeGraph Γ).Adj
        (D.rep By (if Even Wk.length then D.hf y + D.hg x else D.hg x)) y :=
      ((hBy _ (D.rep_mem By _).1).1).symm
    refine ⟨(SimpleGraph.Walk.cons hax lift).concat hay, ?_, ?_, ?_, ?_⟩
    · rw [SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_cons, hliftlen]
      omega
    all_goals
      intro e he
      rw [SimpleGraph.Walk.edges_concat, SimpleGraph.Walk.edges_cons,
        List.concat_eq_append, List.cons_append, List.mem_cons, List.mem_append,
        List.mem_singleton] at he
    · -- every edge is at least `Δ^m` long
      rcases he with rfl | he | rfl
      · rw [edgeLen_mk, norm_sub_rev]
        exact (hBx _ (D.rep_mem Bx _).1).2
      · obtain ⟨B₁, hB₁, B₂, hB₂, hne, rfl⟩ := hlifte e he
        rw [edgeLen_mk]
        exact D.sep B₁ (hWksup B₁ hB₁) B₂ (hWksup B₂ hB₂) hne _ (D.rep_mem B₁ _).1
          _ (D.rep_mem B₂ _).1
      · rw [edgeLen_mk]
        exact (hBy _ (D.rep_mem By _).1).2
    · -- every endpoint is near the centre
      rcases he with rfl | he | rfl
      · intro u hu
        rcases Sym2.mem_iff.mp hu with rfl | rfl
        · exact hnearpt u hadm.left
        · exact D.near Bx hBxB _ (D.rep_mem Bx _).1
      · obtain ⟨B₁, hB₁, B₂, hB₂, -, rfl⟩ := hlifte e he
        intro u hu
        rcases Sym2.mem_iff.mp hu with rfl | rfl
        · exact D.near B₁ (hWksup B₁ hB₁) _ (D.rep_mem B₁ _).1
        · exact D.near B₂ (hWksup B₂ hB₂) _ (D.rep_mem B₂ _).1
      · intro u hu
        rcases Sym2.mem_iff.mp hu with rfl | rfl
        · exact D.near By hByB _ (D.rep_mem By _).1
        · exact hnearpt u hadm.right
    · -- every edge reveals the hashes
      rcases he with rfl | he | rfl
      · exact Or.inl ⟨x, Sym2.mem_mk_left _ _, _, Sym2.mem_mk_right _ _, rfl,
          (D.idx_rep Bx hBxB _).symm⟩
      · obtain ⟨B₁, hB₁, B₂, hB₂, -, rfl⟩ := hlifte e he
        exact Or.inr (Or.inr ⟨_, Sym2.mem_mk_left _ _, _, Sym2.mem_mk_right _ _,
          (D.idx_rep B₂ (hWksup B₂ hB₂) _).symm,
          (D.idx_rep B₁ (hWksup B₁ hB₁) _).symm⟩)
      · refine Or.inr (Or.inl ⟨y, Sym2.mem_mk_right _ _, _, Sym2.mem_mk_left _ _, rfl, ?_⟩)
        rw [D.idx_rep By hByB]
        by_cases hev : Even Wk.length
        · exact Or.inr (by rw [if_pos hev])
        · exact Or.inl (by rw [if_neg hev])
  choose path hlen hlb hnear hrev using key
  refine ⟨path, hlen, hlb, hnear, fun e => ?_⟩
  refine le_trans (Set.encard_le_encard ?_)
    (encard_reveals_le D.hf D.hg D.idx (AdmissiblePt Δ m z) D.hf_bal D.hg_bal e)
  rintro ⟨x, y⟩ ⟨h, he⟩
  exact ⟨h.left, h.right, hrev x y h e he⟩

/-! ## Block separation

The `sep` field: the cubes of a town have side `ℓ` and centres `h` apart in the
maximum norm, so points of distinct blocks are at distance at least `h − ℓ`. With
`h = Δ^{m+1}` and `ℓ = Δ^m` and `Δ ≥ 2` that is at least `Δ^m`, which is Step 5's
lower bound on an interior edge. -/

/-- Distinct centres of the index lattice are `h` apart in the maximum norm. -/
theorem infNorm_smul_sub_lattice {h : ℝ} (hh : 0 < h)
    {w₁ w₂ : EuclideanSpace ℝ (Fin d)} (h₁ : w₁ ∈ lattice d) (h₂ : w₂ ∈ lattice d)
    (hne : w₁ ≠ w₂) : h ≤ infNorm (h • w₁ - h • w₂) := by
  obtain ⟨i, hi⟩ : ∃ i, w₁ i ≠ w₂ i := by
    by_contra hc
    exact hne (euclidean_ext (fun i => not_not.mp (fun hi => hc ⟨i, hi⟩)))
  obtain ⟨n, hn⟩ := (mem_lattice_iff.mp h₁) i
  obtain ⟨k, hk⟩ := (mem_lattice_iff.mp h₂) i
  have hnk : n ≠ k := by
    intro hcon
    exact hi (by rw [hn, hk, hcon])
  have hone : (1:ℝ) ≤ |(n : ℝ) - (k : ℝ)| := by
    have : (1:ℤ) ≤ |n - k| := Int.one_le_abs (sub_ne_zero.mpr hnk)
    calc (1:ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|n - k| : ℤ) : ℝ) := by exact_mod_cast this
      _ = |(n : ℝ) - (k : ℝ)| := by push_cast [Int.cast_abs]; ring_nf
  have hcoord : (h • w₁ - h • w₂) i = h * ((n : ℝ) - (k : ℝ)) := by
    have e1 : (h • w₁ - h • w₂) i = h * w₁ i - h * w₂ i := by simp
    rw [e1, hn, hk]; ring
  refine le_trans ?_ (le_infNorm (h • w₁ - h • w₂) i)
  rw [hcoord, abs_mul, abs_of_pos hh]
  nlinarith

/-- **Block separation.** Points of blocks at distinct centres are at least
`h − ℓ` apart. -/
theorem block_sep {h ℓ : ℝ} {c₁ c₂ : EuclideanSpace ℝ (Fin d)}
    (hc : h ≤ infNorm (c₁ - c₂)) {p q : EuclideanSpace ℝ (Fin d)}
    (hp : p ∈ block ℓ c₁) (hq : q ∈ block ℓ c₂) : h - ℓ ≤ ‖p - q‖ := by
  have h1 : infNorm (p - c₁) ≤ ℓ / 2 := hp.2
  have h2 : infNorm (q - c₂) ≤ ℓ / 2 := hq.2
  have hdec : c₁ - c₂ = (c₁ - p) + ((p - q) + (q - c₂)) := by abel
  have hb1 : infNorm (c₁ - c₂) ≤ infNorm (c₁ - p) + infNorm ((p - q) + (q - c₂)) := by
    rw [hdec]; exact infNorm_add_le _ _
  have hb2 : infNorm ((p - q) + (q - c₂)) ≤ infNorm (p - q) + infNorm (q - c₂) :=
    infNorm_add_le _ _
  have hcp : infNorm (c₁ - p) = infNorm (p - c₁) := infNorm_sub_comm _ _
  have hle : infNorm (p - q) ≤ ‖p - q‖ := infNorm_le_norm _
  linarith

end QFS
