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

end QFS
