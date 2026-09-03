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

end QFS
