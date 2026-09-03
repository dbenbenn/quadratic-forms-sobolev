/-
Step 2 of the proof of Theorem 5.15: the cyclic scheme.

Three ingredients. A favored edge makes every point of the *majority set* of one
block adjacent, in `G`, to every point of the next — which is what turns the
block walk of Step 1 into walks in `G`. The indices of the scheme are read
cyclically, and a pair of consecutive indices determines the scheme's parameters,
which is what keeps the `a²` walks from sharing edges. And the assignment `φ_z`
of pairs to walks exists with bounded fibres by a balanced-partition argument.
-/
import QuadraticFormsSobolev.Paths

open Real Set Metric

namespace QFS

/-! ## Lifting a favored edge to `G` -/

variable {d : ℕ}

/-- **The lift.** If `Q` and `P` are joined by a favored edge, then every point of
the majority set of `Q` for the witnessing cone is adjacent in `G` to every point
of `P`. -/
theorem majority_adj_of_favoredEdge {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {Q P : Set (EuclideanSpace ℝ (Fin d))} (hQlat : Q ⊆ lattice d) (hPlat : P ⊆ lattice d)
    (h : FavoredEdge Γ Q P) :
    ∃ V : DCone (EuclideanSpace ℝ (Fin d)), FavoredIn Γ Q V ∧
      ∀ q ∈ blockFibre Γ Q V, ∀ p ∈ P, (latticeGraph Γ).Adj q p := by
  obtain ⟨V, hVfav, hcont⟩ := h
  refine ⟨V, hVfav, fun q hq p hp => ?_⟩
  refine ⟨hQlat hq.1, hPlat hp, Or.inl ?_⟩
  rw [mem_coneAt, hq.2]
  exact hcont q hq.1 p hp

/-- The majority set is large: at least `#Q / L` points of `Q` are each adjacent
in `G` to every point of `P`. -/
theorem exists_large_adj_of_favoredEdge {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {Q P : Set (EuclideanSpace ℝ (Fin d))} (hQlat : Q ⊆ lattice d) (hPlat : P ⊆ lattice d)
    (hQfin : Q.Finite) {L : ℕ} (hL : (Γ '' Q).ncard ≤ L) (h : FavoredEdge Γ Q P) :
    ∃ S ⊆ Q, Q.ncard ≤ L * S.ncard ∧
      ∀ q ∈ S, ∀ p ∈ P, (latticeGraph Γ).Adj q p := by
  obtain ⟨V, hVfav, hadj⟩ := majority_adj_of_favoredEdge hQlat hPlat h
  exact ⟨blockFibre Γ Q V, fun _ hx => hx.1,
    ncard_le_mul_ncard_blockFibre hQfin hVfav hL, hadj⟩

/-! ## The cyclic indexing

The scheme's `k`-th vertex is `q^k_i` for odd `k` and `q^k_{i+j}` for even `k`,
the indices read in `ZMod a`. A consecutive pair of indices is `(i, i+j)`, which
determines `(i, j)`: that is why the `a²` walks do not share an edge at any given
position, and it is what Step 6's multiplicity count rests on. -/

/-- A consecutive pair of indices of the cyclic scheme determines its
parameters. -/
theorem cyclic_pair_injective (a : ℕ) :
    Function.Injective (fun p : ZMod a × ZMod a => (p.1, p.1 + p.2)) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  subst h1
  simp only [Prod.mk.injEq, true_and]
  exact add_left_cancel h2

/-! ## The assignment `φ_z` -/

/-- **A balanced assignment.** If `#A ≤ K · #M` and `M` is nonempty, the elements
of `A` can be assigned to `M` so that no element of `M` receives more than `K` of
them. This is the paper's `φ_z : A → M` with `#φ_z⁻¹(p) ≤ K`. -/
theorem exists_fun_fiber_le {α β : Type*} [DecidableEq β] {K : ℕ} :
    ∀ (n : ℕ) (M : Finset β), M.card = n → M.Nonempty →
      ∀ A : Finset α, A.card ≤ K * n →
        ∃ f : α → β, (∀ x ∈ A, f x ∈ M) ∧
          ∀ m : β, (A.filter fun x => f x = m).card ≤ K := by
  classical
  intro n
  induction n with
  | zero =>
      intro M hM hMne _ _
      rw [Finset.card_eq_zero] at hM
      exact absurd hM (Finset.nonempty_iff_ne_empty.mp hMne)
  | succ n ih =>
      intro M hM hMne A hA
      obtain ⟨m, hm⟩ := hMne
      by_cases hAK : A.card ≤ K
      · refine ⟨fun _ => m, fun x _ => hm, fun m' => ?_⟩
        by_cases hmm : m = m'
        · subst hmm
          simpa using hAK
        · have hemp : (A.filter fun _ => m = m') = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            exact fun _ _ => hmm
          rw [hemp]
          simp
      · rw [not_le] at hAK
        obtain ⟨A₀, hA₀sub, hA₀card⟩ := Finset.exists_subset_card_eq (le_of_lt hAK)
        have hn : 0 < n := by
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · exfalso
            have hAK1 : A.card ≤ K := by simpa using hA
            omega
          · exact hn
        have hM'card : (M.erase m).card = n := by
          rw [Finset.card_erase_of_mem hm, hM]
          omega
        have hM'ne : (M.erase m).Nonempty := by
          rw [← Finset.card_pos, hM'card]
          exact hn
        have hA' : (A \ A₀).card ≤ K * n := by
          have hcs : (A \ A₀).card = A.card - A₀.card := by
            rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hA₀sub]
          rw [hcs, hA₀card]
          have hexp : K * (n + 1) = K * n + K := by ring
          omega
        obtain ⟨g, hgM, hgfib⟩ := ih (M.erase m) hM'card hM'ne (A \ A₀) hA'
        refine ⟨fun x => if x ∈ A₀ then m else g x, fun x hx => ?_, fun m' => ?_⟩
        · dsimp only
          by_cases hx0 : x ∈ A₀
          · rw [if_pos hx0]; exact hm
          · rw [if_neg hx0]
            exact Finset.mem_of_mem_erase (hgM x (Finset.mem_sdiff.mpr ⟨hx, hx0⟩))
        · dsimp only
          by_cases hmm : m' = m
          · have hfe : (A.filter fun x => (if x ∈ A₀ then m else g x) = m') = A₀ := by
              ext x
              simp only [Finset.mem_filter]
              constructor
              · rintro ⟨hx, hfx⟩
                by_contra hx0
                rw [if_neg hx0, hmm] at hfx
                exact (Finset.mem_erase.mp (hgM x (Finset.mem_sdiff.mpr ⟨hx, hx0⟩))).1 hfx
              · intro hx0
                exact ⟨hA₀sub hx0, by rw [if_pos hx0, hmm]⟩
            rw [hfe, hA₀card]
          · have hfe : (A.filter fun x => (if x ∈ A₀ then m else g x) = m')
                = (A \ A₀).filter fun x => g x = m' := by
              ext x
              simp only [Finset.mem_filter, Finset.mem_sdiff]
              constructor
              · rintro ⟨hx, hfx⟩
                by_cases hx0 : x ∈ A₀
                · rw [if_pos hx0] at hfx
                  exact absurd hfx.symm hmm
                · rw [if_neg hx0] at hfx
                  exact ⟨⟨hx, hx0⟩, hfx⟩
              · rintro ⟨⟨hx, hx0⟩, hgx⟩
                exact ⟨hx, by rw [if_neg hx0]; exact hgx⟩
            rw [hfe]
            exact hgfib m'

/-- **The assignment `φ_z` of the cyclic scheme.** The scheme offers `a²` walks,
indexed by a pair in `ZMod a`; if the set `A` of pairs to be connected has at most
`K a²` elements, each pair can be assigned a walk so that no walk serves more than
`K` of them. -/
theorem exists_scheme_assignment {α : Type*} {a K : ℕ} [NeZero a]
    (A : Finset α) (hA : A.card ≤ K * (a * a)) :
    ∃ f : α → ZMod a × ZMod a,
      ∀ p : ZMod a × ZMod a, (A.filter fun x => f x = p).card ≤ K := by
  classical
  have hcard : (Finset.univ : Finset (ZMod a × ZMod a)).card = a * a := by
    simp [ZMod.card]
  obtain ⟨f, -, hfib⟩ :=
    exists_fun_fiber_le (K := K) (a * a) (Finset.univ : Finset (ZMod a × ZMod a)) hcard
      ⟨(0, 0), Finset.mem_univ _⟩ A hA
  exact ⟨f, hfib⟩

end QFS
