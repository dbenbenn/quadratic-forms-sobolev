/-
Turning the reachability relations of Sections 4 and 5 into honest walks, with
length bounds, and concatenating them.

`Relation.ReflTransGen` records that a path exists, not which one, so it carries
no length. But a walk confined to a *finite* vertex set can be shortened to a
path, whose length is bounded by the size of that set — which is where all the
length bounds of Theorem 5.15 come from.
-/
import QuadraticFormsSobolev.Counting
import QuadraticFormsSobolev.FirstJump

open Real Set Metric

namespace QFS

variable {V : Type*} {G : SimpleGraph V}

/-- A reachability chain confined to `S` gives a walk whose support lies in `S`. -/
theorem exists_walk_of_reflTransGen {r : V → V → Prop} {S : Set V}
    (hadj : ∀ a b, r a b → a = b ∨ G.Adj a b)
    (hmem : ∀ a b, r a b → a ∈ S ∧ b ∈ S)
    {a b : V} (ha : a ∈ S) (h : Relation.ReflTransGen r a b) :
    ∃ w : G.Walk a b, ∀ v ∈ w.support, v ∈ S := by
  induction h with
  | refl => exact ⟨SimpleGraph.Walk.nil, by simpa using ha⟩
  | @tail p c hpre hstep ih =>
      obtain ⟨w, hw⟩ := ih
      rcases hadj p c hstep with heq | hAdj
      · rw [← heq]
        exact ⟨w, hw⟩
      · refine ⟨w.append (SimpleGraph.Walk.cons hAdj SimpleGraph.Walk.nil), fun v hv => ?_⟩
        rw [SimpleGraph.Walk.mem_support_append_iff] at hv
        rcases hv with hv | hv
        · exact hw v hv
        · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
            List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with h1 | h1
          · rw [h1]; exact (hmem _ _ hstep).1
          · rw [h1]; exact (hmem _ _ hstep).2

/-- A walk confined to a finite set can be replaced by one of length less than the
size of that set: delete the cycles. -/
theorem exists_walk_length_lt {S : Set V} (hSfin : S.Finite)
    {a b : V} {w : G.Walk a b} (hw : ∀ v ∈ w.support, v ∈ S) :
    ∃ w' : G.Walk a b, (∀ v ∈ w'.support, v ∈ S) ∧ w'.length < S.ncard := by
  classical
  refine ⟨w.bypass, fun v hv => hw v (SimpleGraph.Walk.support_bypass_subset_support w hv), ?_⟩
  have hnodup : w.bypass.support.Nodup := (SimpleGraph.Walk.bypass_isPath w).support_nodup
  have hsub : w.bypass.support.toFinset ⊆ hSfin.toFinset := by
    intro v hv
    rw [List.mem_toFinset] at hv
    rw [Set.Finite.mem_toFinset]
    exact hw v (SimpleGraph.Walk.support_bypass_subset_support w hv)
  have hcard : w.bypass.support.length ≤ hSfin.toFinset.card := by
    rw [← List.toFinset_card_of_nodup hnodup]
    exact Finset.card_le_card hsub
  have hlen : w.bypass.support.length = w.bypass.length + 1 :=
    SimpleGraph.Walk.length_support w.bypass
  have hSn : hSfin.toFinset.card = S.ncard := by
    rw [← Set.ncard_coe_finset, hSfin.coe_toFinset]
  omega

/-- **The bridge**: a reachability chain confined to a finite set `S` yields a walk
inside `S` of length less than `#S`. -/
theorem exists_walk_of_reflTransGen_lt {r : V → V → Prop} {S : Set V}
    (hSfin : S.Finite) (hadj : ∀ a b, r a b → a = b ∨ G.Adj a b)
    (hmem : ∀ a b, r a b → a ∈ S ∧ b ∈ S)
    {a b : V} (ha : a ∈ S) (h : Relation.ReflTransGen r a b) :
    ∃ w : G.Walk a b, (∀ v ∈ w.support, v ∈ S) ∧ w.length < S.ncard := by
  classical
  obtain ⟨w, hw⟩ := exists_walk_of_reflTransGen hadj hmem ha h
  exact exists_walk_length_lt hSfin hw

/-! ## Concatenation along way-points -/

/-- Concatenating walks through a list of way-points. -/
theorem exists_walk_through_list {S T : Set V} {N : ℕ}
    (hconn : ∀ a ∈ T, ∀ b ∈ T, ∃ w : G.Walk a b, (∀ v ∈ w.support, v ∈ S) ∧ w.length ≤ N) :
    ∀ (l : List V), (∀ v ∈ l, v ∈ T) → ∀ a ∈ T,
      ∃ (b : V) (w : G.Walk a b), b ∈ T ∧ (∀ v ∈ w.support, v ∈ S) ∧
        w.length ≤ l.length * N ∧ ∀ v ∈ l, v ∈ w.support := by
  intro l
  induction l with
  | nil =>
      intro _ a ha
      obtain ⟨w, hw, -⟩ := hconn a ha a ha
      exact ⟨a, SimpleGraph.Walk.nil, ha, by simpa using hw a w.start_mem_support,
        by simp, by simp⟩
  | cons v l ih =>
      intro hl a ha
      have hvT : v ∈ T := hl v (by simp)
      obtain ⟨w₁, hw₁, hlen₁⟩ := hconn a ha v hvT
      obtain ⟨b, w₂, hbT, hw₂, hlen₂, hcov₂⟩ := ih (fun u hu => hl u (by simp [hu])) v hvT
      refine ⟨b, w₁.append w₂, hbT, fun u hu => ?_, ?_, fun u hu => ?_⟩
      · rw [SimpleGraph.Walk.mem_support_append_iff] at hu
        rcases hu with hu | hu
        · exact hw₁ u hu
        · exact hw₂ u hu
      · rw [SimpleGraph.Walk.length_append]
        simp only [List.length_cons]
        nlinarith [hlen₁, hlen₂]
      · rw [SimpleGraph.Walk.mem_support_append_iff]
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact Or.inl w₁.end_mem_support
        · exact Or.inr (hcov₂ u hu')

/-- **Step 1 of Theorem 5.15, abstractly.** If every two way-points of a finite
nonempty set `T` are joined by a walk inside `S` of length at most `N`, then a
single walk inside `S` of length at most `#T · N` passes through all of `T`. -/
theorem exists_walk_covering {S T : Set V} (hTfin : T.Finite) (hTne : T.Nonempty) {N : ℕ}
    (hconn : ∀ a ∈ T, ∀ b ∈ T, ∃ w : G.Walk a b, (∀ v ∈ w.support, v ∈ S) ∧ w.length ≤ N) :
    ∃ (a b : V) (w : G.Walk a b), a ∈ T ∧ b ∈ T ∧ (∀ v ∈ w.support, v ∈ S) ∧
      w.length ≤ T.ncard * N ∧ ∀ v ∈ T, v ∈ w.support := by
  classical
  obtain ⟨a, ha⟩ := hTne
  set l : List V := hTfin.toFinset.toList with hl
  have hlT : ∀ v ∈ l, v ∈ T := by
    intro v hv
    rw [hl, Finset.mem_toList, Set.Finite.mem_toFinset] at hv
    exact hv
  have hllen : l.length = T.ncard := by
    rw [hl, Finset.length_toList, ← Set.ncard_coe_finset, hTfin.coe_toFinset]
  obtain ⟨b, w, hbT, hwS, hwlen, hwcov⟩ := exists_walk_through_list hconn l hlT a ha
  refine ⟨a, b, w, ha, hbT, hwS, by rw [← hllen]; exact hwlen, fun v hv => ?_⟩
  refine hwcov v ?_
  rw [hl, Finset.mem_toList, Set.Finite.mem_toFinset]
  exact hv


/-! ## Instantiation for the graph `G` -/

section Lattice

variable {d : ℕ}

/-- The lattice-point count, for open balls and in `ncard` form. -/
lemma ncard_lattice_inter_ball_le (a : EuclideanSpace ℝ (Fin d)) (R : ℝ) :
    (ball a R ∩ lattice d).ncard ≤ (2 * ⌈R⌉₊ + 1) ^ d := by
  have hfin : (ball a R ∩ lattice d).Finite :=
    (lattice_inter_closedBall_finite a R).subset
      (fun x hx => ⟨hx.2, ball_subset_closedBall hx.1⟩)
  have hsub : ball a R ∩ lattice d ⊆ lattice d ∩ closedBall a R :=
    fun x hx => ⟨hx.2, ball_subset_closedBall hx.1⟩
  have hle : (ball a R ∩ lattice d).encard ≤ (((2 * ⌈R⌉₊ + 1) ^ d : ℕ) : ℕ∞) :=
    le_trans (Set.encard_mono hsub) (encard_lattice_inter_closedBall_le a R)
  rw [← hfin.cast_ncard_eq] at hle
  exact_mod_cast hle

/-- **The bridge for `G`**: a `ConnWithin` chain confined to a finite set of
lattice points becomes a walk of length less than the size of that set. -/
theorem exists_walk_of_connWithin {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {S : Set (EuclideanSpace ℝ (Fin d))} (hSfin : S.Finite) (hSlat : S ⊆ lattice d)
    {a b : EuclideanSpace ℝ (Fin d)} (ha : a ∈ S) (h : ConnWithin Γ S a b) :
    ∃ w : (latticeGraph Γ).Walk a b, (∀ v ∈ w.support, v ∈ S) ∧ w.length < S.ncard := by
  classical
  refine exists_walk_of_reflTransGen_lt hSfin (fun p q hpq => ?_) (fun p q hpq => ?_) ha h
  · exact Or.inr ⟨hSlat hpq.1, hSlat hpq.2.1, hpq.2.2⟩
  · exact ⟨hpq.1, hpq.2.1⟩

/-- An `r`-`R`-connected lattice point is joined to every lattice point of its
`r`-ball by a walk of length less than `(2⌈R⌉+1)^d`, staying inside the `R`-ball.
This is the length bound Step 1 of Theorem 5.15 attaches to Corollary 5.8. -/
theorem exists_walk_of_rrConnected {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {r R : ℝ} (hR : 0 < R) {x : EuclideanSpace ℝ (Fin d)} (hxlat : x ∈ lattice d)
    (hx : RRConnected Γ r R x) {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ ball x r)
    (hylat : y ∈ lattice d) :
    ∃ w : (latticeGraph Γ).Walk x y,
      (∀ v ∈ w.support, v ∈ ball x R ∩ lattice d) ∧ w.length < (2 * ⌈R⌉₊ + 1) ^ d := by
  have hSfin : (ball x R ∩ lattice d).Finite :=
    (lattice_inter_closedBall_finite x R).subset
      (fun z hz => ⟨hz.2, ball_subset_closedBall hz.1⟩)
  obtain ⟨w, hwS, hwlen⟩ :=
    exists_walk_of_connWithin hSfin (fun z hz => hz.2)
      ⟨mem_ball_self hR, hxlat⟩ (hx y hy hylat)
  exact ⟨w, hwS, lt_of_lt_of_le hwlen (ncard_lattice_inter_ball_le x R)⟩

end Lattice

end QFS
