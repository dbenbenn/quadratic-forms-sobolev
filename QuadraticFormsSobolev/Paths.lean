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


/-! ## Step 1 of Theorem 5.15: one walk through all the blocks of a ball -/

section Step1

variable {d : ℕ}

lemma ncard_lattice_inter_closedBall_le' (a : EuclideanSpace ℝ (Fin d)) (M : ℝ) :
    (lattice d ∩ closedBall a M).ncard ≤ (2 * ⌈M⌉₊ + 1) ^ d := by
  have hfin := lattice_inter_closedBall_finite a M
  have hle := encard_lattice_inter_closedBall_le a M
  rw [← hfin.cast_ncard_eq] at hle
  exact_mod_cast hle

lemma townBall_eq_image (h ℓ : ℝ) (z : EuclideanSpace ℝ (Fin d)) (R : ℝ) :
    townBall h ℓ z R = (fun p => townIndex h ℓ p) '' (lattice d ∩ ball z R) := by
  have hset : {p : EuclideanSpace ℝ (Fin d) | p ∈ lattice d ∧ ‖p - z‖ < R}
      = lattice d ∩ ball z R := by
    ext p
    rw [Set.mem_ofPred_eq, Set.mem_inter_iff, mem_ball, dist_eq_norm]
  rw [townBall, hset]

lemma townBall_finite (h ℓ : ℝ) (z : EuclideanSpace ℝ (Fin d)) (R : ℝ) :
    (townBall h ℓ z R).Finite := by
  rw [townBall_eq_image]
  exact Set.Finite.image _ ((lattice_inter_closedBall_finite z R).subset
    (fun p hp => ⟨hp.1, ball_subset_closedBall hp.2⟩))

lemma ncard_townBall_le (h ℓ : ℝ) (z : EuclideanSpace ℝ (Fin d)) (R : ℝ) :
    (townBall h ℓ z R).ncard ≤ (2 * ⌈R⌉₊ + 1) ^ d := by
  have hfin : (lattice d ∩ ball z R).Finite :=
    (lattice_inter_closedBall_finite z R).subset
      (fun p hp => ⟨hp.1, ball_subset_closedBall hp.2⟩)
  rw [townBall_eq_image]
  refine le_trans (Set.ncard_image_le hfin) (le_trans (Set.ncard_le_ncard ?_
    (lattice_inter_closedBall_finite z R)) (ncard_lattice_inter_closedBall_le' z R))
  exact fun p hp => ⟨hp.1, ball_subset_closedBall hp.2⟩

lemma townBall_mono (h ℓ : ℝ) (z : EuclideanSpace ℝ (Fin d)) {R R' : ℝ} (hRR : R ≤ R') :
    townBall h ℓ z R ⊆ townBall h ℓ z R' := by
  rintro _ ⟨p, ⟨hplat, hpR⟩, rfl⟩
  exact ⟨p, ⟨hplat, lt_of_lt_of_le hpR hRR⟩, rfl⟩

lemma FavoredConn.mono {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {T T' : Set (Set (EuclideanSpace ℝ (Fin d)))} (hTT : T ⊆ T')
    {Q P : Set (EuclideanSpace ℝ (Fin d))} (h : FavoredConn Γ T Q P) :
    FavoredConn Γ T' Q P := by
  induction h with
  | refl => exact FavoredConn.refl _ _ _
  | tail _ hstep ih =>
      exact FavoredConn.trans ih
        (Relation.ReflTransGen.single ⟨hTT hstep.1, hTT hstep.2.1, hstep.2.2⟩)

/-- **The bridge for the favored graph.** -/
theorem exists_favoredWalk_of_favoredConn {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {T : Set (Set (EuclideanSpace ℝ (Fin d)))} (hTfin : T.Finite)
    {Q P : Set (EuclideanSpace ℝ (Fin d))} (hQ : Q ∈ T) (h : FavoredConn Γ T Q P) :
    ∃ w : (favoredGraph Γ).Walk Q P, (∀ B ∈ w.support, B ∈ T) ∧ w.length < T.ncard := by
  classical
  refine exists_walk_of_reflTransGen_lt hTfin (fun A B hAB => ?_)
    (fun A B hAB => ⟨hAB.1, hAB.2.1⟩) hQ h
  by_cases hEq : A = B
  · exact Or.inl hEq
  · exact Or.inr ⟨hEq, hAB.2.2⟩

/-- **Step 1 of the proof of Theorem 5.15.** In a `ϑ`-sparsely populated town,
for every centre `z` of the index lattice there is a single walk in the favored
graph which visits every block whose index lies within `r` of `z`, never leaves
the blocks whose index lies within `R`, and has length at most
`(2⌈r⌉+1)^d · (2⌈R⌉+1)^d` — the paper's `t ≤ #(B_r∩ℤ^d) · #(B_R∩ℤ^d)`. -/
theorem exists_favoredWalk_covering {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    {r : ℝ} (hr : 0 < r) :
    ∃ R : ℝ, r < R ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ →
      ∀ h ℓ : ℝ, 0 < h → 0 < ℓ → SparselyPopulated d ϑ h ℓ →
      ∀ z ∈ lattice d,
        ∃ (Q P : Set (EuclideanSpace ℝ (Fin d))) (w : (favoredGraph Γ).Walk Q P),
          (∀ B ∈ w.support, B ∈ townBall h ℓ z R) ∧
          w.length ≤ (2 * ⌈r⌉₊ + 1) ^ d * (2 * ⌈R⌉₊ + 1) ^ d ∧
          (∀ x ∈ lattice d, ‖x - z‖ ≤ r → townIndex h ℓ x ∈ w.support) := by
  classical
  obtain ⟨R₀, hR₀r, hprop⟩ := renormalization (d := d) hϑ hϑ' hr
  refine ⟨R₀ + 1, by linarith, ?_⟩
  intro Γ hΓ h ℓ hh hℓ hsp z hz
  set R : ℝ := R₀ + 1 with hRdef
  have hrR : r < R := by rw [hRdef]; linarith
  -- the way-points: blocks indexed within `r` of `z`
  obtain ⟨T, hTdef⟩ : ∃ T : Set (Set (EuclideanSpace ℝ (Fin d))),
      T = (fun p => townIndex h ℓ p) '' {p | p ∈ lattice d ∧ ‖p - z‖ ≤ r} := ⟨_, rfl⟩
  have hsrcfin : {p : EuclideanSpace ℝ (Fin d) | p ∈ lattice d ∧ ‖p - z‖ ≤ r}.Finite :=
    (lattice_inter_closedBall_finite z r).subset (fun p hp =>
      ⟨hp.1, by rw [Metric.mem_closedBall, dist_eq_norm]; exact hp.2⟩)
  have hTfin : T.Finite := by rw [hTdef]; exact hsrcfin.image _
  have hTne : T.Nonempty := by
    refine ⟨townIndex h ℓ z, ?_⟩
    rw [hTdef]
    exact ⟨z, ⟨hz, by rw [sub_self, norm_zero]; exact hr.le⟩, rfl⟩
  have hTcard : T.ncard ≤ (2 * ⌈r⌉₊ + 1) ^ d := by
    have h1 : T.ncard
        ≤ {p : EuclideanSpace ℝ (Fin d) | p ∈ lattice d ∧ ‖p - z‖ ≤ r}.ncard := by
      rw [hTdef]
      exact Set.ncard_image_le hsrcfin
    have h2 : {p : EuclideanSpace ℝ (Fin d) | p ∈ lattice d ∧ ‖p - z‖ ≤ r}
        ⊆ lattice d ∩ closedBall z r :=
      fun p hp => ⟨hp.1, by rw [Metric.mem_closedBall, dist_eq_norm]; exact hp.2⟩
    have h3 := Set.ncard_le_ncard h2 (lattice_inter_closedBall_finite z r)
    exact le_trans h1 (le_trans h3 (ncard_lattice_inter_closedBall_le' z r))
  have hTsub : T ⊆ townBall h ℓ z R := by
    rw [hTdef]
    rintro _ ⟨p, ⟨hplat, hpr⟩, rfl⟩
    exact ⟨p, ⟨hplat, by linarith⟩, rfl⟩
  -- any two way-points are joined inside the big ball, with a length bound
  have hconn : ∀ A ∈ T, ∀ B ∈ T, ∃ w : (favoredGraph Γ).Walk A B,
      (∀ C ∈ w.support, C ∈ townBall h ℓ z R) ∧
        w.length ≤ (2 * ⌈R⌉₊ + 1) ^ d := by
    intro A hA B hB
    rw [hTdef] at hA hB
    obtain ⟨x, ⟨hxlat, hxr⟩, rfl⟩ := hA
    obtain ⟨y, ⟨hylat, hyr⟩, rfl⟩ := hB
    have hconn0 := hprop Γ hΓ h ℓ hh hℓ hsp z hz x hxlat y hylat hxr hyr
    have hconn1 : FavoredConn Γ (townBall h ℓ z R) (townIndex h ℓ x) (townIndex h ℓ y) :=
      FavoredConn.mono (townBall_mono h ℓ z (by rw [hRdef]; linarith)) hconn0
    obtain ⟨w, hwS, hwlen⟩ :=
      exists_favoredWalk_of_favoredConn (townBall_finite h ℓ z R)
        (hTsub (by rw [hTdef]; exact ⟨x, ⟨hxlat, hxr⟩, rfl⟩)) hconn1
    exact ⟨w, hwS, le_of_lt (lt_of_lt_of_le hwlen (ncard_townBall_le h ℓ z R))⟩
  obtain ⟨Q, P, w, hQT, hPT, hwS, hwlen, hwcov⟩ :=
    exists_walk_covering (G := favoredGraph Γ) hTfin hTne hconn
  refine ⟨Q, P, w, hwS, le_trans hwlen (Nat.mul_le_mul hTcard (le_refl ((2 * ⌈R⌉₊ + 1) ^ d))), ?_⟩
  intro x hxlat hxr
  exact hwcov _ (by rw [hTdef]; exact ⟨x, ⟨hxlat, hxr⟩, rfl⟩)

end Step1

end QFS
