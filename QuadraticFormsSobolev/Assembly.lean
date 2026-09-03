/-
Assembling Step 2 of Theorem 5.15: the walks of the cyclic scheme.

Definition 5.13 declares an edge between blocks `Q` and `P` when *some* cone
favored in `Q` contains `P` based at `Q`. That is too weak for Step 2, which
picks one representative per block and runs it along the whole block walk: a
block sitting between two edges would have to be a majority point for both
witnessing cones at once, and different edges may be witnessed by different
favored cones.

The paper's own phrasing repairs this — "choose for every block a favored cone" —
so we work with the graph relative to such a choice. Proposition 5.14 produces
exactly this, since its proof fixes a favored cone per block before doing
anything else.
-/
import QuadraticFormsSobolev.Multiplicity

open Real Set Metric

namespace QFS

variable {d : ℕ}

/-! ## The favored graph relative to a choice of cones -/

/-- A choice of a cone for every block. -/
abbrev ConeChoice (d : ℕ) :=
  Set (EuclideanSpace ℝ (Fin d)) → DCone (EuclideanSpace ℝ (Fin d))

/-- Adjacency relative to a choice of favored cones: the edge must be witnessed by
the *chosen* cone of one of its endpoints. -/
def choiceAdj (_Γ : Configuration (EuclideanSpace ℝ (Fin d))) (W : ConeChoice d)
    (Q P : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  Q ≠ P ∧ ((∀ x ∈ Q, ∀ y ∈ P, y ∈ shift (W Q).carrier x) ∨
    (∀ x ∈ P, ∀ y ∈ Q, y ∈ shift (W P).carrier x))

instance choiceAdj_symm (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (W : ConeChoice d) :
    Std.Symm (choiceAdj Γ W) := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩

instance choiceAdj_irrefl (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (W : ConeChoice d) :
    Std.Irrefl (choiceAdj Γ W) := ⟨fun _ h => h.1 rfl⟩

/-- The favored graph relative to a choice of cones. -/
def choiceGraph (Γ : Configuration (EuclideanSpace ℝ (Fin d))) (W : ConeChoice d) :
    SimpleGraph (Set (EuclideanSpace ℝ (Fin d))) :=
  ⟨choiceAdj Γ W, choiceAdj_symm Γ W, choiceAdj_irrefl Γ W⟩

/-- The choice graph is a subgraph of the favored graph of Definition 5.13. -/
theorem favoredAdj_of_choiceAdj {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {W : ConeChoice d}
    {Q P : Set (EuclideanSpace ℝ (Fin d))} (hQ : FavoredIn Γ Q (W Q))
    (hP : FavoredIn Γ P (W P)) (h : choiceAdj Γ W Q P) : favoredAdj Γ Q P :=
  ⟨h.1, h.2.imp (fun hc => ⟨W Q, hQ, hc⟩) (fun hc => ⟨W P, hP, hc⟩)⟩

/-! ## The lift, on both sides at once -/

/-- **The both-majority lift.** If `Q` and `P` are adjacent in the choice graph,
then a majority point of `Q` and a majority point of `P` are adjacent in `G`,
whichever way the favored edge points. This is what lets one representative per
block serve both of its incident edges. -/
theorem latticeAdj_of_choiceAdj {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {W : ConeChoice d} {Q P : Set (EuclideanSpace ℝ (Fin d))} (hadj : choiceAdj Γ W Q P)
    {q : EuclideanSpace ℝ (Fin d)} (hqlat : q ∈ lattice d)
    (hq : q ∈ blockFibre Γ Q (W Q))
    {p : EuclideanSpace ℝ (Fin d)} (hplat : p ∈ lattice d)
    (hp : p ∈ blockFibre Γ P (W P)) :
    (latticeGraph Γ).Adj q p := by
  rcases hadj.2 with hc | hc
  · exact ⟨hqlat, hplat, Or.inl (by rw [mem_coneAt, hq.2]; exact hc q hq.1 p hp.1)⟩
  · exact ⟨hqlat, hplat, Or.inr (by rw [mem_coneAt, hp.2]; exact hc p hp.1 q hq.1)⟩

/-! ## The alternating walk

The scheme's walk visits `ρ B α` and `ρ B β` alternately along the block walk;
recursively, one steps to the next block and swaps the two indices, which
produces exactly the paper's `q^k_i` at odd `k` and `q^k_{i+j}` at even `k`. -/

/-- **The lift of a block walk to `G`.** Given a representative `ρ B i` in the
majority set of each block, a walk in the choice graph lifts to a walk in `G` of
the same length, alternating between the two given indices. -/
theorem exists_alternating_walk {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {W : ConeChoice d} {a : ℕ}
    (ρ : Set (EuclideanSpace ℝ (Fin d)) → ZMod a → EuclideanSpace ℝ (Fin d))
    (hρ : ∀ B i, ρ B i ∈ blockFibre Γ B (W B))
    (hρlat : ∀ B i, ρ B i ∈ lattice d) :
    ∀ {B B' : Set (EuclideanSpace ℝ (Fin d))} (Wk : (choiceGraph Γ W).Walk B B')
      (α β : ZMod a),
      ∃ w : (latticeGraph Γ).Walk (ρ B α)
        (ρ B' (if Even Wk.length then α else β)), w.length = Wk.length := by
  intro B B' Wk
  induction Wk with
  | nil =>
      intro α _
      simp only [SimpleGraph.Walk.length_nil]
      exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | cons hadj Wk' ih =>
      intro α β
      obtain ⟨w', hw'⟩ := ih β α
      have hidx : (if Even (Wk'.length + 1) then α else β)
          = (if Even Wk'.length then β else α) := by
        by_cases he : Even Wk'.length
        · rw [if_neg (by simp [Nat.even_add_one, he]), if_pos he]
        · rw [if_pos (by simp [Nat.even_add_one, he]), if_neg he]
      rw [SimpleGraph.Walk.length_cons, hidx]
      refine ⟨SimpleGraph.Walk.cons ?_ w', ?_⟩
      · exact latticeAdj_of_choiceAdj hadj (hρlat _ _) (hρ _ _) (hρlat _ _) (hρ _ _)
      · rw [SimpleGraph.Walk.length_cons, hw']


/-! ## Blocks at distinct centres are distinct

Needed because `choiceAdj` carries `Q ≠ P`: the walk must not step from a block to
itself. Sparse population gives `h > √d ℓ`, so the cubes at distinct centres of
the index lattice are disjoint, and `ℓ ≥ 1` makes them nonempty. -/

/-- A cube of side at least `1` contains a lattice point. -/
theorem block_nonempty {ℓ : ℝ} (hℓ : 1 ≤ ℓ) (c : EuclideanSpace ℝ (Fin d)) :
    (block ℓ c).Nonempty := by
  refine ⟨WithLp.toLp 2 (fun i => ((round (c i) : ℤ) : ℝ)), ?_, ?_⟩
  · rw [mem_lattice_iff]
    exact fun i => ⟨round (c i), rfl⟩
  · refine infNorm_le (by linarith) (fun i => ?_)
    have he : (WithLp.toLp 2 (fun i => ((round (c i) : ℤ) : ℝ)) -
        c : EuclideanSpace ℝ (Fin d)) i = ((round (c i) : ℤ) : ℝ) - c i := by simp
    rw [he, abs_sub_comm]
    have := abs_sub_round (c i)
    linarith

/-- Blocks of a sparsely populated town at distinct centres are distinct. -/
theorem townIndex_ne {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {h ℓ : ℝ} (hh : 0 < h)
    (hℓ : 1 ≤ ℓ) (hsp : SparselyPopulated d ϑ h ℓ)
    {p q : EuclideanSpace ℝ (Fin d)} (hp : p ∈ lattice d) (hq : q ∈ lattice d)
    (hne : p ≠ q) : townIndex h ℓ p ≠ townIndex h ℓ q := by
  have hℓ0 : (0:ℝ) < ℓ := by linarith
  have hs2 : 0 < Real.sin (ϑ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
  have hs1 : Real.sin (ϑ / 2) ≤ 1 := Real.sin_le_one _
  have hD : (0:ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  -- sparse population forces `h > √d ℓ`
  have hδ : Real.sqrt d + 1 ≤ apexShrinkConst d ϑ := by
    rw [apexShrinkConst, le_div_iff₀ hs2]
    nlinarith
  have hbig : Real.sqrt d * ℓ < h := by
    rw [SparselyPopulated, lt_div_iff₀ hℓ0] at hsp
    nlinarith
  intro hEq
  obtain ⟨y, hylat, hycube⟩ := block_nonempty hℓ (h • p)
  have hEq' : block ℓ (h • p) = block ℓ (h • q) := hEq
  have hy2 : y ∈ block ℓ (h • q) := by rw [← hEq']; exact ⟨hylat, hycube⟩
  -- the two cube conditions force the centres close in the maximum norm
  have h1 : infNorm (y - h • p) ≤ ℓ / 2 := hycube
  have h2 : infNorm (y - h • q) ≤ ℓ / 2 := hy2.2
  have hsplit : h • p - h • q = (y - h • q) - (y - h • p) := by abel
  have h3 : infNorm (h • p - h • q) ≤ ℓ := by
    rw [hsplit, sub_eq_add_neg]
    refine le_trans (infNorm_add_le _ _) ?_
    rw [infNorm_neg]
    linarith
  have h4 : ‖h • p - h • q‖ ≤ Real.sqrt d * ℓ :=
    le_trans (norm_le_sqrt_dim_mul_infNorm _) (by nlinarith)
  have h5 : ‖h • p - h • q‖ = h * ‖p - q‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
  have h6 : 1 ≤ ‖p - q‖ := one_le_norm_sub_of_lattice hp hq hne
  rw [h5] at h4
  nlinarith


/-! ## Proposition 5.14 for the choice graph

The proof of Proposition 5.14 already fixes a favored cone per block before doing
anything else, so it produces the choice graph; only the statement had discarded
that. Here it is recorded. -/

/-- Connectivity in the choice graph, through blocks of `T`. -/
def ChoiceConn (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (W : ConeChoice d) (T : Set (Set (EuclideanSpace ℝ (Fin d)))) :
    Set (EuclideanSpace ℝ (Fin d)) → Set (EuclideanSpace ℝ (Fin d)) → Prop :=
  Relation.ReflTransGen (fun Q P => Q ∈ T ∧ P ∈ T ∧ choiceAdj Γ W Q P)

/-- **Proposition 5.14, refined.** The connectivity holds in the graph relative to
a single choice of favored cones, which is what Step 2 needs. -/
theorem renormalization_choice {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {r : ℝ}
    (hr : 0 < r) :
    ∃ R : ℝ, r ≤ R ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ →
      ∀ h ℓ : ℝ, 0 < h → 1 ≤ ℓ → SparselyPopulated d ϑ h ℓ →
      ∃ W : ConeChoice d,
        (∀ B, B.Finite → FavoredIn Γ B (W B)) ∧
        ∀ z ∈ lattice d, ∀ x ∈ lattice d, ∀ y ∈ lattice d,
          ‖x - z‖ ≤ r → ‖y - z‖ ≤ r →
          ChoiceConn Γ W (townBall h ℓ z R) (townIndex h ℓ x) (townIndex h ℓ y) := by
  classical
  have hϑ2 : (0:ℝ) < ϑ / 2 := by positivity
  have hϑ2' : ϑ / 2 ≤ π / 2 := by linarith [pi_pos]
  obtain ⟨R, hRr, hRprop⟩ :=
    discrete_template (d := d) (ϑ := ϑ / 2) hϑ2 hϑ2' (show (0:ℝ) < r + 1 by linarith)
  refine ⟨R, by linarith, ?_⟩
  intro Γ hΓ h ℓ hh hℓ hsp
  have hℓ0 : (0:ℝ) < ℓ := by linarith
  -- one favored cone per block, chosen once and for all
  have hex : ∀ B : Set (EuclideanSpace ℝ (Fin d)), ∃ V : DCone (EuclideanSpace ℝ (Fin d)),
      (B.Finite → FavoredIn Γ B V) ∧ (B.Finite → ∀ x ∈ B, ∃ p ∈ B, V = Γ p) := by
    intro B
    by_cases hB : B.Finite
    · obtain ⟨V, hV, hmem⟩ := exists_favoredIn Γ hB
      exact ⟨V, fun _ => hV, fun _ x hx => hmem ⟨x, hx⟩⟩
    · exact ⟨Γ 0, fun hc => absurd hc hB, fun hc => absurd hc hB⟩
  choose W hWfav hWmem using hex
  refine ⟨W, hWfav, ?_⟩
  intro z hz x hx y hy hxz hyz
  have hblkfin : ∀ p : EuclideanSpace ℝ (Fin d), (townIndex h ℓ p).Finite :=
    fun p => block_finite hℓ0.le (h • p)
  -- the induced `ϑ/2`-configuration on the index lattice
  set Γ' : Configuration (EuclideanSpace ℝ (Fin d)) :=
    fun p => ⟨(W (townIndex h ℓ p)).axis, (W (townIndex h ℓ p)).norm_axis, ϑ / 2, hϑ2, hϑ2'⟩
    with hΓ'
  have hΓ'b : IsBounded Γ' (ϑ / 2) := ⟨hϑ2, fun p => le_refl _⟩
  -- each edge of `Γ'` becomes an edge of the choice graph
  have hedge : ∀ p q : EuclideanSpace ℝ (Fin d), p ∈ lattice d → q ∈ lattice d →
      q ∈ coneAt Γ' p → choiceAdj Γ W (townIndex h ℓ p) (townIndex h ℓ q) := by
    intro p q hp hq hpq
    have hne : q ≠ p := by
      intro hc
      rw [hc, mem_coneAt, sub_self] at hpq
      exact (Γ' p).zero_notMem hpq
    refine ⟨townIndex_ne hϑ hϑ' hh hℓ hsp hp hq (fun hc => hne hc.symm), Or.inl ?_⟩
    intro x' hx' y' hy'
    obtain ⟨p0, hp0Q, hWp⟩ := hWmem _ (hblkfin p) x' hx'
    have hapex : ϑ ≤ (W (townIndex h ℓ p)).apex := by rw [hWp]; exact hΓ.2 p0
    have hax : ‖(W (townIndex h ℓ p)).axis‖ = 1 := (W (townIndex h ℓ p)).norm_axis
    obtain ⟨v, hv1, hvsub, hqp⟩ : ∃ v : EuclideanSpace ℝ (Fin d), ‖v‖ = 1 ∧
        cone v ϑ ⊆ (W (townIndex h ℓ p)).carrier ∧ q - p ∈ cone v (ϑ / 2) := by
      have hmem : q - p ∈ doubleCone (W (townIndex h ℓ p)).axis (ϑ / 2) := hpq
      rcases mem_doubleCone_iff.mp hmem with hc | hc
      · refine ⟨_, hax, fun u hu => ?_, hc⟩
        exact doubleCone_mono (le_of_lt hϑ) (W (townIndex h ℓ p)).apex_le_pi hapex
          (Set.mem_union_left _ hu)
      · refine ⟨-(W (townIndex h ℓ p)).axis, by simp [hax], fun u hu => ?_, ?_⟩
        · have h1 : u ∈ doubleCone (-(W (townIndex h ℓ p)).axis) ϑ := Set.mem_union_left _ hu
          rw [doubleCone_neg] at h1
          exact doubleCone_mono (le_of_lt hϑ) (W (townIndex h ℓ p)).apex_le_pi hapex h1
        · rw [cone_neg]; exact hc
    have hdist : apexShrinkConst d ϑ * ℓ ≤ ‖h • p - h • q‖ := by
      have h1 : ‖h • p - h • q‖ = h * ‖p - q‖ := by
        rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
      have h2 : 1 ≤ ‖p - q‖ := one_le_norm_sub_of_lattice hp hq (fun hc => hne hc.symm)
      have h3 : apexShrinkConst d ϑ * ℓ < h := by
        rw [SparselyPopulated, lt_div_iff₀ hℓ0] at hsp
        linarith
      have h4 : h ≤ h * ‖p - q‖ := by nlinarith
      linarith
    have hincone : h • q ∈ shift (cone v (ϑ / 2)) (h • p) := by
      rw [mem_shift, ← smul_sub]
      exact smul_mem_cone hv1 hϑ2 hϑ2' hh hqp
    have hcube := renormalization_apex_shrink hϑ hϑ' hv1 hℓ0 hdist hincone
    have := Set.mem_iInter₂.mp (hcube hy'.2) x' hx'.2
    rw [mem_shift] at this ⊢
    exact hvsub this
  -- transfer the paths
  have htrans : ∀ a b : EuclideanSpace ℝ (Fin d),
      ConnWithin Γ' (ball z R ∩ lattice d) a b →
      ChoiceConn Γ W (townBall h ℓ z R) (townIndex h ℓ a) (townIndex h ℓ b) := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih =>
        have hmemT : ∀ w ∈ ball z R ∩ lattice d, townIndex h ℓ w ∈ townBall h ℓ z R := by
          rintro w ⟨hwb, hwlat⟩
          refine ⟨w, ⟨hwlat, ?_⟩, rfl⟩
          rw [mem_ball, dist_eq_norm] at hwb
          exact hwb
        refine Relation.ReflTransGen.trans ih (Relation.ReflTransGen.single
          ⟨hmemT _ hstep.1, hmemT _ hstep.2.1, ?_⟩)
        rcases hstep.2.2 with he | he
        · exact hedge _ _ hstep.1.2 hstep.2.1.2 he
        · exact (choiceAdj_symm Γ W).symm _ _ (hedge _ _ hstep.2.1.2 hstep.1.2 he)
  have hconn := hRprop Γ' hΓ'b z hz
  have hzx := hconn x (by rw [mem_ball, dist_eq_norm]; linarith) hx
  have hzy := hconn y (by rw [mem_ball, dist_eq_norm]; linarith) hy
  refine Relation.ReflTransGen.trans ?_ (htrans _ _ hzy)
  -- symmetry of `ChoiceConn`
  have hsymm : ∀ {A B : Set (EuclideanSpace ℝ (Fin d))},
      ChoiceConn Γ W (townBall h ℓ z R) A B → ChoiceConn Γ W (townBall h ℓ z R) B A := by
    intro A B hAB
    induction hAB with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih =>
        exact Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single ⟨hstep.2.1, hstep.1,
            (choiceAdj_symm Γ W).symm _ _ hstep.2.2⟩) ih
  exact hsymm (htrans _ _ hzx)


/-! ## Step 1 for the choice graph, and the scheme's walks -/

lemma ChoiceConn.mono {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {W : ConeChoice d}
    {T T' : Set (Set (EuclideanSpace ℝ (Fin d)))} (hTT : T ⊆ T')
    {Q P : Set (EuclideanSpace ℝ (Fin d))} (h : ChoiceConn Γ W T Q P) :
    ChoiceConn Γ W T' Q P := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single ⟨hTT hstep.1, hTT hstep.2.1, hstep.2.2⟩)

/-- The bridge from `ChoiceConn` to walks in the choice graph. -/
theorem exists_choiceWalk_of_choiceConn {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {W : ConeChoice d}
    {T : Set (Set (EuclideanSpace ℝ (Fin d)))} (hTfin : T.Finite)
    {Q P : Set (EuclideanSpace ℝ (Fin d))} (hQ : Q ∈ T) (h : ChoiceConn Γ W T Q P) :
    ∃ w : (choiceGraph Γ W).Walk Q P, (∀ B ∈ w.support, B ∈ T) ∧ w.length < T.ncard := by
  classical
  exact exists_walk_of_reflTransGen_lt hTfin (fun _ _ hAB => Or.inr hAB.2.2)
    (fun _ _ hAB => ⟨hAB.1, hAB.2.1⟩) hQ h

/-- **Step 1 in the choice graph.** As `exists_favoredWalk_covering`, but for the
graph relative to a single choice of favored cones — the form Step 2 consumes. -/
theorem exists_choiceWalk_covering {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    {r : ℝ} (hr : 0 < r) :
    ∃ R : ℝ, r < R ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ →
      ∀ h ℓ : ℝ, 0 < h → 1 ≤ ℓ → SparselyPopulated d ϑ h ℓ →
      ∃ W : ConeChoice d,
        (∀ B, B.Finite → FavoredIn Γ B (W B)) ∧
        ∀ z ∈ lattice d,
          ∃ (Q P : Set (EuclideanSpace ℝ (Fin d))) (w : (choiceGraph Γ W).Walk Q P),
            (∀ B ∈ w.support, B ∈ townBall h ℓ z R) ∧
            w.length ≤ (2 * ⌈r⌉₊ + 1) ^ d * (2 * ⌈R⌉₊ + 1) ^ d ∧
            (∀ x ∈ lattice d, ‖x - z‖ ≤ r → townIndex h ℓ x ∈ w.support) := by
  classical
  obtain ⟨R₀, hR₀r, hprop⟩ := renormalization_choice (d := d) hϑ hϑ' hr
  refine ⟨R₀ + 1, by linarith, ?_⟩
  intro Γ hΓ h ℓ hh hℓ hsp
  obtain ⟨W, hWfav, hconn0⟩ := hprop Γ hΓ h ℓ hh hℓ hsp
  refine ⟨W, hWfav, ?_⟩
  intro z hz
  set R : ℝ := R₀ + 1 with hRdef
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
      rw [hTdef]; exact Set.ncard_image_le hsrcfin
    have h2 : {p : EuclideanSpace ℝ (Fin d) | p ∈ lattice d ∧ ‖p - z‖ ≤ r}
        ⊆ lattice d ∩ closedBall z r :=
      fun p hp => ⟨hp.1, by rw [Metric.mem_closedBall, dist_eq_norm]; exact hp.2⟩
    exact le_trans h1 (le_trans (Set.ncard_le_ncard h2 (lattice_inter_closedBall_finite z r))
      (ncard_lattice_inter_closedBall_le' z r))
  have hTsub : T ⊆ townBall h ℓ z R := by
    rw [hTdef]
    rintro _ ⟨p, ⟨hplat, hpr⟩, rfl⟩
    exact ⟨p, ⟨hplat, by rw [hRdef]; linarith⟩, rfl⟩
  have hconn : ∀ A ∈ T, ∀ B ∈ T, ∃ w : (choiceGraph Γ W).Walk A B,
      (∀ C ∈ w.support, C ∈ townBall h ℓ z R) ∧ w.length ≤ (2 * ⌈R⌉₊ + 1) ^ d := by
    intro A hA B hB
    rw [hTdef] at hA hB
    obtain ⟨x, ⟨hxlat, hxr⟩, rfl⟩ := hA
    obtain ⟨y, ⟨hylat, hyr⟩, rfl⟩ := hB
    have hc0 := hconn0 z hz x hxlat y hylat hxr hyr
    have hc1 : ChoiceConn Γ W (townBall h ℓ z R) (townIndex h ℓ x) (townIndex h ℓ y) :=
      ChoiceConn.mono (townBall_mono h ℓ z (by rw [hRdef]; linarith)) hc0
    obtain ⟨w, hwS, hwlen⟩ :=
      exists_choiceWalk_of_choiceConn (townBall_finite h ℓ z R)
        (hTsub (by rw [hTdef]; exact ⟨x, ⟨hxlat, hxr⟩, rfl⟩)) hc1
    exact ⟨w, hwS, le_of_lt (lt_of_lt_of_le hwlen (ncard_townBall_le h ℓ z R))⟩
  obtain ⟨Q, P, w, hQT, hPT, hwS, hwlen, hwcov⟩ :=
    exists_walk_covering (G := choiceGraph Γ W) hTfin hTne hconn
  refine ⟨Q, P, w, hwS, le_trans hwlen (Nat.mul_le_mul hTcard
    (le_refl ((2 * ⌈R⌉₊ + 1) ^ d))), fun x hxlat hxr => ?_⟩
  exact hwcov _ (by rw [hTdef]; exact ⟨x, ⟨hxlat, hxr⟩, rfl⟩)

end QFS
