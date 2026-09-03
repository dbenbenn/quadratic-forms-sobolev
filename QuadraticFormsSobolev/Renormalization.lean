/-
Section 5.2 of Bux–Kassmann–Schulze, "Renormalization: Blocks and Towns".

Lemma 5.9: at distances that are large compared to the cube size, passing from a
cone of apex angle `ϑ/2` to one of apex angle `ϑ` absorbs a whole cube at each
end.
-/
import QuadraticFormsSobolev.Section5

open Real Set Metric

namespace QFS

variable {d : ℕ}

/-- The constant `δ` of Lemma 5.9. The paper's `3√d/(2 sin ϑ)` is too small; see
the README. -/
noncomputable def apexShrinkConst (d : ℕ) (ϑ : ℝ) : ℝ :=
  (Real.sqrt d + 1) / Real.sin (ϑ / 2)

lemma apexShrinkConst_pos {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) :
    0 < apexShrinkConst d ϑ := by
  have hs2 : 0 < Real.sin (ϑ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
  have hD : (0:ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  rw [apexShrinkConst]
  positivity

/-- **Lemma 5.9** of Bux–Kassmann–Schulze. Whenever `‖x − y‖ ≥ δ ℓ` and `y` lies
in the cone of apex angle `ϑ/2` at `x`, the whole cube `Ā_ℓ(y)` lies in the cone
of apex angle `ϑ` based at *every* point of `Ā_ℓ(x)`. -/
theorem renormalization_apex_shrink {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {x y : EuclideanSpace ℝ (Fin d)}
    (hdist : apexShrinkConst d ϑ * ℓ ≤ ‖x - y‖) (hy : y ∈ shift (cone v (ϑ / 2)) x) :
    closedCube ℓ y ⊆ ⋂ z ∈ closedCube ℓ x, shift (cone v ϑ) z := by
  have hs2 : 0 < Real.sin (ϑ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
  have hD : (0:ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  rw [apexShrinkConst] at hdist
  intro u hu
  -- the gap of `y − x` with respect to the *wide* cone
  have hgapy : (Real.sqrt d + 1) * ℓ ≤ coneGap v ϑ (y - x) := by
    refine le_trans ?_ (coneGap_ge_of_mem_half hv hϑ hϑ' hy)
    have hnorm : (Real.sqrt d + 1) / Real.sin (ϑ / 2) * ℓ ≤ ‖y - x‖ := by
      rw [norm_sub_rev]; exact hdist
    have := mul_le_mul_of_nonneg_right hnorm (le_of_lt hs2)
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc,
      div_self (ne_of_gt hs2), mul_one] at this
    linarith [this]
  -- `u` is deep inside the wide cone at `x`
  have hux : ‖u - y‖ ≤ ℓ / 2 * Real.sqrt d := by
    have := closedCube_subset_closedBall (le_of_lt hℓ) y hu
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have hgapu : ℓ / 2 * Real.sqrt d < coneGap v ϑ (u - x) := by
    have hlip := coneGap_sub_le hv hϑ hϑ' (y - x) (u - x)
    have he : ‖y - x - (u - x)‖ = ‖u - y‖ := by
      rw [show y - x - (u - x) = -(u - y) by abel, norm_neg]
    rw [he] at hlip
    nlinarith
  have hshr : u - x ∈ shrink (cone v ϑ) (ℓ / 2 * Real.sqrt d) :=
    mem_shrink_cone_of_lt_coneGap hv hϑ hϑ' (by positivity) hgapu
  -- Lemma 2.7 (⋆): the shrunk cone lies in every translate by a small vector
  rw [shrink_eq_iInter_shift (cone v ϑ) (by positivity)] at hshr
  refine Set.mem_iInter₂.mpr (fun z hz => ?_)
  have hzx : ‖z - x‖ ≤ ℓ / 2 * Real.sqrt d := by
    have := closedCube_subset_closedBall (le_of_lt hℓ) x hz
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have hmem := Set.mem_iInter₂.mp hshr (z - x)
    (by rw [Metric.mem_closedBall, dist_zero_right]; exact hzx)
  rw [mem_shift] at hmem ⊢
  have he : u - x - (z - x) = u - z := by abel
  rwa [he] at hmem


/-! ## The paper's constant

The proof of Lemma 5.9 passes through the intermediate estimate

> if `y ∈ Ṽ[x]` and `|x − y| ≥ ℓ√d/(2 sin ϑ)`, then `B_{ℓ√d/2}(y) ⊆ V̄[x]`,

and concludes with `δ = 3√d/(2 sin ϑ)`. By `coneGap_eq_norm_mul_sin` the distance
from `y` to the boundary of `V̄[x]` is exactly `‖y − x‖ sin(ϑ − ∠(v, y−x))`, and
`y ∈ Ṽ[x]` only bounds `∠(v, y−x)` by `ϑ/2`. So at the threshold distance the
available gap can be as small as `ℓ√d sin(ϑ/2)/(2 sin ϑ)`, and the lemma below
says this is *always* less than the `ℓ√d/2` the estimate needs. -/

/-- The threshold distance used in the paper's proof of Lemma 5.9 is too small,
for every admissible apex angle: the gap it guarantees falls strictly short of
what the estimate requires. -/
theorem paper_threshold_insufficient {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    {c : ℝ} (hc : 0 < c) :
    c * Real.sin (ϑ / 2) / (2 * Real.sin ϑ) < c / 2 := by
  have hsϑ : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [pi_pos])
  have hlt : Real.sin (ϑ / 2) < Real.sin ϑ :=
    Real.strictMonoOn_sin ⟨by linarith [pi_pos], by linarith⟩
      ⟨by linarith [pi_pos], hϑ'⟩ (by linarith)
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith


/-- Lemma 5.9 in the paper's phrasing, "there is a constant `δ`". -/
theorem exists_apexShrinkConst {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ = 1 → ∀ ℓ : ℝ, 0 < ℓ →
      ∀ x y : EuclideanSpace ℝ (Fin d), δ * ℓ ≤ ‖x - y‖ →
        y ∈ shift (cone v (ϑ / 2)) x →
        closedCube ℓ y ⊆ ⋂ z ∈ closedCube ℓ x, shift (cone v ϑ) z :=
  ⟨apexShrinkConst d ϑ, apexShrinkConst_pos hϑ hϑ',
    fun _ hv _ hℓ _ _ hdist hy => renormalization_apex_shrink hϑ hϑ' hv hℓ hdist hy⟩

/-! ## Definition 5.10: blocks and towns -/

/-- A **block** `Q_ℓ(x) = ℤ^d ∩ Ā_ℓ(x)`: the lattice points inside a cube. -/
def block (ℓ : ℝ) (x : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  lattice d ∩ closedCube ℓ x

/-- The **town at scale `(h, ℓ)`**: the blocks centred at the points of `hℤ^d`. -/
def town (h ℓ : ℝ) : Set (Set (EuclideanSpace ℝ (Fin d))) :=
  (fun x => block ℓ x) '' scaledLattice d h

/-- A town of scale `(h, ℓ)` is **`ϑ`-sparsely populated** when the constant `δ`
of Lemma 5.9 is less than `h/ℓ`. -/
def SparselyPopulated (d : ℕ) (ϑ h ℓ : ℝ) : Prop := apexShrinkConst d ϑ < h / ℓ

/-- The paper's identification of the town with the integer lattice,
`x ↦ Q_ℓ(h x)`, used in the proof of Proposition 5.14. -/
def townIndex (h ℓ : ℝ) (x : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  block ℓ (h • x)

lemma townIndex_mem_town {h ℓ : ℝ} {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ lattice d) :
    townIndex h ℓ x ∈ town h ℓ := by
  refine ⟨h • x, ?_, rfl⟩
  intro i
  obtain ⟨n, hn⟩ := (mem_lattice_iff.mp hx) i
  refine ⟨n, ?_⟩
  have he : (h • x) i = h * x i := by simp
  rw [he, hn]
  ring

/-- Blocks are finite, so "maximal size" in Definition 5.11 is meaningful. -/
theorem block_finite {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (x : EuclideanSpace ℝ (Fin d)) :
    (block ℓ x).Finite :=
  (lattice_inter_closedBall_finite x (ℓ / 2 * Real.sqrt d)).subset
    (Set.inter_subset_inter Set.Subset.rfl (closedCube_subset_closedBall hℓ x))

/-- A block contains its centre, when that is a lattice point. -/
lemma mem_block_self {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ lattice d) : x ∈ block ℓ x := by
  refine ⟨hx, ?_⟩
  have he : infNorm (x - x) = 0 :=
    le_antisymm (infNorm_le le_rfl (fun i => by rw [sub_self]; simp)) (infNorm_nonneg _)
  simp only [closedCube, Set.mem_ofPred_eq, he]
  linarith

/-! ## Definition 5.11: favored by majority -/

/-- The fibre of `Γ` over a double cone inside a block. Types are compared as
double cones, following Definition 4.2. -/
def blockFibre (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (Q : Set (EuclideanSpace ℝ (Fin d))) (V : DCone (EuclideanSpace ℝ (Fin d))) :
    Set (EuclideanSpace ℝ (Fin d)) := {x ∈ Q | (Γ x).carrier = V.carrier}

/-- **Definition 5.11**: `V` is *favored by majority* in the block `Q` when its
fibre has maximal size. -/
def FavoredIn (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (Q : Set (EuclideanSpace ℝ (Fin d))) (V : DCone (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ W : DCone (EuclideanSpace ℝ (Fin d)),
    (blockFibre Γ Q W).encard ≤ (blockFibre Γ Q V).encard

/-- A cone favored by majority exists in every finite block, and when the block is
nonempty it is realised at one of its points — which is what gives it apex angle
at least `ϑ`.

**Remark 5.12** notes that it need not be unique; accordingly `FavoredIn` is a
predicate, not a function, and every later statement quantifies over *some*
favored cone. -/
theorem exists_favoredIn (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    {Q : Set (EuclideanSpace ℝ (Fin d))} (hQfin : Q.Finite) :
    ∃ V, FavoredIn Γ Q V ∧ (Q.Nonempty → ∃ p ∈ Q, V = Γ p) := by
  classical
  rcases Set.eq_empty_or_nonempty Q with hQ | hQne
  · refine ⟨Γ 0, fun W => ?_, fun hne => absurd hQ (Set.nonempty_iff_ne_empty.mp hne)⟩
    have : blockFibre Γ Q W = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro p ⟨hpQ, -⟩
      rw [hQ] at hpQ
      exact hpQ
    rw [this]
    simp
  · have hSfin : ((fun x => Γ x) '' Q).Finite := hQfin.image _
    have hSne : hSfin.toFinset.Nonempty := by
      obtain ⟨p, hp⟩ := hQne
      exact ⟨Γ p, by simpa using ⟨p, hp, rfl⟩⟩
    obtain ⟨V, hVS, hVmax⟩ :=
      Finset.exists_max_image hSfin.toFinset (fun W => (blockFibre Γ Q W).encard) hSne
    refine ⟨V, fun W => ?_, fun _ => ?_⟩
    · rcases Set.eq_empty_or_nonempty (blockFibre Γ Q W) with hW | ⟨p, hpQ, hptype⟩
      · rw [hW]; simp
      · have hfib : blockFibre Γ Q W = blockFibre Γ Q (Γ p) := by
          simp only [blockFibre, hptype]
        rw [hfib]
        exact hVmax (Γ p) (by simpa using ⟨p, hpQ, rfl⟩)
    · obtain ⟨p, hpQ, hp⟩ : ∃ p ∈ Q, Γ p = V := by simpa using hVS
      exact ⟨p, hpQ, hp.symm⟩

/-! ## Definition 5.13: the favored graph -/

/-- **Definition 5.13**: a directed edge from block `Q` to block `P`, given by a
cone favored by majority in `Q` that contains every point of `P` when based at
every point of `Q`. -/
def FavoredEdge (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (Q P : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ V : DCone (EuclideanSpace ℝ (Fin d)), FavoredIn Γ Q V ∧
    ∀ x ∈ Q, ∀ y ∈ P, y ∈ shift V.carrier x

/-- Connectivity in the **favored graph** of a town, by undirected edge paths
through blocks of `T`. -/
def FavoredConn (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (T : Set (Set (EuclideanSpace ℝ (Fin d)))) :
    Set (EuclideanSpace ℝ (Fin d)) → Set (EuclideanSpace ℝ (Fin d)) → Prop :=
  Relation.ReflTransGen
    (fun Q P => Q ∈ T ∧ P ∈ T ∧ (FavoredEdge Γ Q P ∨ FavoredEdge Γ P Q))

@[refl] lemma FavoredConn.refl (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (T : Set (Set (EuclideanSpace ℝ (Fin d)))) (Q : Set (EuclideanSpace ℝ (Fin d))) :
    FavoredConn Γ T Q Q := Relation.ReflTransGen.refl

lemma FavoredConn.trans {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {T : Set (Set (EuclideanSpace ℝ (Fin d)))} {Q P S : Set (EuclideanSpace ℝ (Fin d))}
    (h₁ : FavoredConn Γ T Q P) (h₂ : FavoredConn Γ T P S) : FavoredConn Γ T Q S :=
  Relation.ReflTransGen.trans h₁ h₂

lemma FavoredConn.symm {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {T : Set (Set (EuclideanSpace ℝ (Fin d)))} {Q P : Set (EuclideanSpace ℝ (Fin d))}
    (h : FavoredConn Γ T Q P) : FavoredConn Γ T P Q := by
  induction h with
  | refl => exact FavoredConn.refl _ _ _
  | tail _ hstep ih =>
      exact FavoredConn.trans
        (Relation.ReflTransGen.single ⟨hstep.2.1, hstep.1, hstep.2.2.symm⟩) ih


/-! ## The favored graph as a simple graph

`FavoredEdge Γ ∅ ∅` holds vacuously, so the edge relation is reflexive at the
empty block and cannot be a `SimpleGraph` adjacency as it stands; the graph
therefore carries an explicit `Q ≠ P`. On nonempty blocks this changes nothing,
since `FavoredEdge Γ Q Q` would put `0` in a cone. -/

/-- Adjacency in the favored graph. -/
def favoredAdj (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (Q P : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  Q ≠ P ∧ (FavoredEdge Γ Q P ∨ FavoredEdge Γ P Q)

instance favoredAdj_symm (Γ : Configuration (EuclideanSpace ℝ (Fin d))) :
    Std.Symm (favoredAdj Γ) := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩

instance favoredAdj_irrefl (Γ : Configuration (EuclideanSpace ℝ (Fin d))) :
    Std.Irrefl (favoredAdj Γ) := ⟨fun _ h => h.1 rfl⟩

/-- The **favored graph** of Definition 5.13, as a simple graph on blocks. -/
def favoredGraph (Γ : Configuration (EuclideanSpace ℝ (Fin d))) :
    SimpleGraph (Set (EuclideanSpace ℝ (Fin d))) :=
  ⟨favoredAdj Γ, favoredAdj_symm Γ, favoredAdj_irrefl Γ⟩

/-- A nonempty block is never adjacent to itself even before the guard. -/
lemma not_favoredEdge_self {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {Q : Set (EuclideanSpace ℝ (Fin d))} (hQ : Q.Nonempty) : ¬ FavoredEdge Γ Q Q := by
  rintro ⟨V, -, hV⟩
  obtain ⟨x, hx⟩ := hQ
  have := hV x hx x hx
  rw [mem_shift, sub_self] at this
  exact V.zero_notMem this

/-! ## Proposition 5.14 -/

/-- The blocks of the town whose index lies within `R` of `z`; the paper's blocks
"not farther away from `z` than `hR`". -/
def townBall (h ℓ : ℝ) (z : EuclideanSpace ℝ (Fin d)) (R : ℝ) :
    Set (Set (EuclideanSpace ℝ (Fin d))) :=
  (fun p => townIndex h ℓ p) '' {p | p ∈ lattice d ∧ ‖p - z‖ < R}

/-- **Proposition 5.14** of Bux–Kassmann–Schulze. For every radius `r` there is
`R ≥ r`, depending only on `r`, `ϑ` and `d`, such that in a `ϑ`-sparsely
populated town of scale `(h, ℓ)` any two blocks whose indices lie within `r` of a
point `z` of the index lattice are connected in the favored graph by a path
through blocks whose indices stay within `R` of `z`.

The proof is the paper's: the town is identified with `ℤ^d` by `x ↦ Q_ℓ(hx)`, the
configuration `x ↦` (the cone of apex angle `ϑ/2` with the axis of a cone favored
in `Q_ℓ(hx)`) is `ϑ/2`-bounded, Lemma 5.9 turns each of its edges into an edge of
the favored graph — this is exactly where sparse population is used, since it
makes `δℓ < h ≤ ‖hx − hy‖` for distinct `x, y` — and Corollary 5.8 supplies the
connectivity. -/
theorem renormalization {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {r : ℝ} (hr : 0 < r) :
    ∃ R : ℝ, r ≤ R ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ →
      ∀ h ℓ : ℝ, 0 < h → 0 < ℓ → SparselyPopulated d ϑ h ℓ →
      ∀ z ∈ lattice d, ∀ x ∈ lattice d, ∀ y ∈ lattice d,
        ‖x - z‖ ≤ r → ‖y - z‖ ≤ r →
        FavoredConn Γ (townBall h ℓ z R) (townIndex h ℓ x) (townIndex h ℓ y) := by
  have hϑ2 : (0:ℝ) < ϑ / 2 := by positivity
  have hϑ2' : ϑ / 2 ≤ π / 2 := by linarith [pi_pos]
  obtain ⟨R, hRr, hRprop⟩ :=
    discrete_template (d := d) (ϑ := ϑ / 2) hϑ2 hϑ2' (show (0:ℝ) < r + 1 by linarith)
  refine ⟨R, by linarith, ?_⟩
  intro Γ hΓ h ℓ hh hℓ hsp z hz x hx y hy hxz hyz
  -- a favored cone in each block, and the induced `ϑ/2`-configuration on `ℤ^d`
  choose W hWfav hWmem using
    fun p : EuclideanSpace ℝ (Fin d) => exists_favoredIn Γ (block_finite hℓ.le (h • p))
  set Γ' : Configuration (EuclideanSpace ℝ (Fin d)) :=
    fun p => ⟨(W p).axis, (W p).norm_axis, ϑ / 2, hϑ2, hϑ2'⟩ with hΓ'
  have hΓ'b : IsBounded Γ' (ϑ / 2) := ⟨hϑ2, fun p => le_refl _⟩
  -- each edge of `Γ'` becomes an edge of the favored graph
  have hedge : ∀ p q : EuclideanSpace ℝ (Fin d), p ∈ lattice d → q ∈ lattice d →
      q ∈ coneAt Γ' p → FavoredEdge Γ (townIndex h ℓ p) (townIndex h ℓ q) := by
    intro p q hp hq hpq
    refine ⟨W p, hWfav p, fun x' hx' y' hy' => ?_⟩
    obtain ⟨p0, hp0Q, hWp⟩ := hWmem p ⟨x', hx'⟩
    have hapex : ϑ ≤ (W p).apex := by rw [hWp]; exact hΓ.2 p0
    have hax : ‖(W p).axis‖ = 1 := (W p).norm_axis
    have hne : q ≠ p := by
      intro hc
      rw [hc, mem_coneAt, sub_self] at hpq
      exact (Γ' p).zero_notMem hpq
    -- pick the half-cone containing `q − p`
    obtain ⟨v, hv1, hvsub, hqp⟩ : ∃ v : EuclideanSpace ℝ (Fin d), ‖v‖ = 1 ∧
        cone v ϑ ⊆ (W p).carrier ∧ q - p ∈ cone v (ϑ / 2) := by
      have hmem : q - p ∈ doubleCone (W p).axis (ϑ / 2) := hpq
      rcases mem_doubleCone_iff.mp hmem with hc | hc
      · refine ⟨(W p).axis, hax, fun u hu => ?_, hc⟩
        exact doubleCone_mono (le_of_lt hϑ) (W p).apex_le_pi hapex
          (Set.mem_union_left _ hu)
      · refine ⟨-(W p).axis, by simp [hax], fun u hu => ?_, ?_⟩
        · have h1 : u ∈ doubleCone (-(W p).axis) ϑ := Set.mem_union_left _ hu
          rw [doubleCone_neg] at h1
          exact doubleCone_mono (le_of_lt hϑ) (W p).apex_le_pi hapex h1
        · rw [cone_neg]; exact hc
    -- Lemma 5.9 applies: sparse population gives the distance
    have hscale : h • q - h • p = h • (q - p) := by rw [smul_sub]
    have hdist : apexShrinkConst d ϑ * ℓ ≤ ‖h • p - h • q‖ := by
      have h1 : ‖h • p - h • q‖ = h * ‖p - q‖ := by
        rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
      have h2 : 1 ≤ ‖p - q‖ := one_le_norm_sub_of_lattice hp hq (fun hc => hne hc.symm)
      have h3 : apexShrinkConst d ϑ * ℓ < h := by
        rw [SparselyPopulated, lt_div_iff₀ hℓ] at hsp
        linarith
      have h4 : h ≤ h * ‖p - q‖ := by nlinarith
      linarith
    have hincone : h • q ∈ shift (cone v (ϑ / 2)) (h • p) := by
      rw [mem_shift, hscale]
      exact smul_mem_cone hv1 hϑ2 hϑ2' hh hqp
    have hcube := renormalization_apex_shrink hϑ hϑ' hv1 hℓ hdist hincone
    have hy'c : y' ∈ closedCube ℓ (h • q) := hy'.2
    have hx'c : x' ∈ closedCube ℓ (h • p) := hx'.2
    have := Set.mem_iInter₂.mp (hcube hy'c) x' hx'c
    rw [mem_shift] at this ⊢
    exact hvsub this
  -- transfer paths
  have htrans : ∀ a b : EuclideanSpace ℝ (Fin d),
      ConnWithin Γ' (ball z R ∩ lattice d) a b →
      FavoredConn Γ (townBall h ℓ z R) (townIndex h ℓ a) (townIndex h ℓ b) := by
    intro a b hab
    induction hab with
    | refl => exact FavoredConn.refl _ _ _
    | tail _ hstep ih =>
        have hmemT : ∀ w ∈ ball z R ∩ lattice d, townIndex h ℓ w ∈ townBall h ℓ z R := by
          rintro w ⟨hwb, hwlat⟩
          refine ⟨w, ⟨hwlat, ?_⟩, rfl⟩
          rw [mem_ball, dist_eq_norm] at hwb
          exact hwb
        refine FavoredConn.trans ih (Relation.ReflTransGen.single
          ⟨hmemT _ hstep.1, hmemT _ hstep.2.1, ?_⟩)
        exact hstep.2.2.imp (fun e => hedge _ _ hstep.1.2 hstep.2.1.2 e)
          (fun e => hedge _ _ hstep.2.1.2 hstep.1.2 e)
  -- Corollary 5.8 connects `z` to `x` and to `y`
  have hconn := hRprop Γ' hΓ'b z hz
  have hzx := hconn x (by rw [mem_ball, dist_eq_norm]; linarith) hx
  have hzy := hconn y (by rw [mem_ball, dist_eq_norm]; linarith) hy
  exact FavoredConn.trans (htrans _ _ hzx).symm (htrans _ _ hzy)

end QFS
