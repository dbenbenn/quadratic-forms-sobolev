/-
Section 5 of Bux–Kassmann–Schulze, "Chaining and renormalization", auxiliary
results: Lemmas 5.1, 5.2, 5.4 and 5.5, the quantitative discrete counterparts of
the Section 4 lemmas.

The point of the discrete setting is to keep track of how far an edge path may
wander, so connectivity is taken here inside a prescribed set of vertices.
-/
import QuadraticFormsSobolev.Section4
import QuadraticFormsSobolev.Section3

open Real Set Metric

namespace QFS

variable {d : ℕ}

/-! ## Lattice points are `√d/2`-dense

"Any closed ball of radius `√d/2` contains a lattice point." -/

/-- Rounding each coordinate produces a lattice point within `√d/2`. -/
theorem exists_lattice_mem_closedBall (z : EuclideanSpace ℝ (Fin d)) :
    ∃ y ∈ lattice d, ‖y - z‖ ≤ Real.sqrt d / 2 := by
  refine ⟨WithLp.toLp 2 (fun i => ((round (z i) : ℤ) : ℝ)), ?_, ?_⟩
  · rw [mem_lattice_iff]
    exact fun i => ⟨round (z i), rfl⟩
  · refine le_trans (norm_le_sqrt_dim_mul_infNorm _) ?_
    have hb : infNorm (WithLp.toLp 2 (fun i => ((round (z i) : ℤ) : ℝ)) - z) ≤ 1 / 2 := by
      refine infNorm_le (by norm_num) (fun i => ?_)
      have he : (WithLp.toLp 2 (fun i => ((round (z i) : ℤ) : ℝ)) - z) i
          = ((round (z i) : ℤ) : ℝ) - z i := by simp
      rw [he, abs_sub_comm]
      exact abs_sub_round (z i)
    calc Real.sqrt d * infNorm (WithLp.toLp 2 (fun i => ((round (z i) : ℤ) : ℝ)) - z)
        ≤ Real.sqrt d * (1 / 2) := by
          exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
      _ = Real.sqrt d / 2 := by ring

/-! ## Connectivity inside a prescribed set of vertices

Definition 5.3 speaks of edge paths "not leaving `B_R(x)`", so unlike `Conn` of
Section 4 — where intermediate vertices were unconstrained — every vertex of the
path is now required to lie in a given set. -/

/-- Undirected connectivity by edge paths all of whose vertices lie in `S`. -/
def ConnWithin (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (S : Set (EuclideanSpace ℝ (Fin d))) :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → Prop :=
  Relation.ReflTransGen
    (fun a b => a ∈ S ∧ b ∈ S ∧ (b ∈ coneAt Γ a ∨ a ∈ coneAt Γ b))

variable {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
  {S S' : Set (EuclideanSpace ℝ (Fin d))}

@[refl] lemma ConnWithin.refl (x : EuclideanSpace ℝ (Fin d)) : ConnWithin Γ S x x :=
  Relation.ReflTransGen.refl

lemma ConnWithin.trans {x y z : EuclideanSpace ℝ (Fin d)}
    (h₁ : ConnWithin Γ S x y) (h₂ : ConnWithin Γ S y z) : ConnWithin Γ S x z :=
  Relation.ReflTransGen.trans h₁ h₂

lemma ConnWithin.symm {x y : EuclideanSpace ℝ (Fin d)} (h : ConnWithin Γ S x y) :
    ConnWithin Γ S y x := by
  induction h with
  | refl => exact ConnWithin.refl _
  | tail _ hstep ih =>
      exact ConnWithin.trans
        (Relation.ReflTransGen.single ⟨hstep.2.1, hstep.1, hstep.2.2.symm⟩) ih

lemma ConnWithin.mono (h : S ⊆ S') {x y : EuclideanSpace ℝ (Fin d)}
    (hxy : ConnWithin Γ S x y) : ConnWithin Γ S' x y := by
  induction hxy with
  | refl => exact ConnWithin.refl _
  | tail _ hstep ih =>
      exact ConnWithin.trans ih
        (Relation.ReflTransGen.single ⟨h hstep.1, h hstep.2.1, hstep.2.2⟩)

/-- A single edge, both of whose endpoints lie in `S`. -/
lemma ConnWithin.of_edge {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ S) (hy : y ∈ S)
    (h : y ∈ coneAt Γ x) : ConnWithin Γ S x y :=
  Relation.ReflTransGen.single ⟨hx, hy, Or.inl h⟩


/-! ## Lemma 5.1: producing lattice points inside cones -/

/-- **Lemma 5.1 (1)** of Bux–Kassmann–Schulze. For a cone of apex angle at least
`ϑ`, if `R > (r + √d)/sin ϑ` then `B_R(x) ∩ Ṽ[x]` contains a lattice point `y`
with `B_r(y) ⊆ Ṽ[x]`. -/
theorem exists_lattice_mem_cone {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {ϑ ϑV : ℝ} (hϑ : 0 < ϑ) (hϑV : ϑ ≤ ϑV) (hϑV' : ϑV ≤ π / 2)
    {r R : ℝ} (hr : 0 < r) (hR : (r + Real.sqrt d) / Real.sin ϑ < R)
    (x : EuclideanSpace ℝ (Fin d)) :
    ∃ y ∈ lattice d, ‖y - x‖ < R ∧ y ∈ shift (cone v ϑV) x ∧
      closedBall y r ⊆ shift (cone v ϑV) x := by
  have hs0 : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [pi_pos, hϑV'])
  have hs1 : Real.sin ϑ ≤ 1 := Real.sin_le_one ϑ
  have hsV : Real.sin ϑ ≤ Real.sin ϑV :=
    Real.strictMonoOn_sin.monotoneOn ⟨by linarith [pi_pos], by linarith⟩
      ⟨by linarith [pi_pos, hϑ], hϑV'⟩ hϑV
  have hdnn : (0:ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  -- Room to choose the height `t` along the axis.
  have hsd : Real.sqrt d / 2 ≤ Real.sqrt d / 2 / Real.sin ϑ := by
    rw [le_div_iff₀ hs0]; nlinarith
  have hsplit : (r + Real.sqrt d) / Real.sin ϑ
      = (r + Real.sqrt d / 2) / Real.sin ϑ + Real.sqrt d / 2 / Real.sin ϑ := by
    field_simp; ring
  have hgap : (r + Real.sqrt d / 2) / Real.sin ϑ < R - Real.sqrt d / 2 := by linarith
  obtain ⟨t, ht1, ht2⟩ : ∃ t : ℝ, (r + Real.sqrt d / 2) / Real.sin ϑ < t ∧
      t + Real.sqrt d / 2 < R :=
    ⟨((r + Real.sqrt d / 2) / Real.sin ϑ + (R - Real.sqrt d / 2)) / 2, by linarith, by linarith⟩
  have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht1
  have htsin : r + Real.sqrt d / 2 < t * Real.sin ϑ := by
    rw [div_lt_iff₀ hs0] at ht1; linarith
  -- A whole ball of radius `r + √d/2` about `x + t·v` lies in the cone.
  have hball : ∀ u : EuclideanSpace ℝ (Fin d), ‖u - (x + t • v)‖ ≤ r + Real.sqrt d / 2 →
      u ∈ shift (cone v ϑV) x := by
    intro u hu
    rw [mem_shift]
    refine mem_cone_of_norm_sub_lt hv (lt_of_lt_of_le hϑ hϑV) hϑV' ht0 ?_
    have he : u - x - t • v = u - (x + t • v) := by abel
    rw [he]
    calc ‖u - (x + t • v)‖ ≤ r + Real.sqrt d / 2 := hu
      _ < t * Real.sin ϑ := htsin
      _ ≤ t * Real.sin ϑV := by exact mul_le_mul_of_nonneg_left hsV ht0.le
  -- A lattice point within `√d/2` of that centre.
  obtain ⟨y, hylat, hyz⟩ := exists_lattice_mem_closedBall (x + t • v)
  refine ⟨y, hylat, ?_, hball y (by linarith), ?_⟩
  · have hzx : ‖x + t • v - x‖ = t := by
      have he : x + t • v - x = t • v := by abel
      rw [he, norm_smul, hv, Real.norm_eq_abs, abs_of_pos ht0, mul_one]
    calc ‖y - x‖ = ‖(y - (x + t • v)) + (x + t • v - x)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖y - (x + t • v)‖ + ‖x + t • v - x‖ := norm_add_le _ _
      _ ≤ Real.sqrt d / 2 + t := by rw [hzx]; linarith
      _ < R := by linarith
  · intro u hu
    rw [Metric.mem_closedBall, dist_eq_norm] at hu
    refine hball u ?_
    calc ‖u - (x + t • v)‖ = ‖(u - y) + (y - (x + t • v))‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖u - y‖ + ‖y - (x + t • v)‖ := norm_add_le _ _
      _ ≤ r + Real.sqrt d / 2 := by linarith

/-- **Lemma 5.1 (2)**: a lattice point in `B_R(x) ∩ Ṽ[x] ∩ B_R(y) ∩ Ṽ[y]`, when
`r > ‖x − y‖` and `R > (r + √d)/sin ϑ + r`. -/
theorem exists_lattice_mem_inter {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {ϑ ϑV : ℝ} (hϑ : 0 < ϑ) (hϑV : ϑ ≤ ϑV) (hϑV' : ϑV ≤ π / 2)
    {r R : ℝ} {x y : EuclideanSpace ℝ (Fin d)} (hxy : ‖x - y‖ < r)
    (hR : (r + Real.sqrt d) / Real.sin ϑ + r < R) :
    ∃ z ∈ lattice d, ‖z - x‖ < R - r ∧ ‖z - y‖ < R ∧
      z ∈ shift (cone v ϑV) x ∧ z ∈ shift (cone v ϑV) y := by
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg _) hxy
  obtain ⟨z, hzlat, hzx, hzc, hzball⟩ :=
    exists_lattice_mem_cone hv hϑ hϑV hϑV' hr
      (by linarith : (r + Real.sqrt d) / Real.sin ϑ < R - r) x
  refine ⟨z, hzlat, hzx, ?_, hzc, ?_⟩
  · calc ‖z - y‖ = ‖(z - x) + (x - y)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖z - x‖ + ‖x - y‖ := norm_add_le _ _
      _ < (R - r) + r := by linarith
      _ = R := by ring
  · -- `Ṽ[y]` is `Ṽ[x]` translated by less than `r`, and `B̄_r(z) ⊆ Ṽ[x]`.
    have hmem : z + (x - y) ∈ shift (cone v ϑV) x := by
      refine hzball ?_
      rw [Metric.mem_closedBall, dist_eq_norm]
      have he : z + (x - y) - z = x - y := by abel
      rw [he]
      exact hxy.le
    rw [mem_shift] at hmem ⊢
    have he : z + (x - y) - x = z - y := by abel
    rwa [he] at hmem


/-! ## Corollary 5.2, Definition 5.3, Lemmas 5.4 and 5.5 -/

variable {ϑ : ℝ}

/-- A half-cone sits inside the double cone it belongs to. -/
lemma cone_subset_carrier (V : DCone (EuclideanSpace ℝ (Fin d))) :
    cone V.axis V.apex ⊆ V.carrier := Set.subset_union_left

/-- **Corollary 5.2**, the quantitative form of Lemma 4.3: two lattice points of
the same type at distance less than `r` are joined by a path of two edges inside
`B_R(x)`, for `R > (r + √d)/sin ϑ + r`. -/
theorem discr_connect_two_of_same_type (hϑ : 0 < ϑ) (hb : ∀ z, ϑ ≤ (Γ z).apex)
    {r R : ℝ} {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ lattice d) (hy : y ∈ lattice d)
    (htype : (Γ x).carrier = (Γ y).carrier) (hxy : ‖x - y‖ < r)
    (hR : (r + Real.sqrt d) / Real.sin ϑ + r < R) :
    ConnWithin Γ (ball x R ∩ lattice d) x y := by
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg _) hxy
  have hs0 : 0 < Real.sin ϑ :=
    Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [pi_pos, (Γ x).apex_le, hb x])
  have hpos : 0 < (r + Real.sqrt d) / Real.sin ϑ := by positivity
  have hrR : r < R := by linarith
  obtain ⟨z, hzlat, hzx, hzy, hzcx, hzcy⟩ :=
    exists_lattice_mem_inter (v := (Γ x).axis) (Γ x).norm_axis hϑ (hb x) (Γ x).apex_le hxy hR
  have hxb : x ∈ ball x R ∩ lattice d := ⟨mem_ball_self (by linarith), hx⟩
  have hyb : y ∈ ball x R ∩ lattice d := by
    refine ⟨?_, hy⟩
    rw [mem_ball, dist_eq_norm, norm_sub_rev]; linarith
  have hzb : z ∈ ball x R ∩ lattice d := by
    refine ⟨?_, hzlat⟩
    rw [mem_ball, dist_eq_norm]; linarith
  refine ConnWithin.trans (ConnWithin.of_edge hxb hzb ?_) (ConnWithin.of_edge hyb hzb ?_).symm
  · rw [mem_coneAt]; exact cone_subset_carrier _ hzcx
  · rw [mem_coneAt, ← htype]; exact cone_subset_carrier _ hzcy

/-- **Definition 5.3**: a lattice point `x` is *`r`-`R`-connected* when every
lattice point of `B_r(x)` is joined to `x` by an undirected edge path that does
not leave `B_R(x)`. -/
def RRConnected (Γ : Configuration (EuclideanSpace ℝ (Fin d))) (r R : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ y ∈ ball x r, y ∈ lattice d → ConnWithin Γ (ball x R ∩ lattice d) x y

/-- **Lemma 5.4**, the discrete counterpart of the density of well-connected
points (Lemma 4.5 (3)): for `R > (√d + r)/sin ϑ` every lattice point `x` has an
`r`-`R`-connected lattice point in `B_R(x)`. -/
theorem exists_rrConnected (hϑ : 0 < ϑ) (hb : ∀ z, ϑ ≤ (Γ z).apex) {r R : ℝ} (hr : 0 ≤ r)
    (hR : (Real.sqrt d + r) / Real.sin ϑ < R) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ lattice d) :
    ∃ y ∈ lattice d, ‖y - x‖ < R ∧ RRConnected Γ r R y := by
  have hs0 : 0 < Real.sin ϑ :=
    Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [pi_pos, (Γ x).apex_le, hb x])
  have hs1 : Real.sin ϑ ≤ 1 := Real.sin_le_one ϑ
  have hdnn : (0:ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hmul : Real.sqrt d + r < R * Real.sin ϑ := by
    rw [div_lt_iff₀ hs0] at hR; linarith
  have hR0 : 0 < R := by nlinarith
  have hrR : r ≤ R := by nlinarith
  -- Enlarge `r` slightly, so that Lemma 5.1 (1) applies and `B_r(y)` is strictly inside.
  set r' : ℝ := (r + R * Real.sin ϑ - Real.sqrt d) / 2 with hr'def
  have hrr' : r < r' := by rw [hr'def]; linarith
  have hr'0 : 0 < r' := lt_of_le_of_lt hr hrr'
  have hr'R : (r' + Real.sqrt d) / Real.sin ϑ < R := by
    rw [div_lt_iff₀ hs0, hr'def]; linarith
  obtain ⟨y, hylat, hyx, hyc, hyball⟩ :=
    exists_lattice_mem_cone (v := (Γ x).axis) (Γ x).norm_axis hϑ (hb x) (Γ x).apex_le hr'0
      hr'R x
  refine ⟨y, hylat, hyx, fun p hp hplat => ?_⟩
  rw [mem_ball, dist_eq_norm] at hp
  -- `p` and `y` both lie in the cone at `x`, so both receive an edge from `x`.
  have hpc : p ∈ shift (cone (Γ x).axis (Γ x).apex) x := by
    refine hyball ?_
    rw [Metric.mem_closedBall, dist_eq_norm]; linarith
  have hyb : y ∈ ball y R ∩ lattice d := ⟨mem_ball_self hR0, hylat⟩
  have hxb : x ∈ ball y R ∩ lattice d := by
    refine ⟨?_, hx⟩
    rw [mem_ball, dist_eq_norm, norm_sub_rev]; exact hyx
  have hpb : p ∈ ball y R ∩ lattice d := by
    refine ⟨?_, hplat⟩
    rw [mem_ball, dist_eq_norm]; linarith
  refine ConnWithin.trans (ConnWithin.of_edge hxb hyb ?_).symm (ConnWithin.of_edge hxb hpb ?_)
  · rw [mem_coneAt]; exact cone_subset_carrier _ hyc
  · rw [mem_coneAt]; exact cone_subset_carrier _ hpc

/-- **Lemma 5.5**, the discrete counterpart of Lemma 4.6 ("über Bande"). If a
lattice point `z` of type `Γ(y)` lies in `B_r(x) ∩ Γ(y)[x]`, then `y` and `x` are
joined by an edge path inside `B_R(x)`, for `R > r + (2r + √d)/sin ϑ`. -/
theorem discr_ueber_bande (hϑ : 0 < ϑ) (hb : ∀ w, ϑ ≤ (Γ w).apex)
    {r R : ℝ} {x y z : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ lattice d) (hy : y ∈ lattice d) (hz : z ∈ lattice d)
    (hxy : ‖x - y‖ < r) (hzx : ‖z - x‖ < r) (hzV : z ∈ shift (Γ y).carrier x)
    (htype : (Γ z).carrier = (Γ y).carrier)
    (hR : r + (2 * r + Real.sqrt d) / Real.sin ϑ < R) :
    ConnWithin Γ (ball x R ∩ lattice d) y x := by
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg _) hxy
  have hs0 : 0 < Real.sin ϑ :=
    Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [pi_pos, (Γ y).apex_le, hb y])
  have hpos : 0 < (2 * r + Real.sqrt d) / Real.sin ϑ := by positivity
  have hrR : r < R := by linarith
  -- `z` and `y` have the same type and are at distance less than `2r`.
  have hzy : ‖z - y‖ < 2 * r := by
    calc ‖z - y‖ = ‖(z - x) + (x - y)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖z - x‖ + ‖x - y‖ := norm_add_le _ _
      _ < 2 * r := by linarith
  obtain ⟨w, hwlat, hwz, hwc, hwball⟩ :=
    exists_lattice_mem_cone (v := (Γ y).axis) (Γ y).norm_axis hϑ (hb y) (Γ y).apex_le
      (by linarith : (0:ℝ) < 2 * r) (by linarith : (2 * r + Real.sqrt d) / Real.sin ϑ < R - r) z
  -- `w` also lies in the cone based at `y`.
  have hwy : w ∈ shift (cone (Γ y).axis (Γ y).apex) y := by
    have hmem : w + (z - y) ∈ shift (cone (Γ y).axis (Γ y).apex) z := by
      refine hwball ?_
      rw [Metric.mem_closedBall, dist_eq_norm]
      have he : w + (z - y) - w = z - y := by abel
      rw [he]; linarith
    rw [mem_shift] at hmem ⊢
    have he : w + (z - y) - z = w - y := by abel
    rwa [he] at hmem
  -- All four vertices lie in `B_R(x)`.
  have hxb : x ∈ ball x R ∩ lattice d := ⟨mem_ball_self (by linarith), hx⟩
  have hyb : y ∈ ball x R ∩ lattice d := by
    refine ⟨?_, hy⟩
    rw [mem_ball, dist_eq_norm, norm_sub_rev]; linarith
  have hzb : z ∈ ball x R ∩ lattice d := by
    refine ⟨?_, hz⟩
    rw [mem_ball, dist_eq_norm]; linarith
  have hwb : w ∈ ball x R ∩ lattice d := by
    refine ⟨?_, hwlat⟩
    rw [mem_ball, dist_eq_norm]
    calc ‖w - x‖ = ‖(w - z) + (z - x)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖w - z‖ + ‖z - x‖ := norm_add_le _ _
      _ < (R - r) + r := by linarith
      _ = R := by ring
  -- `y → w ← z → x`.
  refine ConnWithin.trans (ConnWithin.of_edge hyb hwb ?_)
    (ConnWithin.trans (ConnWithin.of_edge hzb hwb ?_).symm (ConnWithin.of_edge hzb hxb ?_))
  · rw [mem_coneAt]; exact cone_subset_carrier _ hwy
  · rw [mem_coneAt, htype]; exact cone_subset_carrier _ hwc
  · rw [mem_coneAt, htype]
    have h1 : z - x ∈ (Γ y).carrier := hzV
    have h2 : x - z = -(z - x) := by abel
    rw [h2]
    exact neg_mem_doubleCone_iff.mpr h1


/-! ## Lemma 5.6: bounded jumps toward the tip -/

/-- **Lemma 5.6** of Bux–Kassmann–Schulze. There is a constant `δ > 0`, depending
only on `ϑ` and `d`, such that for every double cone of apex angle at least `ϑ`:
if some lattice point of the cone lies closer to the tip than a given lattice
point `x` of the cone, then some lattice point of the cone within `δ` of `x`
does. Equivalently, one may descend to a lattice point of minimal distance to the
tip by jumps of length at most `δ`.

The paper calls the assertion obvious. It is short but not immediate: stepping
radially inward keeps the *angle* to the cone axis unchanged, so a point near the
boundary stays near the boundary and no ball of fixed radius fits. The step used
here is radial *and* along the axis, the second part raising the distance to the
cone boundary by exactly `a sin ϑ` (`coneGap_add_smul_axis`) — enough room for a
ball of radius `√d/2`, hence for a lattice point. -/
theorem exists_closer_lattice_nearby {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ V : DCone (EuclideanSpace ℝ (Fin d)), ϑ ≤ V.apex →
      ∀ x ∈ lattice d, x ∈ V.carrier →
        (∃ z ∈ lattice d, z ∈ V.carrier ∧ ‖z‖ < ‖x‖) →
        ∃ y ∈ lattice d, y ∈ V.carrier ∧ ‖y‖ < ‖x‖ ∧ ‖y - x‖ < δ := by
  have hs0 : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [pi_pos])
  have hρ0 : (0:ℝ) ≤ Real.sqrt d / 2 := by positivity
  have ha₀0 : 0 < (Real.sqrt d / 2 + 1) / Real.sin ϑ := div_pos (by linarith) hs0
  refine ⟨2 * ((Real.sqrt d / 2 + 1) / Real.sin ϑ + Real.sqrt d / 2 + 1)
    + (Real.sqrt d / 2 + 1) / Real.sin ϑ + Real.sqrt d / 2 + 1, by linarith, ?_⟩
  rintro V hV x hxlat hxV ⟨z, hzlat, hzV, hzx⟩
  set ρ : ℝ := Real.sqrt d / 2 with hρdef
  set a₀ : ℝ := (ρ + 1) / Real.sin ϑ with ha₀def
  set t₀ : ℝ := a₀ + ρ + 1 with ht₀def
  have ht₀0 : 0 < t₀ := by rw [ht₀def]; linarith
  have hxne : x ≠ 0 := ne_zero_of_mem_doubleCone hxV
  have hR0 : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  have hxn : ‖x‖ ≠ 0 := ne_of_gt hR0
  by_cases hcase : ‖x‖ ≤ t₀
  · refine ⟨z, hzlat, hzV, hzx, ?_⟩
    calc ‖z - x‖ ≤ ‖z‖ + ‖x‖ := norm_sub_le _ _
      _ < 2 * t₀ := by linarith
      _ < 2 * t₀ + a₀ + ρ + 1 := by linarith
  · rw [not_le] at hcase
    -- The half-cone containing `x`.
    obtain ⟨v, hv1, hvsub, hxc⟩ : ∃ v : EuclideanSpace ℝ (Fin d), ‖v‖ = 1 ∧
        cone v V.apex ⊆ V.carrier ∧ x ∈ cone v V.apex := by
      rcases mem_doubleCone_iff.mp hxV with h | h
      · exact ⟨V.axis, V.norm_axis, Set.subset_union_left, h⟩
      · refine ⟨-V.axis, by simp [V.norm_axis], ?_, ?_⟩
        · rw [cone_neg]; exact Set.subset_union_right
        · rw [cone_neg]; exact h
    have hap0 : 0 < V.apex := V.apex_pos
    have hap' : V.apex ≤ π / 2 := V.apex_le
    have hsV : Real.sin ϑ ≤ Real.sin V.apex :=
      Real.strictMonoOn_sin.monotoneOn ⟨by linarith [pi_pos], by linarith⟩
        ⟨by linarith [pi_pos, hap0], hap'⟩ hV
    have hsV0 : 0 < Real.sin V.apex := lt_of_lt_of_le hs0 hsV
    set a : ℝ := (ρ + 1) / Real.sin V.apex with hadef
    have ha0 : 0 < a := div_pos (by linarith) hsV0
    have haa₀ : a ≤ a₀ := by
      rw [hadef, ha₀def]
      apply div_le_div_of_nonneg_left (by linarith) hs0 hsV
    set t : ℝ := a + ρ + 1 with htdef
    have ht0 : 0 < t := by rw [htdef]; linarith
    have htt₀ : t ≤ t₀ := by rw [htdef, ht₀def]; linarith
    have htR : t < ‖x‖ := lt_of_le_of_lt htt₀ hcase
    -- Step radially inward by `t`, then along the axis by `a`.
    obtain ⟨lam, hlamdef⟩ : ∃ l : ℝ, l = 1 - t / ‖x‖ := ⟨_, rfl⟩
    have hlam0 : 0 < lam := by rw [hlamdef, sub_pos, div_lt_one hR0]; exact htR
    obtain ⟨p, hpdef⟩ : ∃ q : EuclideanSpace ℝ (Fin d), q = lam • x + a • v := ⟨_, rfl⟩
    have hnx' : ‖lam • x‖ = ‖x‖ - t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam0, hlamdef]
      field_simp
    have hdx' : ‖lam • x - x‖ = t := by
      have hcoef : lam - 1 = -(t / ‖x‖) := by rw [hlamdef]; ring
      have he : lam • x - x = (lam - 1) • x := by rw [sub_smul, one_smul]
      rw [he, hcoef, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (div_pos ht0 hR0)]
      field_simp
    have hav : ‖a • v‖ = a := by
      rw [norm_smul, hv1, Real.norm_eq_abs, abs_of_pos ha0, mul_one]
    -- The gap at `p` leaves room for a lattice point.
    have hgapx : 0 < coneGap v V.apex x := (mem_cone_iff_coneGap_pos hv1 hap0 hap' x).mp hxc
    have hgapx' : 0 ≤ coneGap v V.apex (lam • x) := by
      rw [coneGap_smul v V.apex hlam0.le x]
      positivity
    have hgapp : coneGap v V.apex p = coneGap v V.apex (lam • x) + (ρ + 1) := by
      rw [hpdef, coneGap_add_smul_axis hv1, hadef]
      field_simp
    have hgapρ : ρ < coneGap v V.apex p := by rw [hgapp]; linarith
    obtain ⟨y, hylat, hyp⟩ := exists_lattice_mem_closedBall p
    rw [← hρdef] at hyp
    have hyc : y ∈ cone v V.apex := by
      refine closedBall_subset_cone hv1 hap0 hap' hgapρ ?_
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact hyp
    have hpnorm : ‖p‖ ≤ (‖x‖ - t) + a := by
      calc ‖p‖ ≤ ‖lam • x‖ + ‖a • v‖ := by rw [hpdef]; exact norm_add_le _ _
        _ = (‖x‖ - t) + a := by rw [hnx', hav]
    have hpx : ‖p - x‖ ≤ t + a := by
      calc ‖p - x‖ = ‖(lam • x - x) + a • v‖ := by rw [hpdef]; congr 1; abel
        _ ≤ ‖lam • x - x‖ + ‖a • v‖ := norm_add_le _ _
        _ = t + a := by rw [hdx', hav]
    refine ⟨y, hylat, hvsub hyc, ?_, ?_⟩
    · calc ‖y‖ = ‖(y - p) + p‖ := by congr 1; abel
        _ ≤ ‖y - p‖ + ‖p‖ := norm_add_le _ _
        _ ≤ ρ + ((‖x‖ - t) + a) := by linarith
        _ < ‖x‖ := by rw [htdef]; linarith
    · calc ‖y - x‖ = ‖(y - p) + (p - x)‖ := by congr 1; abel
        _ ≤ ‖y - p‖ + ‖p - x‖ := norm_add_le _ _
        _ ≤ ρ + (t + a) := by linarith
        _ < 2 * t₀ + a₀ + ρ + 1 := by linarith


/-! ## Descent by bounded jumps

Lemma 5.6 continues: "I.e., we can go from `x` within `V` to a lattice point of
minimum distance to the tip via a chain of jumps each bounded in length from
above by `δ`." That clause is a general consequence of the local statement, and
is what the induction of Lemma 5.7 consumes; we record it separately.

The descent terminates because squared distances between lattice points are
natural numbers. -/

lemma lattice_sub {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ lattice d)
    (hy : y ∈ lattice d) : x - y ∈ lattice d := by
  rw [mem_lattice_iff] at hx hy ⊢
  intro i
  obtain ⟨n, hn⟩ := hx i
  obtain ⟨m, hm⟩ := hy i
  refine ⟨n - m, ?_⟩
  have he : (x - y) i = x i - y i := by simp
  rw [he, hn, hm]
  push_cast
  ring

lemma zero_mem_lattice : (0 : EuclideanSpace ℝ (Fin d)) ∈ lattice d := by
  rw [mem_lattice_iff]
  exact fun i => ⟨0, by simp⟩

/-- The squared norm of a lattice point is a natural number. -/
lemma exists_natCast_sq_norm {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ lattice d) :
    ∃ n : ℕ, ‖x‖ ^ 2 = (n : ℝ) := by
  rw [mem_lattice_iff] at hx
  choose m hm using hx
  have hsq : ‖x‖ ^ 2 = ∑ i, ((m i : ℤ) : ℝ) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hm i, Real.norm_eq_abs, sq_abs]
  have hnn : (0 : ℤ) ≤ ∑ i, (m i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  refine ⟨(∑ i, (m i) ^ 2).toNat, ?_⟩
  rw [hsq]
  have hcast : (((∑ i, (m i) ^ 2).toNat : ℕ) : ℝ) = ((∑ i, (m i) ^ 2 : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hnn)
  rw [hcast]
  push_cast
  ring

/-- A single jump of the descent: within `W`, strictly closer to `c`, of length
less than `δ`. -/
def Jump (W : Set (EuclideanSpace ℝ (Fin d))) (c : EuclideanSpace ℝ (Fin d)) (δ : ℝ) :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → Prop :=
  fun p q => p ∈ W ∩ lattice d ∧ q ∈ W ∩ lattice d ∧ ‖q - c‖ < ‖p - c‖ ∧ ‖q - p‖ < δ

/-- **The descent principle.** If from every non-minimal lattice point of `W`
there is a jump of length less than `δ` strictly closer to `c`, then every
lattice point of `W` reaches a lattice point of `W` at minimal distance to `c`
through such jumps. -/
theorem exists_min_of_jump {W : Set (EuclideanSpace ℝ (Fin d))}
    {c : EuclideanSpace ℝ (Fin d)} (hc : c ∈ lattice d) {δ : ℝ}
    (hstep : ∀ p ∈ W ∩ lattice d,
      (∃ q ∈ W ∩ lattice d, ‖q - c‖ < ‖p - c‖) →
      ∃ q ∈ W ∩ lattice d, ‖q - c‖ < ‖p - c‖ ∧ ‖q - p‖ < δ) :
    ∀ x ∈ W ∩ lattice d, ∃ m ∈ W ∩ lattice d,
      (∀ w ∈ W ∩ lattice d, ‖m - c‖ ≤ ‖w - c‖) ∧
      Relation.ReflTransGen (Jump W c δ) x m := by
  -- Induct on the natural number `‖x − c‖²`.
  have key : ∀ n : ℕ, ∀ x ∈ W ∩ lattice d, ‖x - c‖ ^ 2 = (n : ℝ) →
      ∃ m ∈ W ∩ lattice d, (∀ w ∈ W ∩ lattice d, ‖m - c‖ ≤ ‖w - c‖) ∧
        Relation.ReflTransGen (Jump W c δ) x m := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hx hxn
      by_cases hmin : ∀ w ∈ W ∩ lattice d, ‖x - c‖ ≤ ‖w - c‖
      · exact ⟨x, hx, hmin, Relation.ReflTransGen.refl⟩
      · have hex : ∃ q ∈ W ∩ lattice d, ‖q - c‖ < ‖x - c‖ := by
          by_contra hcon
          refine hmin (fun w hw => ?_)
          by_contra hlt
          exact hcon ⟨w, hw, by linarith [not_le.mp hlt]⟩
        obtain ⟨q, hq, hqc, hqx⟩ := hstep x hx hex
        obtain ⟨k, hk⟩ := exists_natCast_sq_norm (lattice_sub hq.2 hc)
        have hkn : k < n := by
          have h1 : (k : ℝ) < (n : ℝ) := by
            rw [← hk, ← hxn]
            have h0 : 0 ≤ ‖q - c‖ := norm_nonneg _
            nlinarith
          exact_mod_cast h1
        obtain ⟨m, hm, hmmin, hchain⟩ := ih k hkn q hq hk
        exact ⟨m, hm, hmmin, Relation.ReflTransGen.head ⟨hx, hq, hqc, hqx⟩ hchain⟩
  intro x hx
  obtain ⟨n, hn⟩ := exists_natCast_sq_norm (lattice_sub hx.2 hc)
  exact key n x hx hn


/-- **Lemma 5.6, in full**, including the clause the paper states with "I.e.":
within a double cone of apex angle at least `ϑ`, every lattice point reaches a
lattice point of minimal distance to the tip through a chain of jumps each of
length less than `δ`, with `δ` depending only on `ϑ` and `d`. -/
theorem exists_min_chain_in_cone {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ V : DCone (EuclideanSpace ℝ (Fin d)), ϑ ≤ V.apex →
      ∀ x ∈ V.carrier ∩ lattice d,
        ∃ m ∈ V.carrier ∩ lattice d,
          (∀ w ∈ V.carrier ∩ lattice d, ‖m‖ ≤ ‖w‖) ∧
          Relation.ReflTransGen (Jump V.carrier 0 δ) x m := by
  obtain ⟨δ, hδ0, hδ⟩ := exists_closer_lattice_nearby (d := d) hϑ hϑ'
  refine ⟨δ, hδ0, fun V hV x hx => ?_⟩
  have hstep : ∀ p ∈ V.carrier ∩ lattice d,
      (∃ q ∈ V.carrier ∩ lattice d, ‖q - 0‖ < ‖p - 0‖) →
      ∃ q ∈ V.carrier ∩ lattice d, ‖q - 0‖ < ‖p - 0‖ ∧ ‖q - p‖ < δ := by
    rintro p ⟨hpV, hplat⟩ ⟨q, ⟨hqV, hqlat⟩, hqp⟩
    rw [sub_zero, sub_zero] at hqp
    obtain ⟨y, hylat, hyV, hyn, hyd⟩ := hδ V hV p hplat hpV ⟨q, hqlat, hqV, hqp⟩
    exact ⟨y, ⟨hyV, hylat⟩, by rw [sub_zero, sub_zero]; exact hyn, hyd⟩
  obtain ⟨m, hm, hmin, hchain⟩ :=
    exists_min_of_jump (W := V.carrier) (c := 0) (δ := δ) zero_mem_lattice hstep x hx
  exact ⟨m, hm, fun w hw => by simpa [sub_zero] using hmin w hw, hchain⟩


/-! ## Lemma 5.7: the core induction

Lemma 5.7 asserts the existence of constants `r_k ≤ ρ_k ≤ R_k`, depending only on
`ϑ` and `d`, with `δ < r_1`, such that every lattice point `x` is
`r_k`-`R_k`-connected as soon as at most `k` cone types are realised at the
lattice points of `B_{ρ_k}(x)`.

The statement is recorded below as `CoreInduction` and proved, in the stronger
form in which the constants are produced before the configuration is mentioned —
the paper's assertion that they depend only on `ϑ` and `d`. See `core_induction`
and `coreInduction_holds`; `core_induction_base` is the base case `k = 1` on its
own. -/

/-- The set of cone types realised at the lattice points of `S`. A "type" is the
double cone itself, as in Definition 4.2. -/
def typesIn (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (S : Set (EuclideanSpace ℝ (Fin d))) : Set (Set (EuclideanSpace ℝ (Fin d))) :=
  (fun p => (Γ p).carrier) '' (S ∩ lattice d)

/-- The statement of **Lemma 5.7**, for a fixed configuration. Proved as
`coreInduction_holds`; `core_induction` is the stronger form with the
configuration quantified after the constants. -/
def CoreInduction (Γ : Configuration (EuclideanSpace ℝ (Fin d))) (δ : ℝ) : Prop :=
  ∀ k : ℕ, ∃ r ρ R : ℝ, δ < r ∧ r ≤ ρ ∧ ρ ≤ R ∧
    ∀ x ∈ lattice d, Set.encard (typesIn Γ (ball x ρ)) ≤ (k : ℕ∞) →
      RRConnected Γ r R x

/-- **Lemma 5.7, the base case `k = 1`**, on its own: if only one cone type is
realised at the lattice points of `B_ρ(x)`, then `x` is `r`-`R`-connected, by
Corollary 5.2 applied to `x` and each lattice point of `B_r(x)`. (The full
induction, `core_induction`, starts instead from the vacuous case `k = 0`.) -/
theorem core_induction_base (hϑ : 0 < ϑ) (hb : ∀ z, ϑ ≤ (Γ z).apex) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r ρ R : ℝ, δ < r ∧ r ≤ ρ ∧ ρ ≤ R ∧
      ∀ x ∈ lattice d, Set.encard (typesIn Γ (ball x ρ)) ≤ 1 → RRConnected Γ r R x := by
  have hs0 : 0 < Real.sin ϑ :=
    Real.sin_pos_of_pos_of_lt_pi hϑ (by
      have := (Γ 0).apex_le
      have := hb 0
      linarith [pi_pos])
  have hdnn : (0:ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  refine ⟨δ + 1, δ + 1, (δ + 1 + Real.sqrt d) / Real.sin ϑ + (δ + 1) + 1,
    by linarith, le_rfl, ?_, ?_⟩
  · have : 0 < (δ + 1 + Real.sqrt d) / Real.sin ϑ := div_pos (by linarith) hs0
    linarith
  · intro x hx hcard y hy hylat
    rw [mem_ball, dist_eq_norm] at hy
    -- `x` and `y` are lattice points of `B_ρ(x)`, so they have the same type.
    have hxb : x ∈ ball x (δ + 1) ∩ lattice d := ⟨mem_ball_self (by linarith), hx⟩
    have hyb : y ∈ ball x (δ + 1) ∩ lattice d := by
      refine ⟨?_, hylat⟩
      rw [mem_ball, dist_eq_norm]
      exact hy
    have htx : (Γ x).carrier ∈ typesIn Γ (ball x (δ + 1)) := ⟨x, hxb, rfl⟩
    have hty : (Γ y).carrier ∈ typesIn Γ (ball x (δ + 1)) := ⟨y, hyb, rfl⟩
    have htype : (Γ x).carrier = (Γ y).carrier :=
      Set.encard_le_one_iff.mp hcard _ _ htx hty
    exact discr_connect_two_of_same_type hϑ hb hx hylat htype
      (by rw [norm_sub_rev]; exact hy) (by linarith)


/-! ## Lemma 5.6 for a shrunk half-cone

The induction of Lemma 5.7 descends inside `x̂ + Ṽ_ρ`, a *shrunk* double half-cone
rather than a cone with apex at the origin. By `coneGap_gt_eq_shift_cone` such a
set contains the half-cone with the same axis and angle whose apex has been moved
`ρ / sin ϑ` along the axis, so what is needed is Lemma 5.6 for a half-cone with an
arbitrary apex. The constants below still depend only on `ϑ` and `d`, and in
particular not on the apex or on `ρ`.

The construction turns out not to need the hypothesis that a closer lattice point
exists: outside a ball of radius `t₀` about the apex one can *always* step at
least `1` closer. That unconditional form is what makes the descent terminate,
without any appeal to finiteness of the lattice in a bounded region. -/

/-- **The descent step for a half-cone with arbitrary apex.** Outside the ball of
radius `t₀` about the apex `c`, every lattice point of the half-cone has a
lattice point of the half-cone at least `1` closer to `c`, within distance `δ`.
Both constants depend only on `ϑ` and `d`. -/
theorem exists_lattice_step_toward_apex {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) :
    ∃ δ t₀ : ℝ, 0 < δ ∧ 0 < t₀ ∧
      ∀ (v : EuclideanSpace ℝ (Fin d)) (ϑV : ℝ), ‖v‖ = 1 → ϑ ≤ ϑV → ϑV ≤ π / 2 →
      ∀ c : EuclideanSpace ℝ (Fin d), ∀ x ∈ lattice d, x ∈ shift (cone v ϑV) c →
        t₀ < ‖x - c‖ →
        ∃ y ∈ lattice d, y ∈ shift (cone v ϑV) c ∧ ‖y - c‖ ≤ ‖x - c‖ - 1 ∧
          ‖y - x‖ < δ := by
  have hs0 : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [pi_pos])
  have hqnn : (0:ℝ) ≤ Real.sqrt d / 2 := by positivity
  have hb₀0 : 0 < (Real.sqrt d / 2 + 1) / Real.sin ϑ := div_pos (by linarith) hs0
  refine ⟨Real.sqrt d / 2 + ((Real.sqrt d / 2 + 1) / Real.sin ϑ + Real.sqrt d / 2 + 1)
      + (Real.sqrt d / 2 + 1) / Real.sin ϑ + 1,
    (Real.sqrt d / 2 + 1) / Real.sin ϑ + Real.sqrt d / 2 + 1, by linarith, by linarith, ?_⟩
  intro v ϑV hv hϑV hϑV' c x hxlat hxc hbig
  set q : ℝ := Real.sqrt d / 2 with hqdef
  set b₀ : ℝ := (q + 1) / Real.sin ϑ with hb₀def
  set t₀ : ℝ := b₀ + q + 1 with ht₀def
  have ht₀0 : 0 < t₀ := by rw [ht₀def]; linarith
  have hϑV0 : 0 < ϑV := lt_of_lt_of_le hϑ hϑV
  have hsV : Real.sin ϑ ≤ Real.sin ϑV :=
    Real.strictMonoOn_sin.monotoneOn ⟨by linarith [pi_pos], by linarith⟩
      ⟨by linarith [pi_pos], hϑV'⟩ hϑV
  have hsV0 : 0 < Real.sin ϑV := lt_of_lt_of_le hs0 hsV
  have hgapx : 0 < coneGap v ϑV (x - c) := (mem_cone_iff_coneGap_pos hv hϑV0 hϑV' _).mp hxc
  have hR0 : 0 < ‖x - c‖ := lt_trans ht₀0 hbig
  have hxn : ‖x - c‖ ≠ 0 := ne_of_gt hR0
  set b : ℝ := (q + 1) / Real.sin ϑV with hbdef
  have hb0 : 0 < b := div_pos (by linarith) hsV0
  have hbb₀ : b ≤ b₀ := by
    rw [hbdef, hb₀def]
    exact div_le_div_of_nonneg_left (by linarith) hs0 hsV
  set t : ℝ := b + q + 1 with htdef
  have ht0 : 0 < t := by rw [htdef]; linarith
  have htt₀ : t ≤ t₀ := by rw [htdef, ht₀def]; linarith
  have htR : t < ‖x - c‖ := lt_of_le_of_lt htt₀ hbig
  obtain ⟨lam, hlamdef⟩ : ∃ l : ℝ, l = 1 - t / ‖x - c‖ := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlamdef, sub_pos, div_lt_one hR0]; exact htR
  obtain ⟨p, hpdef⟩ : ∃ w : EuclideanSpace ℝ (Fin d),
      w = c + (lam • (x - c) + b • v) := ⟨_, rfl⟩
  have hpc : p - c = lam • (x - c) + b • v := by rw [hpdef]; abel
  have hnu : ‖lam • (x - c)‖ = ‖x - c‖ - t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam0, hlamdef]
    field_simp
  have hdu : ‖lam • (x - c) - (x - c)‖ = t := by
    have hcoef : lam - 1 = -(t / ‖x - c‖) := by rw [hlamdef]; ring
    have he : lam • (x - c) - (x - c) = (lam - 1) • (x - c) := by rw [sub_smul, one_smul]
    rw [he, hcoef, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (div_pos ht0 hR0)]
    field_simp
  have hbv : ‖b • v‖ = b := by
    rw [norm_smul, hv, Real.norm_eq_abs, abs_of_pos hb0, mul_one]
  have hgap1 : 0 ≤ coneGap v ϑV (lam • (x - c)) := by
    rw [coneGap_smul v ϑV hlam0.le]
    positivity
  have hgapp : coneGap v ϑV (p - c) = coneGap v ϑV (lam • (x - c)) + (q + 1) := by
    rw [hpc, coneGap_add_smul_axis hv, hbdef]
    field_simp
  obtain ⟨y, hylat, hyp⟩ := exists_lattice_mem_closedBall p
  rw [← hqdef] at hyp
  have hgapy : 0 < coneGap v ϑV (y - c) := by
    have hlip := coneGap_sub_le hv hϑV0 hϑV' (p - c) (y - c)
    have he : ‖p - c - (y - c)‖ = ‖y - p‖ := by
      rw [show p - c - (y - c) = -(y - p) by abel, norm_neg]
    rw [he] at hlip
    linarith
  have hyc : y ∈ shift (cone v ϑV) c := (mem_cone_iff_coneGap_pos hv hϑV0 hϑV' _).mpr hgapy
  have hpnorm : ‖p - c‖ ≤ (‖x - c‖ - t) + b := by
    calc ‖p - c‖ = ‖lam • (x - c) + b • v‖ := by rw [hpc]
      _ ≤ ‖lam • (x - c)‖ + ‖b • v‖ := norm_add_le _ _
      _ = (‖x - c‖ - t) + b := by rw [hnu, hbv]
  have hpx : ‖p - x‖ ≤ t + b := by
    calc ‖p - x‖ = ‖(lam • (x - c) - (x - c)) + b • v‖ := by rw [hpdef]; congr 1; abel
      _ ≤ ‖lam • (x - c) - (x - c)‖ + ‖b • v‖ := norm_add_le _ _
      _ = t + b := by rw [hdu, hbv]
  refine ⟨y, hylat, hyc, ?_, ?_⟩
  · calc ‖y - c‖ = ‖(y - p) + (p - c)‖ := by congr 1; abel
      _ ≤ ‖y - p‖ + ‖p - c‖ := norm_add_le _ _
      _ ≤ q + ((‖x - c‖ - t) + b) := by linarith
      _ = ‖x - c‖ - 1 := by rw [htdef]; ring
  · calc ‖y - x‖ = ‖(y - p) + (p - x)‖ := by congr 1; abel
      _ ≤ ‖y - p‖ + ‖p - x‖ := norm_add_le _ _
      _ ≤ q + (t + b) := by linarith
      _ < q + t₀ + b₀ + 1 := by linarith

/-- **Lemma 5.6 for a half-cone with an arbitrary apex `c`**, in the same shape
as `exists_closer_lattice_nearby`: near the apex use the given closer point, far
from it use the descent step. -/
theorem exists_closer_lattice_nearby_shift {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (v : EuclideanSpace ℝ (Fin d)) (ϑV : ℝ), ‖v‖ = 1 → ϑ ≤ ϑV → ϑV ≤ π / 2 →
      ∀ c : EuclideanSpace ℝ (Fin d), ∀ x ∈ lattice d, x ∈ shift (cone v ϑV) c →
        (∃ z ∈ lattice d, z ∈ shift (cone v ϑV) c ∧ ‖z - c‖ < ‖x - c‖) →
        ∃ y ∈ lattice d, y ∈ shift (cone v ϑV) c ∧ ‖y - c‖ < ‖x - c‖ ∧ ‖y - x‖ < δ := by
  obtain ⟨δ, t₀, hδ0, ht₀0, hstep⟩ := exists_lattice_step_toward_apex (d := d) hϑ hϑ'
  refine ⟨2 * t₀ + δ, by linarith, ?_⟩
  rintro v ϑV hv hϑV hϑV' c x hxlat hxc ⟨z, hzlat, hzc, hzx⟩
  by_cases hcase : ‖x - c‖ ≤ t₀
  · refine ⟨z, hzlat, hzc, hzx, ?_⟩
    calc ‖z - x‖ = ‖(z - c) - (x - c)‖ := by congr 1; abel
      _ ≤ ‖z - c‖ + ‖x - c‖ := norm_sub_le _ _
      _ < 2 * t₀ := by linarith
      _ < 2 * t₀ + δ := by linarith
  · rw [not_le] at hcase
    obtain ⟨y, hylat, hyc, hyd, hyx⟩ := hstep v ϑV hv hϑV hϑV' c x hxlat hxc hcase
    exact ⟨y, hylat, hyc, by linarith, by linarith⟩


/-- **The chain of bounded jumps for a half-cone with an arbitrary apex.** From
any lattice point of the half-cone, jumps of length less than `δ` staying in the
half-cone and strictly decreasing the distance to the apex reach a lattice point
within `t₀` of the apex — the paper's "lattice point near the tip".

The descent terminates because each step gains at least `1`, so `⌈‖x − c‖⌉₊`
strictly decreases; no finiteness of the lattice in a bounded region is needed. -/
theorem exists_chain_to_apex {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) :
    ∃ δ t₀ : ℝ, 0 < δ ∧ 0 < t₀ ∧
      ∀ (v : EuclideanSpace ℝ (Fin d)) (ϑV : ℝ), ‖v‖ = 1 → ϑ ≤ ϑV → ϑV ≤ π / 2 →
      ∀ c : EuclideanSpace ℝ (Fin d), ∀ x ∈ lattice d, x ∈ shift (cone v ϑV) c →
        ∃ y ∈ lattice d, y ∈ shift (cone v ϑV) c ∧ ‖y - c‖ ≤ t₀ ∧
          Relation.ReflTransGen (Jump (shift (cone v ϑV) c) c δ) x y := by
  obtain ⟨δ, t₀, hδ0, ht₀0, hstep⟩ := exists_lattice_step_toward_apex (d := d) hϑ hϑ'
  refine ⟨δ, t₀, hδ0, ht₀0, fun v ϑV hv h1 h2 c => ?_⟩
  have key : ∀ n : ℕ, ∀ x, x ∈ lattice d → x ∈ shift (cone v ϑV) c →
      ⌈‖x - c‖⌉₊ ≤ n →
      ∃ y ∈ lattice d, y ∈ shift (cone v ϑV) c ∧ ‖y - c‖ ≤ t₀ ∧
        Relation.ReflTransGen (Jump (shift (cone v ϑV) c) c δ) x y := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hxlat hxc hxn
      by_cases hsmall : ‖x - c‖ ≤ t₀
      · exact ⟨x, hxlat, hxc, hsmall, Relation.ReflTransGen.refl⟩
      · rw [not_le] at hsmall
        obtain ⟨y, hylat, hyc, hyd, hyx⟩ := hstep v ϑV hv h1 h2 c x hxlat hxc hsmall
        have hpos : 0 < ⌈‖x - c‖⌉₊ := Nat.ceil_pos.mpr (by linarith)
        have hceil : ⌈‖y - c‖⌉₊ < ⌈‖x - c‖⌉₊ := by
          have hle : ⌈‖y - c‖⌉₊ ≤ ⌈‖x - c‖⌉₊ - 1 := by
            rw [Nat.ceil_le]
            have hcast : ((⌈‖x - c‖⌉₊ - 1 : ℕ) : ℝ) = (⌈‖x - c‖⌉₊ : ℝ) - 1 := by
              have h1' : 1 ≤ ⌈‖x - c‖⌉₊ := hpos
              push_cast [Nat.cast_sub h1']
              ring
            rw [hcast]
            have := Nat.le_ceil ‖x - c‖
            linarith
          omega
        obtain ⟨z, hzlat, hzc, hzt, hchain⟩ :=
          ih ⌈‖y - c‖⌉₊ (lt_of_lt_of_le hceil hxn) y hylat hyc le_rfl
        refine ⟨z, hzlat, hzc, hzt, Relation.ReflTransGen.head ?_ hchain⟩
        exact ⟨⟨hxc, hxlat⟩, ⟨hyc, hylat⟩, by linarith, hyx⟩
  exact fun x hxlat hxc => key ⌈‖x - c‖⌉₊ x hxlat hxc le_rfl

/-- **The local jump statement and the descent chain for a shrunk half-cone**, in
the form Lemma 5.7 uses. The region `c + Ṽ_ρ` of the paper contains the half-cone
with apex `c + (ρ/sin ϑ_V)·v`; inside it, every lattice point reaches, by jumps of
length less than `δ`, a lattice point within `t₀` of that apex — and the whole
chain stays inside `c + Ṽ_ρ`. -/
theorem exists_chain_to_apex_shrunk {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) :
    ∃ δ t₀ : ℝ, 0 < δ ∧ 0 < t₀ ∧
      ∀ (v : EuclideanSpace ℝ (Fin d)) (ϑV : ℝ), ‖v‖ = 1 → ϑ ≤ ϑV → ϑV ≤ π / 2 →
      ∀ ρ : ℝ, 0 ≤ ρ → ∀ c : EuclideanSpace ℝ (Fin d),
        -- the displaced apex of the shrunk half-cone
        ∀ x ∈ lattice d, x ∈ shift (cone v ϑV) (c + (ρ / Real.sin ϑV) • v) →
          ∃ y ∈ lattice d,
            y ∈ shift (cone v ϑV) (c + (ρ / Real.sin ϑV) • v) ∧
            ‖y - (c + (ρ / Real.sin ϑV) • v)‖ ≤ t₀ ∧
            Relation.ReflTransGen
              (Jump (shift (cone v ϑV) (c + (ρ / Real.sin ϑV) • v))
                (c + (ρ / Real.sin ϑV) • v) δ) x y := by
  obtain ⟨δ, t₀, hδ0, ht₀0, hchain⟩ := exists_chain_to_apex (d := d) hϑ hϑ'
  exact ⟨δ, t₀, hδ0, ht₀0, fun v ϑV hv h1 h2 ρ _hρ c =>
    hchain v ϑV hv h1 h2 (c + (ρ / Real.sin ϑV) • v)⟩

/-- The half-cone used above really does sit inside the paper's `c + Ṽ_ρ`, so the
whole descent takes place in the shrunk double half-cone. -/
theorem shift_cone_apex_subset_shift_shrink {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {ϑV : ℝ} (hϑV : 0 < ϑV) (hϑV' : ϑV ≤ π / 2) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (c : EuclideanSpace ℝ (Fin d)) :
    shift (cone v ϑV) (c + (ρ / Real.sin ϑV) • v) ⊆ shift (shrink (cone v ϑV) ρ) c := by
  have he : shift (cone v ϑV) (c + (ρ / Real.sin ϑV) • v)
      = shift (shift (cone v ϑV) ((ρ / Real.sin ϑV) • v)) c := by
    rw [shift_shift]
    congr 1
    abel
  rw [he]
  exact shift_mono (shift_cone_subset_shrink hv hϑV hϑV' hρ) c


/-! ## Type counting

Item 1 of the induction step of Lemma 5.7: if a cone type `V` is realised
somewhere in `T` but nowhere in a subset `S`, then `S` realises strictly fewer
types than `T`. -/

lemma mem_typesIn {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {S : Set (EuclideanSpace ℝ (Fin d))} {p : EuclideanSpace ℝ (Fin d)} (hp : p ∈ S)
    (hlat : p ∈ lattice d) : (Γ p).carrier ∈ typesIn Γ S := ⟨p, ⟨hp, hlat⟩, rfl⟩

lemma typesIn_mono {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {S T : Set (EuclideanSpace ℝ (Fin d))} (h : S ⊆ T) : typesIn Γ S ⊆ typesIn Γ T :=
  Set.image_mono (Set.inter_subset_inter h Set.Subset.rfl)

/-- Dropping a witnessed element from an ambient set of at most `k+1` elements
leaves at most `k`. -/
lemma encard_le_of_subset_diff {α : Type*} {A B : Set α} {v : α} {k : ℕ}
    (hAB : A ⊆ B \ {v}) (hv : v ∈ B) (hB : B.encard ≤ ((k + 1 : ℕ) : ℕ∞)) :
    A.encard ≤ (k : ℕ∞) := by
  have h1 : (B \ {v}).encard + 1 = B.encard := Set.encard_sdiff_singleton_add_one hv
  have h2 : A.encard ≤ (B \ {v}).encard := Set.encard_mono hAB
  have h3 : (B \ {v}).encard + 1 ≤ (k : ℕ∞) + 1 := by
    rw [h1]
    refine hB.trans ?_
    push_cast
    exact le_rfl
  exact h2.trans ((WithTop.add_le_add_iff_right WithTop.one_ne_top).mp h3)

/-- **Type counting for the induction step of Lemma 5.7.** If at most `k+1` cone
types are realised at the lattice points of `T`, the type of `y ∈ T` is realised
in `T`, and no lattice point of `S ⊆ T` has that type, then at most `k` types are
realised at the lattice points of `S`. -/
theorem encard_typesIn_le_of_missing {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {S T : Set (EuclideanSpace ℝ (Fin d))} (hST : S ⊆ T)
    {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ T) (hylat : y ∈ lattice d)
    (hmiss : ∀ p ∈ S, p ∈ lattice d → (Γ p).carrier ≠ (Γ y).carrier)
    {k : ℕ} (hT : (typesIn Γ T).encard ≤ ((k + 1 : ℕ) : ℕ∞)) :
    (typesIn Γ S).encard ≤ (k : ℕ∞) := by
  refine encard_le_of_subset_diff ?_ (mem_typesIn hy hylat) hT
  rintro t ⟨p, ⟨hpS, hplat⟩, rfl⟩
  exact ⟨typesIn_mono hST (mem_typesIn hpS hplat), fun h => hmiss p hpS hplat h⟩

/-! ## Path assembly

Item 3 of the induction step: the paths produced by the inductive hypothesis live
in balls `B_{R'}(p)` around various lattice points `p`, and have to be pushed into
one big ball. -/

variable {Γ : Configuration (EuclideanSpace ℝ (Fin d))}

/-- Push a path from a small ball into a larger one. -/
lemma ConnWithin.mono_ball {p b : EuclideanSpace ℝ (Fin d)} {r R : ℝ}
    (h : r + dist p b ≤ R) {u w : EuclideanSpace ℝ (Fin d)}
    (huw : ConnWithin Γ (ball p r ∩ lattice d) u w) :
    ConnWithin Γ (ball b R ∩ lattice d) u w :=
  ConnWithin.mono (Set.inter_subset_inter (Metric.ball_subset_ball' h) Set.Subset.rfl) huw

/-- An `r`-`R`-connected point joins any two lattice points of its `r`-ball. -/
lemma RRConnected.conn {r R : ℝ} {c : EuclideanSpace ℝ (Fin d)} (h : RRConnected Γ r R c)
    {p q : EuclideanSpace ℝ (Fin d)} (hp : p ∈ ball c r) (hplat : p ∈ lattice d)
    (hq : q ∈ ball c r) (hqlat : q ∈ lattice d) :
    ConnWithin Γ (ball c R ∩ lattice d) p q :=
  (h p hp hplat).symm.trans (h q hq hqlat)

/-- A descent chain never moves further from the base point than it started, so
it stays inside the region on which the inductive hypothesis was invoked. -/
lemma Jump.chain_dist_le {W : Set (EuclideanSpace ℝ (Fin d))}
    {c : EuclideanSpace ℝ (Fin d)} {δ : ℝ} {x y : EuclideanSpace ℝ (Fin d)}
    (h : Relation.ReflTransGen (Jump W c δ) x y) : ‖y - c‖ ≤ ‖x - c‖ := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact le_trans hstep.2.2.1.le ih

/-- Every point of a descent chain lies in `W`. -/
lemma Jump.chain_mem {W : Set (EuclideanSpace ℝ (Fin d))}
    {c : EuclideanSpace ℝ (Fin d)} {δ : ℝ} {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ W ∩ lattice d) (h : Relation.ReflTransGen (Jump W c δ) x y) :
    y ∈ W ∩ lattice d := by
  induction h with
  | refl => exact hx
  | tail _ hstep _ => exact hstep.2.1

/-- **The paper's "all these well-connected balls overlap".** A descent chain
whose jumps are shorter than `r` becomes an edge path, as soon as every lattice
point of the region *reachable from `x`* is `r`-`R`-connected; the path is
delivered inside any ball `B_{Rb}(b)` containing the corresponding balls `B_R(p)`.

The hypotheses are guarded by `‖p − c‖ ≤ ‖x − c‖`, which by `Jump.chain_dist_le`
holds along the chain: the region `W` is an unbounded cone, so the unguarded form
would be far too strong to apply. -/
theorem connWithin_of_chain {W : Set (EuclideanSpace ℝ (Fin d))}
    {c b : EuclideanSpace ℝ (Fin d)} {δ r R Rb : ℝ} (hδr : δ ≤ r)
    {x y : EuclideanSpace ℝ (Fin d)}
    (hconn : ∀ p ∈ W ∩ lattice d, ‖p - c‖ ≤ ‖x - c‖ → RRConnected Γ r R p)
    (hsub : ∀ p ∈ W ∩ lattice d, ‖p - c‖ ≤ ‖x - c‖ → R + dist p b ≤ Rb)
    (hchain : Relation.ReflTransGen (Jump W c δ) x y) :
    ConnWithin Γ (ball b Rb ∩ lattice d) x y := by
  induction hchain with
  | refl => exact ConnWithin.refl _
  | tail hpre hstep ih =>
      obtain ⟨hp, hq, -, hlen⟩ := hstep
      have hpd := Jump.chain_dist_le hpre
      refine ih.trans (ConnWithin.mono_ball (hsub _ hp hpd) ?_)
      refine (hconn _ hp hpd) _ ?_ hq.2
      rw [mem_ball, dist_eq_norm]
      exact lt_of_lt_of_le hlen hδr


/-! ## The induction step of Lemma 5.7 -/

/-- **The induction step of Lemma 5.7.** Given constants for `k` cone types,
produce constants for `k+1`.

Following the paper: pick an `s`-`S`-connected lattice point `x̂` near `x`
(Lemma 5.4) and set `r = S`; for `y ∈ B_r(x)` of type `V`, produce a lattice
point `z` in `B_ŝ(x̂) ∩ (x̂ + Ṽ_{ρ'}) ∩ V[y]` (Lemma 5.1(2), applied at the
*displaced* apex so that `z` lands in the shrunk cone), and split on whether the
type `V` occurs in `B_{ŝ₂}(x̂) ∩ V[x̂]`. If it does not, the region realises at most
`k` types, the inductive hypothesis makes every lattice point of it
`r'`-`R'`-connected, and the descent chain from `z` to the tip glues these
together and up to `x̂`. If it does, Lemma 5.5 applies directly. -/
theorem core_induction_step (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    {δ t₀ : ℝ} (hδ0 : 0 < δ) (ht₀0 : 0 < t₀)
    (hchain : ∀ (v : EuclideanSpace ℝ (Fin d)) (ϑV : ℝ), ‖v‖ = 1 → ϑ ≤ ϑV → ϑV ≤ π / 2 →
      ∀ c : EuclideanSpace ℝ (Fin d), ∀ x ∈ lattice d, x ∈ shift (cone v ϑV) c →
        ∃ y ∈ lattice d, y ∈ shift (cone v ϑV) c ∧ ‖y - c‖ ≤ t₀ ∧
          Relation.ReflTransGen (Jump (shift (cone v ϑV) c) c δ) x y)
    {k : ℕ} {r' ρ' R' : ℝ} (hδr' : δ < r') (hkr' : (k : ℝ) ≤ r')
    (hrρ' : r' ≤ ρ') (hρR' : ρ' ≤ R')
    (IH : ∀ G : Configuration (EuclideanSpace ℝ (Fin d)), (∀ z, ϑ ≤ (G z).apex) →
      ∀ p ∈ lattice d, (typesIn G (ball p ρ')).encard ≤ (k : ℕ∞) →
        RRConnected G r' R' p) :
    ∃ r ρ R : ℝ, δ < r ∧ ((k + 1 : ℕ) : ℝ) ≤ r ∧ r ≤ ρ ∧ ρ ≤ R ∧
      ∀ G : Configuration (EuclideanSpace ℝ (Fin d)), (∀ z, ϑ ≤ (G z).apex) →
      ∀ x ∈ lattice d, (typesIn G (ball x ρ)).encard ≤ ((k + 1 : ℕ) : ℕ∞) →
        RRConnected G r R x := by
  have hσ0 : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [pi_pos])
  have hσ1 : Real.sin ϑ ≤ 1 := Real.sin_le_one ϑ
  have hD : (0:ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hρ'0 : 0 < ρ' := lt_of_lt_of_le (lt_trans hδ0 hδr') hrρ'
  have hR'0 : 0 < R' := lt_of_lt_of_le hρ'0 hρR'
  have hdivρ : ρ' ≤ ρ' / Real.sin ϑ := by rw [le_div_iff₀ hσ0]; nlinarith
  have hdivρ0 : 0 < ρ' / Real.sin ϑ := div_pos hρ'0 hσ0
  obtain ⟨s, hs⟩ : ∃ t : ℝ, t = ρ' / Real.sin ϑ + t₀ + 1 := ⟨_, rfl⟩
  have hs0' : 0 < s := by linarith
  have hdivS : Real.sqrt d + s ≤ (Real.sqrt d + s) / Real.sin ϑ := by
    rw [le_div_iff₀ hσ0]; nlinarith
  obtain ⟨S, hS⟩ : ∃ t : ℝ, t = (Real.sqrt d + s) / Real.sin ϑ + 1 := ⟨_, rfl⟩
  have hS0 : 0 < S := by linarith
  have hSs : s < S := by linarith
  obtain ⟨m, hm⟩ : ∃ t : ℝ, t = ρ' / Real.sin ϑ + 2 * S := ⟨_, rfl⟩
  have hm0 : 0 < m := by linarith
  have hdivsh : 0 < (m + Real.sqrt d) / Real.sin ϑ := div_pos (by linarith) hσ0
  obtain ⟨sh, hsh⟩ : ∃ t : ℝ, t = (m + Real.sqrt d) / Real.sin ϑ + m + 1 := ⟨_, rfl⟩
  have hsh0 : 0 < sh := by linarith
  have hshm : m < sh := by linarith
  obtain ⟨s2, hs2⟩ : ∃ t : ℝ, t = sh + ρ' / Real.sin ϑ + ρ' := ⟨_, rfl⟩
  have hs20 : 0 < s2 := by linarith
  have hs2sh : sh < s2 := by linarith
  have h2Ss2 : 2 * S < s2 := by linarith
  obtain ⟨ρ, hρ⟩ : ∃ t : ℝ, t = s2 + S + 1 := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by linarith
  have hdivR3 : 0 < (2 * s2 + Real.sqrt d) / Real.sin ϑ := div_pos (by linarith) hσ0
  obtain ⟨R3, hR3⟩ : ∃ t : ℝ, t = s2 + (2 * s2 + Real.sqrt d) / Real.sin ϑ + 1 := ⟨_, rfl⟩
  have hR30 : 0 < R3 := by linarith
  obtain ⟨R, hR⟩ : ∃ t : ℝ, t = R' + s2 + S + R3 + ρ + 2 * S + sh + 1 := ⟨_, rfl⟩
  refine ⟨S, ρ, R, by linarith, by push_cast; linarith, by linarith, by linarith, ?_⟩
  intro G hb x hxlat hcard
  obtain ⟨xh, hxhlat, hxhx, hxhconn⟩ :=
    exists_rrConnected (Γ := G) (r := s) (R := S) hϑ hb (le_of_lt hs0') (by linarith) hxlat
  have claim : ∀ y ∈ ball x S, y ∈ lattice d → ConnWithin G (ball x R ∩ lattice d) xh y := by
    intro y hy hylat
    rw [mem_ball, dist_eq_norm] at hy
    have htri1 : ‖(xh - x) - (y - x)‖ ≤ ‖xh - x‖ + ‖y - x‖ := norm_sub_le _ _
    have hxhy : ‖xh - y‖ < 2 * S := by
      have he : xh - y = (xh - x) - (y - x) := by abel
      rw [he]; linarith
    have hv : ‖(G y).axis‖ = 1 := (G y).norm_axis
    have hϑV : ϑ ≤ (G y).apex := hb y
    have hϑV0 : 0 < (G y).apex := (G y).apex_pos
    have hϑV' : (G y).apex ≤ π / 2 := (G y).apex_le
    have hσV : Real.sin ϑ ≤ Real.sin (G y).apex :=
      Real.strictMonoOn_sin.monotoneOn ⟨by linarith [pi_pos], by linarith⟩
        ⟨by linarith [pi_pos], hϑV'⟩ hϑV
    have hσV0 : 0 < Real.sin (G y).apex := lt_of_lt_of_le hσ0 hσV
    have hdivV : ρ' / Real.sin (G y).apex ≤ ρ' / Real.sin ϑ :=
      div_le_div_of_nonneg_left (le_of_lt hρ'0) hσ0 hσV
    have hdivV0 : 0 < ρ' / Real.sin (G y).apex := div_pos hρ'0 hσV0
    obtain ⟨a, ha⟩ : ∃ w : EuclideanSpace ℝ (Fin d),
        w = xh + (ρ' / Real.sin (G y).apex) • (G y).axis := ⟨_, rfl⟩
    have haxh : ‖a - xh‖ = ρ' / Real.sin (G y).apex := by
      have he : a - xh = (ρ' / Real.sin (G y).apex) • (G y).axis := by rw [ha]; abel
      rw [he, norm_smul, hv, Real.norm_eq_abs, abs_of_pos hdivV0, mul_one]
    have hay : ‖a - y‖ < m := by
      have he : a - y = (a - xh) + (xh - y) := by abel
      have h1 : ‖(a - xh) + (xh - y)‖ ≤ ‖a - xh‖ + ‖xh - y‖ := norm_add_le _ _
      rw [he]; rw [haxh] at h1; linarith
    obtain ⟨z, hzlat, hza, hzy, hzca, hzcy⟩ :=
      exists_lattice_mem_inter (v := (G y).axis) (R := sh) hv hϑ hϑV hϑV' hay (by linarith)
    have hedge : z ∈ coneAt G y := by
      rw [mem_coneAt]; exact cone_subset_carrier _ hzcy
    have hzx : ‖z - x‖ < s2 + S := by
      have he : z - x = (z - a) + ((a - xh) + (xh - x)) := by abel
      have h1 : ‖(z - a) + ((a - xh) + (xh - x))‖ ≤ ‖z - a‖ + ‖(a - xh) + (xh - x)‖ :=
        norm_add_le _ _
      have h2 : ‖(a - xh) + (xh - x)‖ ≤ ‖a - xh‖ + ‖xh - x‖ := norm_add_le _ _
      rw [he]; rw [haxh] at h2; linarith
    have hzball : z ∈ ball x R ∩ lattice d :=
      ⟨by rw [mem_ball, dist_eq_norm]; linarith, hzlat⟩
    have hyball : y ∈ ball x R ∩ lattice d :=
      ⟨by rw [mem_ball, dist_eq_norm]; linarith, hylat⟩
    have hzy' : ConnWithin G (ball x R ∩ lattice d) y z :=
      ConnWithin.of_edge hyball hzball hedge
    obtain ⟨Reg, hReg⟩ : ∃ T : Set (EuclideanSpace ℝ (Fin d)),
        T = ball xh s2 ∩ shift (G y).carrier xh := ⟨_, rfl⟩
    have hRegdist : ∀ p ∈ Reg, ‖p - xh‖ < s2 := by
      intro p hp
      rw [hReg] at hp
      have := hp.1
      rw [mem_ball, dist_eq_norm] at this
      exact this
    have hRegsub : Reg ⊆ ball x ρ := by
      intro p hp
      rw [mem_ball, dist_eq_norm]
      have h1 := hRegdist p hp
      have he : p - x = (p - xh) + (xh - x) := by abel
      have h2 : ‖(p - xh) + (xh - x)‖ ≤ ‖p - xh‖ + ‖xh - x‖ := norm_add_le _ _
      rw [he]; linarith
    by_cases hcase : ∃ p ∈ Reg, p ∈ lattice d ∧ (G p).carrier = (G y).carrier
    · obtain ⟨p, hpReg, hplat, hptype⟩ := hcase
      have hpxh : ‖p - xh‖ < s2 := hRegdist p hpReg
      rw [hReg] at hpReg
      have hconn := discr_ueber_bande (Γ := G) (R := R3) hϑ hb hxhlat hylat hplat
        (by linarith : ‖xh - y‖ < s2) hpxh hpReg.2 hptype (by linarith)
      refine (ConnWithin.mono_ball ?_ hconn).symm
      rw [dist_eq_norm]; linarith
    · have hmiss : ∀ p ∈ Reg, p ∈ lattice d → (G p).carrier ≠ (G y).carrier := by
        intro p hp hplat htype
        exact hcase ⟨p, hp, hplat, htype⟩
      have hRegcard : (typesIn G Reg).encard ≤ (k : ℕ∞) := by
        refine encard_typesIn_le_of_missing hRegsub ?_ hylat hmiss hcard
        rw [mem_ball, dist_eq_norm]; linarith
      obtain ⟨w, hwlat, hwc, hwt, hwchain⟩ :=
        hchain (G y).axis (G y).apex hv hϑV hϑV' a z hzlat hzca
      have hshrink := shift_cone_apex_subset_shift_shrink (d := d) hv hϑV0 hϑV'
        (le_of_lt hρ'0) xh
      rw [← ha] at hshrink
      have hballReg : ∀ p ∈ shift (cone (G y).axis (G y).apex) a ∩ lattice d,
          ‖p - a‖ ≤ ‖z - a‖ → ball p ρ' ⊆ Reg := by
        intro p hp hpd u hu
        rw [mem_ball, dist_eq_norm] at hu
        rw [hReg]
        refine ⟨?_, ?_⟩
        · rw [mem_ball, dist_eq_norm]
          have he : u - xh = (u - p) + ((p - a) + (a - xh)) := by abel
          have h1 : ‖(u - p) + ((p - a) + (a - xh))‖ ≤ ‖u - p‖ + ‖(p - a) + (a - xh)‖ :=
            norm_add_le _ _
          have h2 : ‖(p - a) + (a - xh)‖ ≤ ‖p - a‖ + ‖a - xh‖ := norm_add_le _ _
          rw [he]; rw [haxh] at h2; linarith
        · have hpshr := hshrink hp.1
          refine cone_subset_carrier _ (hpshr.2 ?_)
          rw [Metric.mem_closedBall, dist_eq_norm]
          have he : u - xh - (p - xh) = u - p := by abel
          rw [he]
          exact le_of_lt hu
      have hconnp : ∀ p ∈ shift (cone (G y).axis (G y).apex) a ∩ lattice d,
          ‖p - a‖ ≤ ‖z - a‖ → RRConnected G r' R' p := by
        intro p hp hpd
        exact IH G hb p hp.2
          (le_trans (Set.encard_mono (typesIn_mono (hballReg p hp hpd))) hRegcard)
      have hsubp : ∀ p ∈ shift (cone (G y).axis (G y).apex) a ∩ lattice d,
          ‖p - a‖ ≤ ‖z - a‖ → R' + dist p x ≤ R := by
        intro p hp hpd
        rw [dist_eq_norm]
        have he : p - x = (p - a) + ((a - xh) + (xh - x)) := by abel
        have h1 : ‖(p - a) + ((a - xh) + (xh - x))‖ ≤ ‖p - a‖ + ‖(a - xh) + (xh - x)‖ :=
          norm_add_le _ _
        have h2 : ‖(a - xh) + (xh - x)‖ ≤ ‖a - xh‖ + ‖xh - x‖ := norm_add_le _ _
        rw [he]; rw [haxh] at h2; linarith
      have hzw : ConnWithin G (ball x R ∩ lattice d) z w :=
        connWithin_of_chain (le_of_lt hδr') hconnp hsubp hwchain
      have hwxh : ‖w - xh‖ < s := by
        have he : w - xh = (w - a) + (a - xh) := by abel
        have h1 : ‖(w - a) + (a - xh)‖ ≤ ‖w - a‖ + ‖a - xh‖ := norm_add_le _ _
        rw [he]; rw [haxh] at h1; linarith
      have hxhw : ConnWithin G (ball x R ∩ lattice d) xh w := by
        refine ConnWithin.mono_ball ?_
          (hxhconn w (by rw [mem_ball, dist_eq_norm]; exact hwxh) hwlat)
        rw [dist_eq_norm]; linarith
      exact (hxhw.trans hzw.symm).trans hzy'.symm
  intro y hy hylat
  exact (claim x (mem_ball_self hS0) hxlat).symm.trans (claim y hy hylat)


/-- **Lemma 5.7** of Bux–Kassmann–Schulze, the core induction: there is a jump
constant `δ > 0` and, for every `k`, radii `r_k ≤ ρ_k ≤ R_k` with `δ < r_k`, all
depending only on `ϑ` and `d`, such that every lattice point is
`r_k`-`R_k`-connected as soon as at most `k` cone types are realised at the
lattice points of `B_{ρ_k}`. -/
theorem core_induction (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℕ, ∃ r ρ R : ℝ, δ < r ∧ (k : ℝ) ≤ r ∧ r ≤ ρ ∧ ρ ≤ R ∧
      ∀ G : Configuration (EuclideanSpace ℝ (Fin d)), (∀ z, ϑ ≤ (G z).apex) →
      ∀ x ∈ lattice d, (typesIn G (ball x ρ)).encard ≤ (k : ℕ∞) →
        RRConnected G r R x := by
  obtain ⟨δ, t₀, hδ0, ht₀0, hchain⟩ := exists_chain_to_apex (d := d) hϑ hϑ'
  refine ⟨δ, hδ0, fun k => ?_⟩
  induction k with
  | zero =>
      refine ⟨δ + 1, δ + 1, δ + 1, by linarith, by push_cast; linarith, le_rfl, le_rfl, ?_⟩
      intro G _hb x hxlat hcard
      exfalso
      have hmem : (G x).carrier ∈ typesIn G (ball x (δ + 1)) :=
        mem_typesIn (mem_ball_self (by linarith)) hxlat
      have h0 : (typesIn G (ball x (δ + 1))).encard = 0 :=
        le_antisymm (by simpa using hcard) (zero_le)
      rw [Set.encard_eq_zero] at h0
      rw [h0] at hmem
      exact absurd hmem (Set.notMem_empty _)
  | succ k ih =>
      obtain ⟨r', ρ', R', h1, hk1, h2, h3, IH⟩ := ih
      exact core_induction_step hϑ hϑ' hδ0 ht₀0 hchain h1 hk1 h2 h3 IH


/-- **Lemma 5.7** in the form recorded by `CoreInduction`, for a fixed
`ϑ`-bounded configuration. -/
theorem coreInduction_holds (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) (hb : ∀ z, ϑ ≤ (Γ z).apex) :
    ∃ δ : ℝ, 0 < δ ∧ CoreInduction Γ δ := by
  obtain ⟨δ, hδ0, h⟩ := core_induction (d := d) (ϑ := ϑ) hϑ hϑ'
  refine ⟨δ, hδ0, fun k => ?_⟩
  obtain ⟨r, ρ, R, h1, -, h2, h3, h4⟩ := h k
  exact ⟨r, ρ, R, h1, h2, h3, h4 Γ hb⟩


/-- Sanity check that the conclusion of Lemma 5.7 has content: `ConnWithin` is not
vacuously true. With no admissible vertices only the reflexive case survives, so a
`ConnWithin` between distinct points really does record an edge path. -/
theorem connWithin_empty {x y : EuclideanSpace ℝ (Fin d)}
    (h : ConnWithin Γ ∅ x y) : x = y := by
  induction h with
  | refl => rfl
  | tail _ hstep _ => simp at hstep


/-! ## Corollary 5.8 -/

/-- Shrinking every cone of the configuration only removes edges. -/
lemma ConnWithin.mono_config {Γ' : Configuration (EuclideanSpace ℝ (Fin d))}
    (h : ∀ z, (Γ' z).carrier ⊆ (Γ z).carrier) {S : Set (EuclideanSpace ℝ (Fin d))}
    {x y : EuclideanSpace ℝ (Fin d)} (hxy : ConnWithin Γ' S x y) : ConnWithin Γ S x y := by
  induction hxy with
  | refl => exact ConnWithin.refl _
  | tail _ hstep ih =>
      refine ConnWithin.trans ih (Relation.ReflTransGen.single ?_)
      exact ⟨hstep.1, hstep.2.1, hstep.2.2.imp (fun e => h _ e) (fun e => h _ e)⟩

lemma RRConnected.mono_config {Γ' : Configuration (EuclideanSpace ℝ (Fin d))}
    (h : ∀ z, (Γ' z).carrier ⊆ (Γ z).carrier) {r R : ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : RRConnected Γ' r R x) : RRConnected Γ r R x :=
  fun y hy hylat => ConnWithin.mono_config h (hx y hy hylat)

/-- The observation closing the proof of Corollary 5.8: an `r`-`R`-connected point
is `r'`-`R`-connected for every `r' ≤ r`. -/
lemma RRConnected.mono_radius {r₁ r₂ R : ℝ} (h : r₂ ≤ r₁) {x : EuclideanSpace ℝ (Fin d)}
    (hx : RRConnected Γ r₁ R x) : RRConnected Γ r₂ R x :=
  fun y hy hylat => hx y (Metric.ball_subset_ball h hy) hylat

/-- **Corollary 5.8** of Bux–Kassmann–Schulze. For every `r > 0` there is `R ≥ r`,
depending only on `r`, `ϑ` and `d`, such that for *any* configuration with apex
angles bounded below by `ϑ`, every lattice point is `r`-`R`-connected.

By Corollary 2.4 one may replace the configuration by one taking at most `L`
values, with `L` depending only on `ϑ` and `d` (`ref_config_uniform`); Lemma 5.7
then applies with `k = L`, and the observation `RRConnected.mono_radius` brings
the small radius down to `r`. Because the paper's `r_k` are only known to exist
for each `k`, we take `k = max L ⌈r⌉₊` and use that `k ≤ r_k`, which is how
`core_induction` records the growth of the radii.

(The hypothesis `0 < r` that the paper states is not needed — for `r ≤ 0` the
ball `B_r(x)` is empty and the conclusion is vacuous. It is kept for fidelity.) -/
theorem discrete_template {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {r : ℝ} (_hr : 0 < r) :
    ∃ R : ℝ, r ≤ R ∧ ∀ G : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded G ϑ →
      ∀ x ∈ lattice d, RRConnected G r R x := by
  obtain ⟨L, hL⟩ := ref_config_uniform (E := EuclideanSpace ℝ (Fin d)) hϑ hϑ'
  obtain ⟨δ, hδ0, hcore⟩ :=
    core_induction (d := d) (ϑ := ϑ / 3) (by positivity) (by linarith [pi_pos])
  obtain ⟨rk, ρk, Rk, h1, hkr, h2, h3, h4⟩ := hcore (max L ⌈r⌉₊)
  have hrk : r ≤ rk := by
    have hle : r ≤ ((max L ⌈r⌉₊ : ℕ) : ℝ) := by
      calc r ≤ ((⌈r⌉₊ : ℕ) : ℝ) := Nat.le_ceil r
        _ ≤ ((max L ⌈r⌉₊ : ℕ) : ℝ) := by exact_mod_cast Nat.le_max_right L ⌈r⌉₊
    linarith
  refine ⟨Rk, by linarith, fun G hG x hxlat => ?_⟩
  obtain ⟨G', hcard, hsub, _hapex, hb'⟩ := hL G hG
  refine RRConnected.mono_config hsub (RRConnected.mono_radius hrk ?_)
  refine h4 G' hb'.2 x hxlat ?_
  calc (typesIn G' (ball x ρk)).encard
      ≤ ((fun V : DCone (EuclideanSpace ℝ (Fin d)) => V.carrier) '' (Set.range G')).encard := by
        refine Set.encard_mono ?_
        rintro _ ⟨p, -, rfl⟩
        exact ⟨G' p, ⟨p, rfl⟩, rfl⟩
    _ ≤ (Set.range G').encard := Set.encard_image_le _ _
    _ ≤ (L : ℕ∞) := hcard
    _ ≤ ((max L ⌈r⌉₊ : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_max_left L ⌈r⌉₊


/-! ## Lattice points in a bounded region

Needed to make "maximal size" in Definition 5.11 meaningful. -/

/-- Only finitely many lattice points lie in a ball. -/
theorem lattice_inter_closedBall_finite (a : EuclideanSpace ℝ (Fin d)) (M : ℝ) :
    (lattice d ∩ closedBall a M).Finite := by
  classical
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ‖a‖ + M ≤ (K : ℝ) := ⟨⌈‖a‖ + M⌉₊, Nat.le_ceil _⟩
  have hFfin : (Set.pi Set.univ (fun _ : Fin d => Set.Icc (-(K : ℤ)) (K : ℤ))).Finite :=
    Set.Finite.pi (fun _ => Set.finite_Icc _ _)
  refine Set.Finite.subset
    (hFfin.image (fun n : Fin d → ℤ =>
      (WithLp.toLp 2 (fun i => ((n i : ℤ) : ℝ)) : EuclideanSpace ℝ (Fin d)))) ?_
  rintro x ⟨hxlat, hxb⟩
  rw [mem_lattice_iff] at hxlat
  choose n hn using hxlat
  rw [Metric.mem_closedBall, dist_eq_norm] at hxb
  refine ⟨n, Set.mem_univ_pi.mpr (fun i => ?_), ?_⟩
  · have h1 : |x i - a i| ≤ M := by
      have h := abs_coord_le_norm (x - a) i
      have he : (x - a) i = x i - a i := by simp
      rw [he] at h
      linarith
    have h2 : |a i| ≤ ‖a‖ := abs_coord_le_norm a i
    have h3 : |((n i : ℤ) : ℝ)| ≤ (K : ℝ) := by
      rw [← hn i]
      have h4 := abs_sub_abs_le_abs_sub (x i) (a i)
      linarith
    rw [← Int.cast_abs] at h3
    have h5 : |n i| ≤ (K : ℤ) := by exact_mod_cast h3
    exact Set.mem_Icc.mpr (abs_le.mp h5)
  · have he : (fun i => ((n i : ℤ) : ℝ)) = WithLp.ofLp x := funext fun i => (hn i).symm
    simp only [he, WithLp.toLp_ofLp]

end QFS
