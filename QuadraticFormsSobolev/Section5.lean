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

The statement is recorded below as `CoreInduction`, and the base case `k = 1` is
proved. The induction step is not formalised; see the README for what it needs. -/

/-- The set of cone types realised at the lattice points of `S`. A "type" is the
double cone itself, as in Definition 4.2. -/
def typesIn (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (S : Set (EuclideanSpace ℝ (Fin d))) : Set (Set (EuclideanSpace ℝ (Fin d))) :=
  (fun p => (Γ p).carrier) '' (S ∩ lattice d)

/-- The statement of **Lemma 5.7**. Recorded so that the remaining target is
precise; only the case `k ≤ 1` is proved (`core_induction_base`). -/
def CoreInduction (Γ : Configuration (EuclideanSpace ℝ (Fin d))) (δ : ℝ) : Prop :=
  ∀ k : ℕ, ∃ r ρ R : ℝ, δ < r ∧ r ≤ ρ ∧ ρ ≤ R ∧
    ∀ x ∈ lattice d, Set.encard (typesIn Γ (ball x ρ)) ≤ (k : ℕ∞) →
      RRConnected Γ r R x

/-- **Lemma 5.7, the base case `k = 1`.** If only one cone type is realised at the
lattice points of `B_ρ(x)`, then `x` is `r`-`R`-connected; this is Corollary 5.2
applied to `x` and each lattice point of `B_r(x)`. -/
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

end QFS
