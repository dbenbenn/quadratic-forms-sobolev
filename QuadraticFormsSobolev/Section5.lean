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

end QFS
