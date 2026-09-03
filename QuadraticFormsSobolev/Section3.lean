/-
Section 3 of Bux–Kassmann–Schulze: the lattice `hℤ^d`, and Lemma 3.4 comparing
`|s-t|` with `|x-y|` for cube points over lattice points.
-/
import QuadraticFormsSobolev.Cubes
import QuadraticFormsSobolev.RefCones

open Real Set Metric MeasureTheory

namespace QFS

variable {d : ℕ}

/-! ## Lattices -/

/-- The rescaled lattice `hℤ^d ⊆ ℝ^d`. -/
def scaledLattice (d : ℕ) (h : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, ∃ n : ℤ, x i = n * h}

/-- The lattice `ℤ^d ⊆ ℝ^d`. -/
def lattice (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) := scaledLattice d 1

lemma mem_lattice_iff {x : EuclideanSpace ℝ (Fin d)} :
    x ∈ lattice d ↔ ∀ i, ∃ n : ℤ, x i = n := by
  simp [lattice, scaledLattice]

/-! ## Lattice points in a bounded region

Needed to make "maximal size" in Definition 5.11 meaningful, and to pick the
axis of Lemma 3.3. -/

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

lemma infNorm_sub_comm (x y : EuclideanSpace ℝ (Fin d)) :
    infNorm (x - y) = infNorm (y - x) := by
  rw [← infNorm_neg (y - x), neg_sub]

/-- On the lattice `hℤ^d` the maximum norm takes values in `hℕ`; so a difference
of lattice points with `‖x-y‖_∞ > h` in fact has `‖x-y‖_∞ ≥ 2h`. This is the
step "the maximum norm takes only integer values on lattice points" in the proof
of Lemma 3.4. -/
lemma two_mul_le_infNorm_sub [Nonempty (Fin d)] {h : ℝ} (hh : 0 < h)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ scaledLattice d h)
    (hy : y ∈ scaledLattice d h) (hlt : h < infNorm (x - y)) :
    2 * h ≤ infNorm (x - y) := by
  obtain ⟨i, hi⟩ := exists_infNorm_eq (x - y)
  obtain ⟨n, hn⟩ := hx i
  obtain ⟨m, hm⟩ := hy i
  have hxy : (x - y) i = ((n - m : ℤ) : ℝ) * h := by
    have : (x - y) i = x i - y i := by simp
    rw [this, hn, hm]
    push_cast
    ring
  have key : infNorm (x - y) = |((n - m : ℤ) : ℝ)| * h := by
    rw [hi, hxy, abs_mul, abs_of_pos hh]
  rw [key] at hlt ⊢
  have h1 : (1 : ℝ) < |((n - m : ℤ) : ℝ)| := by nlinarith
  have hcast : |((n - m : ℤ) : ℝ)| = ((|n - m| : ℤ) : ℝ) := by push_cast [abs_abs]; ring_nf
  rw [hcast] at h1 ⊢
  have h2 : (1 : ℤ) < |n - m| := by exact_mod_cast h1
  have h3 : (2 : ℤ) ≤ |n - m| := by omega
  have h4 : (2 : ℝ) ≤ ((|n - m| : ℤ) : ℝ) := by exact_mod_cast h3
  nlinarith

/-! ## Lemma 3.4 -/

/-- **Lemma 3.4** of Bux–Kassmann–Schulze. For `x, y` in the lattice `hℤ^d` at
Euclidean distance more than `√d·h`, and points `s ∈ A_h(x)`, `t ∈ A_h(y)`,

  `(2√d)⁻¹ |x-y| < |s-t| < 2√d |x-y|`.

The paper states the hypothesis as `x, y ∈ ℤ^d` for every `h > 0`; its proof
treats `h = 1` and says the general case "follows by scaling", which is the
statement proved here. The literal statement is false — see
`lemma_cubes_literal_false`. -/
theorem lemma_cubes {h : ℝ} (hh : 0 < h) {x y s t : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ scaledLattice d h) (hy : y ∈ scaledLattice d h)
    (hxy : Real.sqrt d * h < ‖x - y‖) (hs : s ∈ cube h x) (ht : t ∈ cube h y) :
    1 / (2 * Real.sqrt d) * ‖x - y‖ < ‖s - t‖ ∧ ‖s - t‖ < 2 * Real.sqrt d * ‖x - y‖ := by
  -- The hypothesis forces `d > 0`.
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exfalso
    have : ‖x - y‖ = 0 := by simp [EuclideanSpace.norm_eq]
    rw [this] at hxy
    simp at hxy
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hsd : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  -- `‖x-y‖ ≤ √d · N` gives `h < N`, and lattice integrality upgrades this to `2h ≤ N`.
  have hN1 : ‖x - y‖ ≤ Real.sqrt d * infNorm (x - y) := norm_le_sqrt_dim_mul_infNorm _
  have hhN : h < infNorm (x - y) := by nlinarith
  have hN2 : 2 * h ≤ infNorm (x - y) := two_mul_le_infNorm_sub hh hx hy hhN
  -- The two cube conditions.
  have hsx : infNorm (s - x) < h / 2 := hs
  have hty : infNorm (t - y) < h / 2 := ht
  have hyt : infNorm (y - t) < h / 2 := by rw [infNorm_sub_comm]; exact ht
  have hxs : infNorm (x - s) < h / 2 := by rw [infNorm_sub_comm]; exact hs
  -- `M < N + h` and `N < M + h`.
  have hMN : infNorm (s - t) < infNorm (x - y) + h := by
    have e : s - t = (s - x) + ((x - y) + (y - t)) := by abel
    have b1 : infNorm (s - t) ≤ infNorm (s - x) + infNorm ((x - y) + (y - t)) := by
      rw [e]; exact infNorm_add_le _ _
    have b2 : infNorm ((x - y) + (y - t)) ≤ infNorm (x - y) + infNorm (y - t) :=
      infNorm_add_le _ _
    linarith
  have hNM : infNorm (x - y) < infNorm (s - t) + h := by
    have e : x - y = (x - s) + ((s - t) + (t - y)) := by abel
    have b1 : infNorm (x - y) ≤ infNorm (x - s) + infNorm ((s - t) + (t - y)) := by
      rw [e]; exact infNorm_add_le _ _
    have b2 : infNorm ((s - t) + (t - y)) ≤ infNorm (s - t) + infNorm (t - y) :=
      infNorm_add_le _ _
    linarith
  -- Passing between the two norms.
  have hNle : infNorm (x - y) ≤ ‖x - y‖ := infNorm_le_norm _
  have hMle : infNorm (s - t) ≤ ‖s - t‖ := infNorm_le_norm _
  have hstle : ‖s - t‖ ≤ Real.sqrt d * infNorm (s - t) := norm_le_sqrt_dim_mul_infNorm _
  have hNnn : 0 ≤ infNorm (x - y) := infNorm_nonneg _
  constructor
  · -- `‖x-y‖ ≤ √d N < √d (2M) ≤ 2√d ‖s-t‖`
    have hkey : ‖x - y‖ < 2 * Real.sqrt d * ‖s - t‖ := by nlinarith
    have he : 1 / (2 * Real.sqrt d) * ‖x - y‖ = ‖x - y‖ / (2 * Real.sqrt d) := by ring
    rw [he, div_lt_iff₀ (by positivity)]
    nlinarith
  · -- `‖s-t‖ ≤ √d M < √d (N + h) ≤ 2√d N ≤ 2√d ‖x-y‖`
    nlinarith

/-! ## The literal form of Lemma 3.4 is false

With `x, y ∈ ℤ^d` (rather than `hℤ^d`) the lower bound fails already for
`d = 1`, `h = 3/2`, `x = 0`, `y = 2`, `s = 7/10`, `t = 13/10`. -/

/-- The point of `ℝ^1` with coordinate `c`. -/
def pt (c : ℝ) : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => c)

@[simp] lemma pt_apply (c : ℝ) (i : Fin 1) : pt c i = c := rfl

@[simp] lemma pt_zero : pt 0 = 0 := rfl

lemma norm_pt_sub (a b : ℝ) : ‖pt a - pt b‖ = |a - b| := by
  rw [EuclideanSpace.norm_eq]
  have hcoord : ∀ i : Fin 1, ‖(pt a - pt b) i‖ ^ 2 = (a - b) ^ 2 := by
    intro i
    simp [pt, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_congr rfl (fun i _ => hcoord i)]
  simp [Real.sqrt_sq_eq_abs]

lemma infNorm_pt_sub (a b : ℝ) : infNorm (pt a - pt b) = |a - b| := by
  obtain ⟨i, hi⟩ := exists_infNorm_eq (pt a - pt b)
  rw [hi]
  simp [pt]

/-- The literal statement of Lemma 3.4, with `x, y ∈ ℤ^d` for arbitrary `h > 0`,
is false. -/
theorem lemma_cubes_literal_false :
    ¬ ∀ (d : ℕ) (h : ℝ), 0 < h → ∀ x y s t : EuclideanSpace ℝ (Fin d),
        x ∈ lattice d → y ∈ lattice d → Real.sqrt d * h < ‖x - y‖ →
        s ∈ cube h x → t ∈ cube h y →
        1 / (2 * Real.sqrt d) * ‖x - y‖ < ‖s - t‖ := by
  intro H
  have hlat : ∀ n : ℤ, pt (n : ℝ) ∈ lattice 1 := by
    intro n
    rw [mem_lattice_iff]
    exact fun i => ⟨n, by simp [pt]⟩
  have h1 : Real.sqrt (1 : ℕ) = 1 := by simp
  have hxy : Real.sqrt (1 : ℕ) * (3 / 2 : ℝ) < ‖pt 0 - pt 2‖ := by
    rw [norm_pt_sub, h1]; norm_num
  have hs : pt (7 / 10) ∈ cube (3 / 2 : ℝ) (pt 0) := by
    rw [mem_cube_iff, infNorm_pt_sub]; norm_num
  have ht : pt (13 / 10) ∈ cube (3 / 2 : ℝ) (pt 2) := by
    rw [mem_cube_iff, infNorm_pt_sub]; norm_num
  have := H 1 (3 / 2) (by norm_num) (pt 0) (pt 2) (pt (7 / 10)) (pt (13 / 10))
    (by simpa using hlat 0) (by simpa using hlat 2) hxy hs ht
  rw [norm_pt_sub, norm_pt_sub, h1] at this
  norm_num at this


/-! ## Favoured indices by majority (Section 3)

`A_h^m(u) = {x ∈ A_h(u) | V^m ⊆ Γ(x)}`, and `m` is *`h`-favoured by majority at
`u`* when this set has maximal Lebesgue measure among the reference cones. -/

section Favoured

variable {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {θ : ℝ}

/-- `A_h^m(u) = {x ∈ A_h(u) | V^m ⊆ Γ(x)}`. -/
def cubeCone (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (V : Set (EuclideanSpace ℝ (Fin d))) (h : ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x ∈ cube h u | V ⊆ (Γ x).carrier}

lemma cubeCone_subset_cube (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (V : Set (EuclideanSpace ℝ (Fin d))) (h : ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    cubeCone Γ V h u ⊆ cube h u := fun _ hx => hx.1

/-- `A_h(u) = ⋃_{i ∈ {1,…,L}} A_h^i(u)`, the identity from which the bound
`λ_d(A_h^m(u)) ≥ L⁻¹ λ_d(A_h(u))` is read off. -/
lemma cube_eq_biUnion_cubeCone (F : RefFamily Γ θ) (h : ℝ)
    (u : EuclideanSpace ℝ (Fin d)) :
    cube h u = ⋃ v ∈ F.axes, cubeCone Γ (F.cone v) h u := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hvS, hv⟩ := F.covers x
    exact Set.mem_biUnion hvS ⟨hx, hv⟩
  · intro hx
    obtain ⟨v, -, hx'⟩ := Set.mem_iUnion₂.mp hx
    exact hx'.1

/-- `v` is an *`h`-favoured index by majority at `u`*: among the reference cones,
`A_h^v(u)` has maximal Lebesgue measure. -/
def IsFavoured (F : RefFamily Γ θ) (h : ℝ) (u v : EuclideanSpace ℝ (Fin d)) : Prop :=
  v ∈ F.axes ∧ ∀ w ∈ F.axes,
    volume (cubeCone Γ (F.cone w) h u) ≤ volume (cubeCone Γ (F.cone v) h u)

/-- `λ_d(A_h^m(u)) ≥ L⁻¹ λ_d(A_h(u))` for every `h`-favoured index `m` at `u`
(Section 3, the remark following the definition). -/
theorem volume_cube_le_card_mul (F : RefFamily Γ θ) {h : ℝ}
    {u v : EuclideanSpace ℝ (Fin d)} (hv : IsFavoured F h u v) :
    volume (cube h u) ≤ F.axes.card * volume (cubeCone Γ (F.cone v) h u) := by
  rw [cube_eq_biUnion_cubeCone F h u]
  calc volume (⋃ w ∈ F.axes, cubeCone Γ (F.cone w) h u)
      ≤ ∑ w ∈ F.axes, volume (cubeCone Γ (F.cone w) h u) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _w ∈ F.axes, volume (cubeCone Γ (F.cone v) h u) :=
        Finset.sum_le_sum (fun w hw => hv.2 w hw)
    _ = F.axes.card * volume (cubeCone Γ (F.cone v) h u) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end Favoured

/-! ## Lemma 3.2 -/

section Indicator

variable {E : Type*}

/-- The indicator function of a set, valued in `ℝ`. -/
noncomputable def ind (S : Set E) (x : E) : ℝ := Set.indicator S (fun _ => 1) x

lemma ind_nonneg (S : Set E) (x : E) : 0 ≤ ind S x :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) x

lemma ind_of_mem {S : Set E} {x : E} (h : x ∈ S) : ind S x = 1 :=
  Set.indicator_of_mem h _

/-- The comparison of indicators used throughout: if membership on the left
forces membership on the right, the indicators compare. -/
lemma ind_le_ind {S T : Set E} {x y : E} (h : x ∈ S → y ∈ T) : ind S x ≤ ind T y := by
  by_cases hx : x ∈ S
  · rw [ind_of_mem hx, ind_of_mem (h hx)]
  · rw [ind, Set.indicator_of_notMem hx]
    exact ind_nonneg T y

end Indicator

/-- The content of the proof of Lemma 3.2: if `y ∈ V_{√d}[x]`, then
`B̄_{√d/2}(y) ⊆ V_{√d/2}[x]`, and hence the whole unit cube `A_1(y)` lies in
`V_{√d/2}[x]`. -/
lemma cube_subset_of_mem_shift_shrink {S : Set (EuclideanSpace ℝ (Fin d))}
    {x y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ shift (shrink S (Real.sqrt d)) x) :
    cube 1 y ⊆ shift (shrink S (Real.sqrt d / 2)) x := by
  rw [← shrink_shift] at hy ⊢
  have h2 : (Real.sqrt d : ℝ) = 2 * (Real.sqrt d / 2) := by ring
  rw [h2] at hy
  refine (cube_subset_closedBall y).trans ?_
  have hball := closedBall_subset_shrink hy
  have he : (1 : ℝ) / 2 * Real.sqrt d = Real.sqrt d / 2 := by ring
  rwa [he]

/-- **Lemma 3.2** of Bux–Kassmann–Schulze. The paper states it for `x, y ∈ ℤ^d`
and `1`-favoured indices `m` at `x` and `n` at `y`, with `s ∈ A_1^m(x)` and
`t ∈ A_1^n(y)`; its proof uses only `s ∈ A_1(x)` and `t ∈ A_1(y)`, which is what
is assumed here. See `lemma_min_dist_favoured` for the paper's exact form. -/
theorem lemma_min_dist {V W : Set (EuclideanSpace ℝ (Fin d))}
    {x y s t : EuclideanSpace ℝ (Fin d)} (hs : s ∈ cube 1 x) (ht : t ∈ cube 1 y) :
    ind (shift (shrink V (Real.sqrt d / 2)) x) t
        + ind (shift (shrink W (Real.sqrt d / 2)) y) s
      ≥ ind (shift (shrink V (Real.sqrt d)) x) y
        + ind (shift (shrink W (Real.sqrt d)) y) x := by
  refine add_le_add (ind_le_ind (fun hy => ?_)) (ind_le_ind (fun hx => ?_))
  · exact cube_subset_of_mem_shift_shrink hy ht
  · exact cube_subset_of_mem_shift_shrink hx hs

/-- **Lemma 3.2** in the paper's exact form, with lattice points and `1`-favoured
indices. -/
theorem lemma_min_dist_favoured {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {θ : ℝ}
    (F : RefFamily Γ θ) {x y v w s t : EuclideanSpace ℝ (Fin d)}
    (_hx : x ∈ lattice d) (_hy : y ∈ lattice d)
    (_hv : IsFavoured F 1 x v) (_hw : IsFavoured F 1 y w)
    (hs : s ∈ cubeCone Γ (F.cone v) 1 x) (ht : t ∈ cubeCone Γ (F.cone w) 1 y) :
    ind (shift (shrink (F.cone v) (Real.sqrt d / 2)) x) t
        + ind (shift (shrink (F.cone w) (Real.sqrt d / 2)) y) s
      ≥ ind (shift (shrink (F.cone v) (Real.sqrt d)) x) y
        + ind (shift (shrink (F.cone w) (Real.sqrt d)) y) x :=
  lemma_min_dist hs.1 ht.1


lemma norm_pt (c : ℝ) : ‖pt c‖ = |c| := by
  have := norm_pt_sub c 0
  simpa using this

lemma pt_mem_lattice (n : ℤ) : pt (n : ℝ) ∈ lattice 1 := by
  rw [mem_lattice_iff]
  exact fun i => ⟨n, by simp⟩

/-! ## Lemma 3.3 is false in dimension one

Lemma 3.3 asserts: for every `r > 0` there is an apex angle `θ > 0` such that
each reference cone `V^m` admits an axis `v(m)` with
`V(v(m), θ) ∩ ℤ^d ⊆ V^m_r ∩ ℤ^d`. Proposition 3.5 applies it with `r = √d`.

In `d = 1` every double cone is all of `ℝ \ {0}`, so `V(v, θ) ∩ ℤ = ℤ \ {0}`,
while `V^m_r ∩ ℤ = {n : |n| > r}` omits `±1` as soon as `r ≥ 1`. With `r = √d = 1`
the inclusion therefore fails for every choice of `θ` and `v`. -/

/-- In `ℝ^1` every double cone contains the lattice point `1`. -/
lemma pt_one_mem_doubleCone {v : EuclideanSpace ℝ (Fin 1)} (hv : ‖v‖ = 1)
    {θ : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ π / 2) : pt 1 ∈ doubleCone v θ := by
  have hcos : Real.cos θ < 1 := by
    have h0 : (0 : ℝ) ∈ Set.Icc 0 π := ⟨le_refl 0, Real.pi_pos.le⟩
    have hm : θ ∈ Set.Icc 0 π := ⟨hθ.le, by linarith [Real.pi_pos]⟩
    have := Real.strictAntiOn_cos h0 hm hθ
    simpa using this
  have hv0 : |v 0| = 1 := by
    rw [← hv, EuclideanSpace.norm_eq]
    simp [Real.sqrt_sq_eq_abs]
  have hne : pt 1 ≠ 0 := by
    intro hc
    have := congrArg (fun z : EuclideanSpace ℝ (Fin 1) => z 0) hc
    simp at this
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hv0 with h1 | h1
  · refine Or.inl ⟨hne, ?_⟩
    have hinner : (inner ℝ v (pt 1) : ℝ) = 1 := by
      simp [PiLp.inner_apply, h1]
    rw [hinner, norm_pt]
    simpa using hcos
  · refine Or.inr ⟨by simpa using hne, ?_⟩
    have hneg : -pt (1 : ℝ) = pt (-1) := by
      ext i; simp
    rw [hneg]
    have hinner : (inner ℝ v (pt (-1)) : ℝ) = 1 := by
      simp [PiLp.inner_apply, h1]
    rw [hinner, norm_pt]
    simpa using hcos

/-- **Lemma 3.3 is false in dimension one** for `r = √d = 1`: no apex angle
`θ ∈ (0, π/2]` and no unit axis `v` give `V(v,θ) ∩ ℤ ⊆ V_r ∩ ℤ`, whatever the
reference cone `V(u, ϑ)`. -/
theorem lemma_new_config_false_dim_one
    (u : EuclideanSpace ℝ (Fin 1)) (ϑ : ℝ)
    (v : EuclideanSpace ℝ (Fin 1)) (hv : ‖v‖ = 1) (θ : ℝ) (hθ : 0 < θ) (hθ' : θ ≤ π / 2) :
    ¬ (doubleCone v θ ∩ lattice 1 ⊆ shrink (doubleCone u ϑ) 1 ∩ lattice 1) := by
  intro H
  have h1 : pt 1 ∈ doubleCone v θ ∩ lattice 1 :=
    ⟨pt_one_mem_doubleCone hv hθ hθ', by simpa using pt_mem_lattice 1⟩
  obtain ⟨-, hball⟩ := (H h1).1
  have hmem : (0 : EuclideanSpace ℝ (Fin 1)) ∈ closedBall (pt 1) 1 := by
    rw [Metric.mem_closedBall, dist_zero_left, norm_pt]
    norm_num
  exact zero_notMem_doubleCone u ϑ (hball hmem)

end QFS
