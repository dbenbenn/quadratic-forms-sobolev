/-
Section 3 of Bux–Kassmann–Schulze: the lattice `hℤ^d`, and Lemma 3.4 comparing
`|s-t|` with `|x-y|` for cube points over lattice points.
-/
import QuadraticFormsSobolev.Cubes

open Real Set Metric

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
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
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

/-- A point of `ℝ^1` from a real number. -/
private def pt (c : ℝ) : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => c)

private lemma norm_pt_sub (a b : ℝ) : ‖pt a - pt b‖ = |a - b| := by
  rw [EuclideanSpace.norm_eq]
  have hcoord : ∀ i : Fin 1, ‖(pt a - pt b) i‖ ^ 2 = (a - b) ^ 2 := by
    intro i
    simp [pt, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_congr rfl (fun i _ => hcoord i)]
  simp [Real.sqrt_sq_eq_abs]

private lemma infNorm_pt_sub (a b : ℝ) : infNorm (pt a - pt b) = |a - b| := by
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

end QFS
