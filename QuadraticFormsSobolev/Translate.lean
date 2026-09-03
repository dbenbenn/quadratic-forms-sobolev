/-
Translation and shrinking of subsets of a normed space.

Definition 2.1 of Bux-Kassmann-Schulze forms double half-cones `V_r` and shifted
cones `V[x]`; both operations, and the whole of the proof of Lemma 2.7, use only
the normed group structure, so they are developed here in that generality.
-/
import Mathlib

open Real Set Metric

namespace QFS

variable {E : Type*} [NormedAddCommGroup E]

/-! ## Shrinking a set

For a set `S` and `r > 0`, `S_r = {y ∈ S | closedBall y r ⊆ S}`. Applied to a double
cone this is the paper's *double half-cone* `V_r` (Definition 2.1). -/


/-- The `r`-shrinking `S_r = {y ∈ S | B̄_r(y) ⊆ S}` of Definition 2.1. -/
def shrink (S : Set E) (r : ℝ) : Set E := {y ∈ S | closedBall y r ⊆ S}

@[simp] lemma mem_shrink {S : Set E} {r : ℝ} {y : E} :
    y ∈ shrink S r ↔ y ∈ S ∧ closedBall y r ⊆ S := Iff.rfl

lemma shrink_subset (S : Set E) (r : ℝ) : shrink S r ⊆ S := fun _ h => h.1

/-! ## Shifted cones -/

/-- `S[x] = S + x`, the shift of Definition 2.1. -/
def shift (S : Set E) (x : E) : Set E := {y | y - x ∈ S}

@[simp] lemma mem_shift {S : Set E} {x y : E} : y ∈ shift S x ↔ y - x ∈ S := Iff.rfl

/-- `shift` really is translation: `S[x] = S + x`. -/
lemma shift_eq_image (S : Set E) (x : E) : shift S x = (fun h => x + h) '' S := by
  ext y
  simp only [mem_shift, Set.mem_image]
  constructor
  · exact fun h => ⟨y - x, h, by abel⟩
  · rintro ⟨h, hh, rfl⟩
    simpa using hh

@[simp] lemma shift_zero (S : Set E) : shift S 0 = S := by ext y; simp [shift]

/-- Shrinking commutes with shifting. -/
lemma shrink_shift (S : Set E) (r : ℝ) (x : E) :
    shrink (shift S x) r = shift (shrink S r) x := by
  ext y
  simp only [mem_shrink, mem_shift, Set.subset_def, Metric.mem_closedBall, dist_eq_norm]
  constructor
  · rintro ⟨hy, hb⟩
    refine ⟨hy, fun z hz => ?_⟩
    have h1 : ‖z + x - y‖ ≤ r := by
      have he : z + x - y = z - (y - x) := by abel
      rw [he]; exact hz
    simpa using hb (z + x) h1
  · rintro ⟨hy, hb⟩
    refine ⟨hy, fun z hz => ?_⟩
    have h1 : ‖z - x - (y - x)‖ ≤ r := by
      have he : z - x - (y - x) = z - y := by abel
      rw [he]; exact hz
    exact hb (z - x) h1

/-! ## Elementary properties of `shift` -/

lemma shift_mono {S T : Set E} (h : S ⊆ T) (x : E) : shift S x ⊆ shift T x :=
  fun _ hy => h hy

lemma shift_shift (S : Set E) (a b : E) : shift (shift S a) b = shift S (a + b) := by
  ext y
  simp only [mem_shift]
  constructor
  · intro h; simpa [sub_add_eq_sub_sub, sub_right_comm] using h
  · intro h; simpa [sub_add_eq_sub_sub, sub_right_comm] using h

lemma shrink_mono {S T : Set E} (h : S ⊆ T) (r : ℝ) : shrink S r ⊆ shrink T r :=
  fun _ hy => ⟨h hy.1, hy.2.trans h⟩

/-- Shrinking by a larger radius gives a smaller set. -/
lemma shrink_antitone (S : Set E) {r r' : ℝ} (h : r ≤ r') : shrink S r' ⊆ shrink S r :=
  fun _ hy => ⟨hy.1, (closedBall_subset_closedBall h).trans hy.2⟩

/-! ## Step (⋆) of the proof of Lemma 2.7

`V_ℓ = ⋂_{ξ ∈ B̄_ℓ} V[ξ]`. -/

/-- Equation (⋆) in the proof of Lemma 2.7: the `ℓ`-shrinking of `S` is exactly
the intersection of all translates `S[ξ]` with `‖ξ‖ ≤ ℓ`. -/
theorem shrink_eq_iInter_shift (S : Set E) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    shrink S ℓ = ⋂ ξ ∈ closedBall (0 : E) ℓ, shift S ξ := by
  ext ζ
  simp only [mem_shrink, Set.mem_iInter, mem_shift, Metric.mem_closedBall,
    Set.subset_def, dist_eq_norm]
  constructor
  · rintro ⟨-, hb⟩ ξ hξ
    refine hb (ζ - ξ) ?_
    simpa using hξ
  · intro h
    constructor
    · simpa using h 0 (by simpa using hℓ)
    · intro z hz
      have := h (ζ - z) (by simpa [norm_sub_rev] using hz)
      simpa using this

/-! ## Step (✝) of the proof of Lemma 2.7

`⋃_{ξ ∈ B̄_ℓ} V_{2ℓ}[ξ] ⊆ V_ℓ`. -/

/-- The intermediate claim of the proof of Lemma 2.7: if `ζ ∈ S_{2ℓ}` then
`B̄_ℓ(ζ) ⊆ S_ℓ`. -/
lemma closedBall_subset_shrink {S : Set E} {ℓ : ℝ} {ζ : E} (hζ : ζ ∈ shrink S (2 * ℓ)) :
    closedBall ζ ℓ ⊆ shrink S ℓ := by
  intro w hw
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  have hℓ : 0 ≤ ℓ := le_trans (norm_nonneg _) hw
  have hle : ∀ u : E, ‖u - w‖ ≤ ℓ → u ∈ S := by
    intro u hu
    refine hζ.2 ?_
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖u - ζ‖ = ‖(u - w) + (w - ζ)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖u - w‖ + ‖w - ζ‖ := norm_add_le _ _
      _ ≤ ℓ + ℓ := add_le_add hu hw
      _ = 2 * ℓ := by ring
  exact ⟨hle w (by simpa using hℓ), fun u hu => hle u (by
    rw [Metric.mem_closedBall, dist_eq_norm] at hu; exact hu)⟩

/-- Equation (✝) in the proof of Lemma 2.7. -/
theorem iUnion_shift_shrink_subset (S : Set E) (ℓ : ℝ) :
    ⋃ ξ ∈ closedBall (0 : E) ℓ, shift (shrink S (2 * ℓ)) ξ ⊆ shrink S ℓ := by
  intro y hy
  simp only [Set.mem_iUnion, mem_shift, Metric.mem_closedBall, dist_zero_right] at hy
  obtain ⟨ξ, hξ, hyξ⟩ := hy
  refine closedBall_subset_shrink hyξ ?_
  rw [Metric.mem_closedBall, dist_eq_norm]
  simpa using hξ

/-! ## The conclusion of the proof of Lemma 2.7 -/

/-- The untranslated conclusion drawn in the proof of Lemma 2.7:
for every `ξ` with `‖ξ‖ ≤ ℓ`, `S_{2ℓ}[ξ] ⊆ S_ℓ ⊆ S[ξ]`. -/
theorem shift_shrink_two_subset (S : Set E) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {ξ : E} (hξ : ‖ξ‖ ≤ ℓ) :
    shift (shrink S (2 * ℓ)) ξ ⊆ shrink S ℓ ∧ shrink S ℓ ⊆ shift S ξ := by
  refine ⟨?_, ?_⟩
  · intro y hy
    refine iUnion_shift_shrink_subset S ℓ ?_
    simp only [Set.mem_iUnion, Metric.mem_closedBall, dist_zero_right]
    exact ⟨ξ, hξ, hy⟩
  · rw [shrink_eq_iInter_shift S hℓ]
    exact Set.biInter_subset_of_mem (by simpa using hξ)

/-- Lemma 2.7, in the translated form the paper states just before specialising
`ℓ = (h/2)√d`: for every `x` and every `ξ` in the closed `ℓ`-ball around `x`,
`S_{2ℓ}[ξ] ⊆ S_ℓ[x] ⊆ S[ξ]`. -/
theorem shift_shrink_sandwich (S : Set E) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (x : E) {ξ : E}
    (hξ : ‖ξ - x‖ ≤ ℓ) :
    shift (shrink S (2 * ℓ)) ξ ⊆ shift (shrink S ℓ) x ∧
      shift (shrink S ℓ) x ⊆ shift S ξ := by
  obtain ⟨h1, h2⟩ := shift_shrink_two_subset S hℓ (ξ := ξ - x) hξ
  have e : ξ - x + x = ξ := by abel
  constructor
  · have := shift_mono h1 x
    rwa [shift_shift, e] at this
  · have := shift_mono h2 x
    rwa [shift_shift, e] at this

end QFS
