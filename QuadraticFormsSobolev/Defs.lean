/-
Definition 2.1 of Bux–Kassmann–Schulze, *Quadratic forms and Sobolev spaces of
fractional order* (arXiv:1707.09277): cones, double cones, double half-cones,
configurations, and `ϑ`-boundedness.
-/
import QuadraticFormsSobolev.Translate

open Real Set Metric
open RealInnerProductSpace

namespace QFS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Cones and double cones (Definition 2.1) -/

/-- The *cone* `Ṽ(v, ϑ)`, exactly as in Definition 2.1: the set of nonzero `h`
with `⟪v, h⟫ / ‖h‖ > cos ϑ`. -/
def cone (v : E) (ϑ : ℝ) : Set E :=
  {h : E | h ≠ 0 ∧ Real.cos ϑ < ⟪v, h⟫ / ‖h‖}

/-- The *double cone* `V(v, ϑ) = Ṽ ∪ (−Ṽ)` of Definition 2.1. -/
def doubleCone (v : E) (ϑ : ℝ) : Set E :=
  cone v ϑ ∪ -(cone v ϑ)

lemma mem_cone_iff {v h : E} {ϑ : ℝ} :
    h ∈ cone v ϑ ↔ h ≠ 0 ∧ Real.cos ϑ < ⟪v, h⟫ / ‖h‖ := Iff.rfl

lemma mem_doubleCone_iff {v h : E} {ϑ : ℝ} :
    h ∈ doubleCone v ϑ ↔ h ∈ cone v ϑ ∨ -h ∈ cone v ϑ := by
  simp [doubleCone, Set.mem_neg]

/-- The defining inequality of a cone, cleared of the division. -/
lemma mem_cone_iff_mul {v h : E} {ϑ : ℝ} :
    h ∈ cone v ϑ ↔ h ≠ 0 ∧ Real.cos ϑ * ‖h‖ < ⟪v, h⟫ := by
  constructor
  · rintro ⟨hne, hlt⟩
    have hn : 0 < ‖h‖ := norm_pos_iff.mpr hne
    rw [lt_div_iff₀ hn] at hlt
    exact ⟨hne, hlt⟩
  · rintro ⟨hne, hlt⟩
    have hn : 0 < ‖h‖ := norm_pos_iff.mpr hne
    exact ⟨hne, by rwa [lt_div_iff₀ hn]⟩

/-- A cone of apex angle at most `π/2` is convex — the "ice cream cone". This is
what makes the sets `B_r(x) ∩ Ṽ[x]` used in Theorem 4.1 connected. -/
lemma convex_cone (v : E) {ϑ : ℝ} (hϑ : ϑ ≤ π / 2) (hϑ₀ : 0 ≤ ϑ) : Convex ℝ (cone v ϑ) := by
  have hc0 : 0 ≤ Real.cos ϑ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hϑ⟩
  rintro h₁ hh₁ h₂ hh₂ a b ha hb hab
  rw [mem_cone_iff_mul] at hh₁ hh₂ ⊢
  have h1 := hh₁.2
  have h2 := hh₂.2
  have hinner : ⟪v, a • h₁ + b • h₂⟫ = a * ⟪v, h₁⟫ + b * ⟪v, h₂⟫ := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have hnorm : ‖a • h₁ + b • h₂‖ ≤ a * ‖h₁‖ + b * ‖h₂‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
      abs_of_nonneg hb]
  have hpos : Real.cos ϑ * (a * ‖h₁‖ + b * ‖h₂‖) < a * ⟪v, h₁⟫ + b * ⟪v, h₂⟫ := by
    rcases lt_or_eq_of_le ha with ha' | ha'
    · rcases lt_or_eq_of_le hb with hb' | hb'
      · nlinarith
      · rw [← hb']; nlinarith
    · rw [← ha']
      have hb1 : b = 1 := by rw [← ha'] at hab; linarith
      rw [hb1]; nlinarith
  have hne : a • h₁ + b • h₂ ≠ 0 := by
    intro hz
    rw [hz] at hinner
    simp only [inner_zero_right] at hinner
    have : (0:ℝ) ≤ Real.cos ϑ * (a * ‖h₁‖ + b * ‖h₂‖) := by
      have : 0 ≤ a * ‖h₁‖ + b * ‖h₂‖ := by positivity
      positivity
    linarith [hinner ▸ hpos]
  refine ⟨hne, ?_⟩
  calc Real.cos ϑ * ‖a • h₁ + b • h₂‖ ≤ Real.cos ϑ * (a * ‖h₁‖ + b * ‖h₂‖) :=
        mul_le_mul_of_nonneg_left hnorm hc0
    _ < a * ⟪v, h₁⟫ + b * ⟪v, h₂⟫ := hpos
    _ = ⟪v, a • h₁ + b • h₂⟫ := hinner.symm

lemma zero_notMem_cone (v : E) (ϑ : ℝ) : (0 : E) ∉ cone v ϑ := by
  simp [cone]

lemma zero_notMem_doubleCone (v : E) (ϑ : ℝ) : (0 : E) ∉ doubleCone v ϑ := by
  simp [mem_doubleCone_iff, zero_notMem_cone]

lemma ne_zero_of_mem_cone {v h : E} {ϑ : ℝ} (hh : h ∈ cone v ϑ) : h ≠ 0 := hh.1

lemma ne_zero_of_mem_doubleCone {v h : E} {ϑ : ℝ} (hh : h ∈ doubleCone v ϑ) : h ≠ 0 := by
  rcases mem_doubleCone_iff.mp hh with h' | h'
  · exact h'.1
  · simpa using fun hz => h'.1 (by simp [hz])

/-- A double cone is symmetric about the origin. -/
@[simp] lemma neg_mem_doubleCone_iff {v h : E} {ϑ : ℝ} :
    -h ∈ doubleCone v ϑ ↔ h ∈ doubleCone v ϑ := by
  simp [mem_doubleCone_iff, or_comm]

/-! ### The description of a cone through the unoriented angle

Mathlib's `InnerProductGeometry.angle` satisfies a triangle inequality, which is
what the proof of Lemma 2.2 needs. For a unit axis the paper's defining
inequality is exactly `angle v h < ϑ`. -/

open InnerProductGeometry in
lemma mem_cone_iff_angle {v h : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ₀ : 0 ≤ ϑ) (hϑ : ϑ ≤ π) :
    h ∈ cone v ϑ ↔ h ≠ 0 ∧ angle v h < ϑ := by
  constructor
  · rintro ⟨hne, hlt⟩
    refine ⟨hne, ?_⟩
    have hcos : Real.cos (angle v h) = ⟪v, h⟫ / ‖h‖ := by
      rw [cos_angle, hv, one_mul]
    rw [← hcos] at hlt
    by_contra hle
    rw [not_lt] at hle
    exact absurd (Real.strictAntiOn_cos.antitoneOn ⟨hϑ₀, hϑ⟩
      ⟨angle_nonneg v h, angle_le_pi v h⟩ hle) (not_le.mpr hlt)
  · rintro ⟨hne, hlt⟩
    refine ⟨hne, ?_⟩
    have hcos : Real.cos (angle v h) = ⟪v, h⟫ / ‖h‖ := by
      rw [cos_angle, hv, one_mul]
    rw [← hcos]
    exact Real.strictAntiOn_cos ⟨angle_nonneg v h, angle_le_pi v h⟩ ⟨hϑ₀, hϑ⟩ hlt

open InnerProductGeometry in
lemma mem_doubleCone_iff_angle {v h : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ₀ : 0 ≤ ϑ) (hϑ : ϑ ≤ π) :
    h ∈ doubleCone v ϑ ↔ h ≠ 0 ∧ (angle v h < ϑ ∨ π - ϑ < angle v h) := by
  rw [mem_doubleCone_iff, mem_cone_iff_angle hv hϑ₀ hϑ, mem_cone_iff_angle hv hϑ₀ hϑ]
  constructor
  · rintro (⟨hne, hlt⟩ | ⟨hne, hlt⟩)
    · exact ⟨hne, Or.inl hlt⟩
    · refine ⟨fun hz => hne (by simp [hz]), Or.inr ?_⟩
      rw [angle_neg_right] at hlt; linarith
  · rintro ⟨hne, hlt | hlt⟩
    · exact Or.inl ⟨hne, hlt⟩
    · refine Or.inr ⟨by simpa using hne, ?_⟩
      rw [angle_neg_right]; linarith

/-- Cones grow with the apex angle. -/
lemma cone_mono {v : E} {ϑ ϑ' : ℝ} (hϑ₀ : 0 ≤ ϑ) (hϑ' : ϑ' ≤ π) (h : ϑ ≤ ϑ') :
    cone v ϑ ⊆ cone v ϑ' := by
  rintro h' ⟨hne, hlt⟩
  refine ⟨hne, lt_of_le_of_lt ?_ hlt⟩
  exact Real.strictAntiOn_cos.antitoneOn ⟨hϑ₀, h.trans hϑ'⟩ ⟨hϑ₀.trans h, hϑ'⟩ h

/-- Double cones grow with the apex angle. -/
lemma doubleCone_mono {v : E} {ϑ ϑ' : ℝ} (hϑ₀ : 0 ≤ ϑ) (hϑ' : ϑ' ≤ π) (h : ϑ ≤ ϑ') :
    doubleCone v ϑ ⊆ doubleCone v ϑ' := by
  intro y hy
  rw [mem_doubleCone_iff] at hy ⊢
  exact hy.imp (fun a => cone_mono hϑ₀ hϑ' h a) (fun a => cone_mono hϑ₀ hϑ' h a)


/-! ## Openness of cones

The paper uses (in Section 4) that `Γ(x)` is open and does not contain the tip. -/

lemma isOpen_cone (v : E) (ϑ : ℝ) : IsOpen (cone v ϑ) := by
  have h1 : Continuous (fun h : E => ⟪v, h⟫) := by fun_prop
  have hcont : ContinuousOn (fun h : E => ⟪v, h⟫ / ‖h‖) {(0 : E)}ᶜ :=
    h1.continuousOn.div continuous_norm.continuousOn (fun h hh => by simpa using hh)
  have hopen : IsOpen ({(0 : E)}ᶜ ∩ (fun h : E => ⟪v, h⟫ / ‖h‖) ⁻¹' (Ioi (Real.cos ϑ))) :=
    hcont.isOpen_inter_preimage isOpen_compl_singleton isOpen_Ioi
  convert hopen using 1
  ext h
  simp [cone]

lemma isOpen_doubleCone (v : E) (ϑ : ℝ) : IsOpen (doubleCone v ϑ) :=
  (isOpen_cone v ϑ).union ((isOpen_cone v ϑ).neg)

/-! ## Double half-cones (Definition 2.1) -/

/-- The *double half-cone* `V_r(v, ϑ)` of Definition 2.1. -/
def doubleHalfCone (v : E) (ϑ r : ℝ) : Set E := shrink (doubleCone v ϑ) r

/-! ## Configurations (Definition 2.1) -/

/-- An element of the family `𝒱` of all double cones: a unit symmetry axis
together with an apex angle in `(0, π/2]`. -/
structure DCone (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The symmetry axis, a unit vector. -/
  axis : E
  /-- The axis is a unit vector. -/
  norm_axis : ‖axis‖ = 1
  /-- The apex angle. -/
  apex : ℝ
  /-- The apex angle is positive. -/
  apex_pos : 0 < apex
  /-- The apex angle is at most `π/2`. -/
  apex_le : apex ≤ π / 2

/-- The underlying subset of `ℝ^d` of a double cone. -/
def DCone.carrier (V : DCone E) : Set E := doubleCone V.axis V.apex

instance : Membership E (DCone E) := ⟨fun V x => x ∈ V.carrier⟩

@[simp] lemma DCone.mem_iff {V : DCone E} {x : E} : x ∈ V ↔ x ∈ V.carrier := Iff.rfl

lemma DCone.apex_le_pi (V : DCone E) : V.apex ≤ π := V.apex_le.trans (by linarith [pi_pos])

lemma DCone.isOpen_carrier (V : DCone E) : IsOpen V.carrier := isOpen_doubleCone _ _

lemma DCone.zero_notMem (V : DCone E) : (0 : E) ∉ V.carrier := zero_notMem_doubleCone _ _

/-- A *configuration* is a map `Γ : ℝ^d → 𝒱` (Definition 2.1). -/
abbrev Configuration (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  E → DCone E

/-- `Γ` is *`ϑ`-bounded*: `ϑ` is a positive lower bound for all apex angles
occurring in `Γ(ℝ^d)` (Definition 2.1). -/
def IsBounded (Γ : Configuration E) (ϑ : ℝ) : Prop :=
  0 < ϑ ∧ ∀ x, ϑ ≤ (Γ x).apex

/-- `V^Γ[x] = x + Γ(x)` (Definition 2.1). -/
def coneAt (Γ : Configuration E) (x : E) : Set E := shift (Γ x).carrier x

@[simp] lemma mem_coneAt {Γ : Configuration E} {x y : E} :
    y ∈ coneAt Γ x ↔ y - x ∈ (Γ x).carrier := Iff.rfl

lemma isOpen_coneAt (Γ : Configuration E) (x : E) : IsOpen (coneAt Γ x) := by
  have : coneAt Γ x = (fun y => y - x) ⁻¹' (Γ x).carrier := rfl
  rw [this]
  exact (Γ x).isOpen_carrier.preimage (continuous_id.sub continuous_const)

/-- A configuration puts no loop at `x`: `x ∉ V^Γ[x]` (used in Section 4). -/
lemma notMem_coneAt_self (Γ : Configuration E) (x : E) : x ∉ coneAt Γ x := by
  intro h
  rw [mem_coneAt, sub_self] at h
  exact (Γ x).zero_notMem h

/-- `V_r^Γ[x] = {y ∈ V^Γ[x] | B̄_r(y) ⊆ V^Γ[x]}` (Definition 2.1). -/
def coneAtShrink (Γ : Configuration E) (x : E) (r : ℝ) : Set E := shrink (coneAt Γ x) r

/-! ## Admissibility: condition (M) -/

section Measurable
variable [MeasurableSpace E]

/-- Condition (M) of Definition 2.1: `{(x,y) | y - x ∈ Γ(x)}` is a Borel set. -/
def CondM (Γ : Configuration E) : Prop :=
  MeasurableSet {p : E × E | p.2 - p.1 ∈ (Γ p.1).carrier}

/-- `Γ` is *`ϑ`-admissible*: `ϑ`-bounded and satisfying (M) (Definition 2.1). -/
def IsAdmissible (Γ : Configuration E) (ϑ : ℝ) : Prop := IsBounded Γ ϑ ∧ CondM Γ

lemma IsAdmissible.isBounded {Γ : Configuration E} {ϑ : ℝ} (h : IsAdmissible Γ ϑ) :
    IsBounded Γ ϑ := h.1

end Measurable

end QFS
