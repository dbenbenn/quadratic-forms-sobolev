/-
Lemma A.2 of Bux–Kassmann–Schulze: a Lebesgue differentiation theorem along
cubes.

  *Let `φ : ℝ^d → ℝ` be locally integrable. For almost every `s`: if `(x_h)_{h>0}`
  is a sequence in `hℤ^d` with `s ∈ Ã_h(x_h)` for every `h`, then*
  `λ_d(A_h(x_h))^{-1} ∫_{A_h(x_h)} φ → φ(s)` *as `h → 0`.*

The cubes are not centred at `s`, so this is not the plain differentiation
theorem for balls; but a cube of side `h` containing `s` sits inside
`B̄_{h√d}(s)` and has volume `h^d`, a fixed fraction of that ball's volume, so
the cubes form a Vitali family and Mathlib's `VitaliFamily.ae_tendsto_average`
applies. Nothing here needs the cubes to be centred at lattice points, so the
statement is proved for arbitrary centres.
-/
import QuadraticFormsSobolev.Section3

open Real Set Metric MeasureTheory ENNReal Filter Topology
open scoped NNReal

namespace QFS

variable {d : ℕ}

/-! ## Cubes are closed, and open cubes are open -/

lemma continuous_coord (i : Fin d) :
    Continuous (fun x : EuclideanSpace ℝ (Fin d) => x i) := by
  refine LipschitzWith.continuous (K := 1) (fun x y => ?_)
  rw [edist_dist, edist_dist, ENNReal.coe_one, one_mul]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.dist_eq, dist_eq_norm]
  have h := abs_coord_le_norm (x - y) i
  have he : (x - y) i = x i - y i := by simp
  rw [he] at h
  exact h

lemma closedCube_eq_iInter {h : ℝ} (hh : 0 ≤ h) (u : EuclideanSpace ℝ (Fin d)) :
    closedCube h u = ⋂ i, (fun x : EuclideanSpace ℝ (Fin d) => x i) ⁻¹'
      (Icc (u i - h / 2) (u i + h / 2)) := by
  rw [closedCube_eq_preimage hh]
  ext x
  simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]

lemma cube_eq_iInter {h : ℝ} (hh : 0 < h) (u : EuclideanSpace ℝ (Fin d)) :
    cube h u = ⋂ i, (fun x : EuclideanSpace ℝ (Fin d) => x i) ⁻¹'
      (Ioo (u i - h / 2) (u i + h / 2)) := by
  rw [cube_eq_preimage hh]
  ext x
  simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]

lemma isClosed_closedCube {h : ℝ} (hh : 0 ≤ h) (u : EuclideanSpace ℝ (Fin d)) :
    IsClosed (closedCube h u) := by
  rw [closedCube_eq_iInter hh]
  exact isClosed_iInter (fun i => isClosed_Icc.preimage (continuous_coord i))

lemma isOpen_cube {h : ℝ} (hh : 0 < h) (u : EuclideanSpace ℝ (Fin d)) :
    IsOpen (cube h u) := by
  rw [cube_eq_iInter hh]
  exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (continuous_coord i))

lemma mem_cube_self {h : ℝ} (hh : 0 < h) (u : EuclideanSpace ℝ (Fin d)) :
    u ∈ cube h u := by
  have he : infNorm (u - u) = 0 := by
    rw [sub_self]
    simp [infNorm]
  simp only [cube, Set.mem_ofPred_eq, he]
  linarith

/-- A cube of side `h` containing `x` lies in the ball of radius `h√d` about
`x`. -/
lemma closedCube_subset_closedBall_of_mem {h : ℝ} {u x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ closedCube h u) : closedCube h u ⊆ closedBall x (h * Real.sqrt d) := by
  intro y hy
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h1 : infNorm (y - u) ≤ h / 2 := hy
  have h2 : infNorm (x - u) ≤ h / 2 := hx
  have h3 : infNorm (y - x) ≤ h := by
    have he : y - x = (y - u) + (u - x) := by abel
    have h4 : infNorm (u - x) = infNorm (x - u) := infNorm_sub_comm _ _
    calc infNorm (y - x) ≤ infNorm (y - u) + infNorm (u - x) := by
          rw [he]; exact infNorm_add_le _ _
      _ ≤ h := by rw [h4]; linarith
  calc ‖y - x‖ ≤ Real.sqrt d * infNorm (y - x) := norm_le_sqrt_dim_mul_infNorm _
    _ ≤ Real.sqrt d * h := mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
    _ = h * Real.sqrt d := by ring

/-! ## The Vitali family of cubes -/

/-- The volume of the unit ball of `ℝ^d`. -/
noncomputable def unitBallVol (d : ℕ) : ℝ≥0∞ :=
  volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)

lemma unitBallVol_ne_top : unitBallVol d ≠ ⊤ := measure_closedBall_lt_top.ne

lemma volume_closedBall_eq (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall x r) = ENNReal.ofReal (r ^ d) * unitBallVol d := by
  rw [unitBallVol, Measure.addHaar_closedBall' volume x hr, finrank_euclideanSpace_fin]

/-- The doubling constant of the Vitali family of cubes: big enough both for the
doubling condition on balls and for a cube of side `h` to fill a fixed fraction
of the ball of radius `3h√d`. -/
noncomputable def cubeVitaliConst (d : ℕ) : ℝ≥0 :=
  (3 : ℝ≥0) ^ d + Real.toNNReal ((3 * Real.sqrt d) ^ d) * (unitBallVol d).toNNReal

lemma cubeVitali_doubling (x : EuclideanSpace ℝ (Fin d)) :
    ∃ᶠ r in 𝓝[>] (0:ℝ), volume (closedBall x (3 * r))
      ≤ cubeVitaliConst d * volume (closedBall x r) := by
  refine Filter.Eventually.frequently ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : (0:ℝ) < r := hr
  rw [volume_closedBall_eq x (by positivity), volume_closedBall_eq x hr0.le,
    show (3 * r) ^ d = 3 ^ d * r ^ d by ring,
    ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 3 ^ d)]
  have hc : ENNReal.ofReal ((3:ℝ) ^ d) ≤ ((cubeVitaliConst d : ℝ≥0) : ℝ≥0∞) := by
    have h1 : ENNReal.ofReal ((3:ℝ) ^ d) = (((3:ℝ≥0) ^ d : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_pow]
      rw [show ((3:ℝ) ^ d) = ((3:ℝ) ^ d) from rfl, ENNReal.ofReal_pow (by norm_num)]
      congr 1
      simp [ENNReal.ofReal]
    rw [h1]
    simp only [cubeVitaliConst]
    exact ENNReal.coe_le_coe.mpr le_self_add
  calc ENNReal.ofReal ((3:ℝ) ^ d) * ENNReal.ofReal (r ^ d) * unitBallVol d
      = ENNReal.ofReal ((3:ℝ) ^ d) * (ENNReal.ofReal (r ^ d) * unitBallVol d) := by ring
    _ ≤ ((cubeVitaliConst d : ℝ≥0) : ℝ≥0∞) * (ENNReal.ofReal (r ^ d) * unitBallVol d) :=
        mul_le_mul' hc le_rfl

/-- The Vitali family in which the closed cubes live. -/
noncomputable def cubeVitali (d : ℕ) :
    VitaliFamily (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  Vitali.vitaliFamily volume (cubeVitaliConst d) cubeVitali_doubling

lemma closedCube_mem_setsAt {h : ℝ} (hh : 0 < h) {u x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ closedCube h u) : closedCube h u ∈ (cubeVitali d).setsAt x := by
  refine ⟨isClosed_closedCube hh.le u, ⟨u, ?_⟩, h * Real.sqrt d,
    closedCube_subset_closedBall_of_mem hx, ?_⟩
  · exact ((isOpen_cube hh u).subset_interior_iff.mpr (cube_subset_closedCube h u))
      (mem_cube_self hh u)
  · have hsd : (0:ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
    rw [volume_closedBall_eq x (by positivity), volume_closedCube hh.le,
      show (3 * (h * Real.sqrt d)) ^ d = (3 * Real.sqrt d) ^ d * h ^ d by ring,
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (3 * Real.sqrt d) ^ d)]
    have hc : ENNReal.ofReal ((3 * Real.sqrt d) ^ d) * unitBallVol d
        ≤ ((cubeVitaliConst d : ℝ≥0) : ℝ≥0∞) := by
      have h1 : ENNReal.ofReal ((3 * Real.sqrt d) ^ d) * unitBallVol d
          = ((Real.toNNReal ((3 * Real.sqrt d) ^ d) * (unitBallVol d).toNNReal :
              ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.coe_mul, ENNReal.coe_toNNReal unitBallVol_ne_top]
        rfl
      rw [h1]
      simp only [cubeVitaliConst]
      exact ENNReal.coe_le_coe.mpr le_add_self
    calc ENNReal.ofReal ((3 * Real.sqrt d) ^ d) * ENNReal.ofReal (h ^ d) * unitBallVol d
        = (ENNReal.ofReal ((3 * Real.sqrt d) ^ d) * unitBallVol d)
          * ENNReal.ofReal (h ^ d) := by ring
      _ ≤ ((cubeVitaliConst d : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (h ^ d) :=
          mul_le_mul' hc le_rfl

/-- The cubes of a shrinking sequence containing `x` converge to `x` in the
Vitali family's filter. -/
lemma tendsto_closedCube_filterAt {ι : Type} {l : Filter ι} {x : EuclideanSpace ℝ (Fin d)}
    (hn : ι → ℝ) (un : ι → EuclideanSpace ℝ (Fin d)) (hpos : ∀ i, 0 < hn i)
    (hlim : Tendsto hn l (𝓝 0)) (hmem : ∀ i, x ∈ closedCube (hn i) (un i)) :
    Tendsto (fun i => closedCube (hn i) (un i)) l ((cubeVitali d).filterAt x) := by
  refine (cubeVitali d).tendsto_filterAt_iff.mpr
    ⟨Eventually.of_forall (fun i => closedCube_mem_setsAt (hpos i) (hmem i)), fun ε hε => ?_⟩
  have hsd : (0:ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hlim' : Tendsto (fun i => hn i * Real.sqrt d) l (𝓝 0) := by
    simpa using hlim.mul_const (Real.sqrt d)
  filter_upwards [hlim' (Iio_mem_nhds (show (0:ℝ) < ε from hε))] with i hi
  exact (closedCube_subset_closedBall_of_mem (hmem i)).trans
    (closedBall_subset_closedBall (le_of_lt hi))

/-! ## Lemma A.2 -/

/-- **Lemma A.2** of Bux–Kassmann–Schulze. For a locally integrable `φ` and
almost every `s`, the averages of `φ` over any shrinking sequence of cubes
containing `s` converge to `φ(s)`.

The paper takes the cubes centred at points of `hℤ^d`; the proof needs only that
they contain `s` and shrink, so no lattice hypothesis appears. The paper's
`λ_d(A_h(x_h))^{-1} ∫_{A_h(x_h)} φ` is the average over the open cube, which
agrees with the average over the closed one since they differ by a null set. -/
theorem lemma_lebesgue_diff {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : LocallyIntegrable φ volume) :
    ∀ᵐ s : EuclideanSpace ℝ (Fin d),
      ∀ {ι : Type} {l : Filter ι} (hn : ι → ℝ) (un : ι → EuclideanSpace ℝ (Fin d)),
        (∀ i, 0 < hn i) → Tendsto hn l (𝓝 0) → (∀ i, s ∈ closedCube (hn i) (un i)) →
        Tendsto (fun i => ⨍ y in closedCube (hn i) (un i), φ y) l (𝓝 (φ s)) := by
  filter_upwards [(cubeVitali d).ae_tendsto_average hφ] with s hs ι l hn un hpos hlim hmem
  exact hs.comp (tendsto_closedCube_filterAt hn un hpos hlim hmem)

/-! ## The step functions of Section 3.2

Section 3.2 replaces `f` by the piecewise-constant approximation
`f_h(x) = h^{-d} ∫_{A_h(x) ∩ B*} f`, indexed by the lattice point whose
half-closed cube contains the point. This section proves the convergence
`f_h(x_h(s)) → f(s)` for almost every `s` that the argument rests on. -/

/-- The lattice point of `hℤ^d` whose half-closed cube contains `s`. -/
noncomputable def stepIndex (d : ℕ) (h : ℝ) (s : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (round (s i / h) : ℝ) * h)

lemma stepIndex_mem_scaledLattice {h : ℝ} (s : EuclideanSpace ℝ (Fin d)) :
    stepIndex d h s ∈ scaledLattice d h :=
  fun i => ⟨round (s i / h), rfl⟩

lemma mem_halfClosedCube_stepIndex {h : ℝ} (hh : 0 < h)
    (s : EuclideanSpace ℝ (Fin d)) : s ∈ halfClosedCube h (stepIndex d h s) := by
  intro i
  have hc : (stepIndex d h s) i = (round (s i / h) : ℝ) * h := rfl
  rw [Set.mem_Ico, hc, round_eq]
  have h1 : ((⌊s i / h + 1 / 2⌋ : ℤ) : ℝ) ≤ s i / h + 1 / 2 := Int.floor_le _
  have h2 : s i / h + 1 / 2 < (⌊s i / h + 1 / 2⌋ : ℤ) + 1 := Int.lt_floor_add_one _
  have h3 : s i = (s i / h) * h := by field_simp
  constructor <;> nlinarith [h1, h2, h3.le, h3.ge]

lemma halfClosedCube_subset_closedCube {h : ℝ} (hh : 0 ≤ h)
    (u : EuclideanSpace ℝ (Fin d)) : halfClosedCube h u ⊆ closedCube h u := by
  intro x hx
  rw [closedCube_eq_iInter hh]
  intro T hT
  obtain ⟨i, rfl⟩ := Set.mem_range.mp hT
  exact ⟨(hx i).1, le_of_lt (hx i).2⟩

lemma mem_closedCube_stepIndex {h : ℝ} (hh : 0 < h)
    (s : EuclideanSpace ℝ (Fin d)) : s ∈ closedCube h (stepIndex d h s) :=
  halfClosedCube_subset_closedCube hh.le _ (mem_halfClosedCube_stepIndex hh s)

/-- **The convergence Section 3.2 rests on.** For almost every `s`, the averages
of `φ` over the cubes of the tiling that contain `s` converge to `φ(s)`. -/
theorem tendsto_avg_stepIndex {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : LocallyIntegrable φ volume) :
    ∀ᵐ s : EuclideanSpace ℝ (Fin d),
      ∀ {ι : Type} {l : Filter ι} (hn : ι → ℝ), (∀ i, 0 < hn i) →
        Tendsto hn l (𝓝 0) →
        Tendsto (fun i => ⨍ y in closedCube (hn i) (stepIndex d (hn i) s), φ y) l (𝓝 (φ s)) := by
  filter_upwards [lemma_lebesgue_diff hφ] with s hs ι l hn hpos hlim
  exact hs hn (fun i => stepIndex d (hn i) s) hpos hlim
    (fun i => mem_closedCube_stepIndex (hpos i) s)

/-- The paper's `f_h` restricts the integral to `B*`; for `s` in the interior of
`B*` that makes no difference in the limit, since the cubes eventually lie inside
`B*`. -/
theorem tendsto_avg_stepIndex_indicator {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : LocallyIntegrable φ volume) (S : Set (EuclideanSpace ℝ (Fin d))) :
    ∀ᵐ s : EuclideanSpace ℝ (Fin d), s ∈ interior S →
      ∀ {ι : Type} {l : Filter ι} (hn : ι → ℝ), (∀ i, 0 < hn i) →
        Tendsto hn l (𝓝 0) →
        Tendsto (fun i => ⨍ y in closedCube (hn i) (stepIndex d (hn i) s),
          S.indicator φ y) l (𝓝 (φ s)) := by
  filter_upwards [tendsto_avg_stepIndex hφ] with s hs hsS ι l hn hpos hlim
  -- the cubes eventually lie inside `S`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior s hsS
  have hsd : (0:ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hlim' : Tendsto (fun i => hn i * Real.sqrt d) l (𝓝 0) := by
    simpa using hlim.mul_const (Real.sqrt d)
  have hev : ∀ᶠ i in l, closedCube (hn i) (stepIndex d (hn i) s) ⊆ S := by
    filter_upwards [hlim' (Iio_mem_nhds hε)] with i hi
    refine fun y hy => interior_subset (hball ?_)
    have h1 := closedCube_subset_closedBall_of_mem (mem_closedCube_stepIndex (hpos i) s) hy
    rw [Metric.mem_closedBall] at h1
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt h1 hi
  refine Tendsto.congr' ?_ (hs hn hpos hlim)
  filter_upwards [hev] with i hi
  refine (average_congr ?_).symm
  filter_upwards [ae_restrict_mem (measurableSet_closedCube (hpos i).le _)] with y hy
  exact Set.indicator_of_mem (hi hy) φ

/-! ## Integrating a step function over the tiling

The other half of Section 3.2's bookkeeping: a function constant on each tile
integrates to the sum of its values times `h^d`. Indexing the tiles by
`Fin d → ℤ` rather than by the lattice as a subset keeps the index type
countable on the nose. -/

/-- The point `h·n` of `hℤ^d`. -/
noncomputable def latticePt (d : ℕ) (h : ℝ) (n : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (n i : ℝ) * h)

lemma latticePt_mem_scaledLattice (h : ℝ) (n : Fin d → ℤ) :
    latticePt d h n ∈ scaledLattice d h := fun i => ⟨n i, rfl⟩

lemma latticePt_injective {h : ℝ} (hh : h ≠ 0) :
    Function.Injective (latticePt d h) := by
  intro n m hnm
  funext i
  have hc : ∀ p : Fin d → ℤ, (latticePt d h p) i = (p i : ℝ) * h := fun _ => rfl
  have := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) hnm
  rw [hc, hc] at this
  have : (n i : ℝ) = (m i : ℝ) := by
    field_simp at this
    tauto
  exact_mod_cast this

lemma halfClosedCube_eq_preimage (h : ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    halfClosedCube h u = (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ)) ⁻¹'
      (Set.pi Set.univ (fun i => Ico (u i - h / 2) (u i + h / 2))) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_univ_pi, halfClosedCube, Set.mem_ofPred_eq]

lemma measurableSet_halfClosedCube (h : ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    MeasurableSet (halfClosedCube h u) := by
  rw [halfClosedCube_eq_preimage]
  exact (PiLp.volume_preserving_ofLp (Fin d)).measurable
    (MeasurableSet.univ_pi (fun _ => measurableSet_Ico))

lemma volume_halfClosedCube {h : ℝ} (hh : 0 ≤ h) (u : EuclideanSpace ℝ (Fin d)) :
    volume (halfClosedCube h u) = ENNReal.ofReal (h ^ d) := by
  rw [halfClosedCube_eq_preimage,
    MeasurePreserving.measure_preimage (PiLp.volume_preserving_ofLp (Fin d))
    (MeasurableSet.univ_pi (fun _ => measurableSet_Ico)).nullMeasurableSet, volume_pi_pi]
  have hfac : ∀ i : Fin d, volume (Ico (u i - h / 2) (u i + h / 2)) = ENNReal.ofReal h := by
    intro i
    rw [Real.volume_Ico]
    congr 1
    ring
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← ENNReal.ofReal_pow hh]

/-- The tile containing `s` is the one indexed by `stepIndex`. -/
lemma stepIndex_eq_of_mem {h : ℝ} (hh : 0 < h) {x s : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ scaledLattice d h) (hs : s ∈ halfClosedCube h x) : stepIndex d h s = x := by
  obtain ⟨w, -, huniq⟩ := existsUnique_mem_halfClosedCube (d := d) hh s
  rw [huniq (stepIndex d h s) ⟨stepIndex_mem_scaledLattice s, mem_halfClosedCube_stepIndex hh s⟩,
    huniq x ⟨hx, hs⟩]

lemma iUnion_halfClosedCube {h : ℝ} (hh : 0 < h) :
    (⋃ n : Fin d → ℤ, halfClosedCube h (latticePt d h n)) = Set.univ := by
  refine Set.eq_univ_of_forall (fun s => ?_)
  refine Set.mem_iUnion.mpr ⟨fun i => round (s i / h), ?_⟩
  have he : latticePt d h (fun i => round (s i / h)) = stepIndex d h s := rfl
  rw [he]
  exact mem_halfClosedCube_stepIndex hh s

lemma pairwiseDisjoint_halfClosedCube {h : ℝ} (hh : 0 < h) :
    Pairwise (Function.onFun Disjoint
      (fun n : Fin d → ℤ => halfClosedCube h (latticePt d h n))) := by
  intro n m hnm
  refine Set.disjoint_left.mpr (fun s hsn hsm => ?_)
  have h1 := stepIndex_eq_of_mem hh (latticePt_mem_scaledLattice h n) hsn
  have h2 := stepIndex_eq_of_mem hh (latticePt_mem_scaledLattice h m) hsm
  exact hnm (latticePt_injective (ne_of_gt hh) (h1.symm.trans h2))

/-- The integral over `ℝ^d` splits along the tiling. -/
theorem lintegral_eq_tsum_halfClosedCube {h : ℝ} (hh : 0 < h)
    (F : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    ∫⁻ s, F s = ∑' n : Fin d → ℤ, ∫⁻ s in halfClosedCube h (latticePt d h n), F s := by
  rw [← setLIntegral_univ F, ← iUnion_halfClosedCube (d := d) hh,
    lintegral_iUnion (fun n => measurableSet_halfClosedCube h (latticePt d h n))
      (pairwiseDisjoint_halfClosedCube hh)]

/-- **A step function integrates to the sum of its values times `h^d`.** This is
the identity Section 3.2 uses to turn the discrete sums of Corollary 3.1 into
integrals. -/
theorem lintegral_stepFun {h : ℝ} (hh : 0 < h)
    (c : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    ∫⁻ s, c (stepIndex d h s)
      = ∑' n : Fin d → ℤ, c (latticePt d h n) * ENNReal.ofReal (h ^ d) := by
  rw [lintegral_eq_tsum_halfClosedCube hh]
  refine tsum_congr (fun n => ?_)
  have hcongr : ∀ s ∈ halfClosedCube h (latticePt d h n),
      c (stepIndex d h s) = c (latticePt d h n) := by
    intro s hs
    rw [stepIndex_eq_of_mem hh (latticePt_mem_scaledLattice h n) hs]
  rw [setLIntegral_congr_fun (measurableSet_halfClosedCube h (latticePt d h n)) hcongr,
    setLIntegral_const, volume_halfClosedCube hh.le]

end QFS
