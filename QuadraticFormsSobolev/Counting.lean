/-
Counting lattice points, for Theorem 5.15: an upper bound for balls that is
uniform in the centre, a lower bound for blocks, and the pigeonhole giving the
size of a majority set.
-/
import QuadraticFormsSobolev.Renormalization

open Real Set Metric

namespace QFS

variable {d : ℕ}

/-- Coordinates determine a point of `ℝ^d`. -/
lemma euclidean_ext {x y : EuclideanSpace ℝ (Fin d)} (h : ∀ i, x i = y i) : x = y := by
  have he : WithLp.ofLp x = WithLp.ofLp y := funext h
  have := congrArg (WithLp.toLp (2 : ENNReal)) he
  simpa using this

/-- The coordinate map `x ↦ (round (x i))ᵢ` is injective on the lattice. -/
lemma round_injOn_lattice :
    Set.InjOn (fun (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) => round (x i)) (lattice d) := by
  intro x hx y hy hxy
  refine euclidean_ext (fun i => ?_)
  obtain ⟨n, hn⟩ := (mem_lattice_iff.mp hx) i
  obtain ⟨m, hm⟩ := (mem_lattice_iff.mp hy) i
  have hnm : n = m := by
    have h := congrFun hxy i
    simp only [hn, hm, round_intCast] at h
    exact h
  rw [hn, hm, hnm]

/-! ## Upper bound for balls -/

/-- **A ball of radius `M` contains at most `(2⌈M⌉ + 1)^d` lattice points**, a
bound independent of the centre. -/
theorem encard_lattice_inter_closedBall_le (a : EuclideanSpace ℝ (Fin d)) (M : ℝ) :
    (lattice d ∩ closedBall a M).encard ≤ (((2 * ⌈M⌉₊ + 1) ^ d : ℕ) : ℕ∞) := by
  classical
  set F : Finset (Fin d → ℤ) :=
    Fintype.piFinset (fun i => Finset.Icc ⌈a i - M⌉ ⌊a i + M⌋) with hF
  have hinj : Set.InjOn (fun (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) => round (x i))
      (lattice d ∩ closedBall a M) := round_injOn_lattice.mono Set.inter_subset_left
  have hsub : (fun (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) => round (x i)) ''
      (lattice d ∩ closedBall a M) ⊆ (F : Set (Fin d → ℤ)) := by
    rintro _ ⟨x, ⟨hxlat, hxb⟩, rfl⟩
    rw [hF, Finset.mem_coe]
    refine Fintype.mem_piFinset.mpr (fun i => ?_)
    obtain ⟨n, hn⟩ := (mem_lattice_iff.mp hxlat) i
    have hround : round (x i) = n := by rw [hn]; simp
    rw [Metric.mem_closedBall, dist_eq_norm] at hxb
    have hcoord : |x i - a i| ≤ M := by
      have h := abs_coord_le_norm (x - a) i
      have he : (x - a) i = x i - a i := by simp
      rw [he] at h
      linarith
    rw [abs_le] at hcoord
    simp only [hround]
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · rw [Int.ceil_le, ← hn]; linarith [hcoord.1]
    · rw [Int.le_floor, ← hn]; linarith [hcoord.2]
  have hcard : F.card ≤ (2 * ⌈M⌉₊ + 1) ^ d := by
    rw [hF, Fintype.card_piFinset]
    calc ∏ i : Fin d, (Finset.Icc ⌈a i - M⌉ ⌊a i + M⌋).card
        ≤ ∏ _i : Fin d, (2 * ⌈M⌉₊ + 1) := by
          refine Finset.prod_le_prod' (fun i _ => ?_)
          rw [Int.card_Icc]
          have hfl : (⌊a i + M⌋ : ℝ) ≤ a i + M := Int.floor_le _
          have hce : a i - M ≤ (⌈a i - M⌉ : ℝ) := Int.le_ceil _
          have hM' : M ≤ (⌈M⌉₊ : ℝ) := Nat.le_ceil M
          have hcast : ((⌊a i + M⌋ + 1 - ⌈a i - M⌉ : ℤ) : ℝ)
              ≤ ((2 * ⌈M⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
          have h1 : (⌊a i + M⌋ + 1 - ⌈a i - M⌉ : ℤ) ≤ ((2 * ⌈M⌉₊ + 1 : ℕ) : ℤ) := by
            exact_mod_cast hcast
          omega
      _ = (2 * ⌈M⌉₊ + 1) ^ d := by simp
  calc (lattice d ∩ closedBall a M).encard
      = ((fun (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) => round (x i)) ''
          (lattice d ∩ closedBall a M)).encard := (Set.InjOn.encard_image hinj).symm
    _ ≤ (F : Set (Fin d → ℤ)).encard := Set.encard_mono hsub
    _ = (F.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard F
    _ ≤ (((2 * ⌈M⌉₊ + 1) ^ d : ℕ) : ℕ∞) := by exact_mod_cast hcard


/-! ## Lower bound for blocks -/

/-- **A block of integer side `ℓ` centred at a lattice point contains at least
`ℓ^d` lattice points.** This is the count behind the size `Δ^{d(n-1)}/L` of the
majority sets in the proof of Theorem 5.15. -/
theorem le_encard_block {ℓ : ℕ} {c : EuclideanSpace ℝ (Fin d)} (hc : c ∈ lattice d) :
    (((ℓ ^ d : ℕ)) : ℕ∞) ≤ (block (ℓ : ℝ) c).encard := by
  classical
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, k = ℓ / 2 := ⟨_, rfl⟩
  have hk : 2 * k ≤ ℓ ∧ ℓ ≤ 2 * k + 1 := by omega
  set S : Finset (Fin d → ℤ) := Fintype.piFinset (fun _ => Finset.Ico (0 : ℤ) (ℓ : ℤ)) with hS
  set g : (Fin d → ℤ) → EuclideanSpace ℝ (Fin d) := fun s =>
    WithLp.toLp 2 (fun i => c i + ((s i : ℤ) : ℝ) - ((k : ℕ) : ℝ)) with hg
  have hgcoord : ∀ (s : Fin d → ℤ) (i : Fin d),
      (g s) i = c i + ((s i : ℤ) : ℝ) - ((k : ℕ) : ℝ) := fun s i => rfl
  have hginj : Set.InjOn g (S : Set (Fin d → ℤ)) := by
    intro s _ t _ hst
    funext i
    have h : (g s) i = (g t) i := by rw [hst]
    rw [hgcoord, hgcoord] at h
    have hreal : ((s i : ℤ) : ℝ) = ((t i : ℤ) : ℝ) := by linarith
    exact_mod_cast hreal
  have hgmem : ∀ s ∈ (S : Set (Fin d → ℤ)), g s ∈ block (ℓ : ℝ) c := by
    intro s hs
    rw [Finset.mem_coe, hS, Fintype.mem_piFinset] at hs
    refine ⟨?_, ?_⟩
    · rw [mem_lattice_iff]
      intro i
      obtain ⟨n, hn⟩ := (mem_lattice_iff.mp hc) i
      refine ⟨n + s i - (k : ℤ), ?_⟩
      rw [hgcoord, hn]
      push_cast
      ring
    · refine infNorm_le (by positivity) (fun i => ?_)
      have hsi := Finset.mem_Ico.mp (hs i)
      have hlo : (0 : ℝ) ≤ ((s i : ℤ) : ℝ) := by exact_mod_cast hsi.1
      have hhi : ((s i : ℤ) : ℝ) ≤ ((ℓ : ℤ) : ℝ) - 1 := by
        have : (s i : ℤ) ≤ (ℓ : ℤ) - 1 := by omega
        exact_mod_cast this
      have hk1 : (2 : ℝ) * ((k : ℕ) : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hk.1
      have hk2 : (ℓ : ℝ) ≤ 2 * ((k : ℕ) : ℝ) + 1 := by exact_mod_cast hk.2
      have hcoord : (g s - c) i = ((s i : ℤ) : ℝ) - ((k : ℕ) : ℝ) := by
        have he : (g s - c) i = (g s) i - c i := by simp
        rw [he, hgcoord]
        ring
      rw [hcoord, abs_le]
      push_cast at hhi ⊢
      constructor <;> linarith
  have hScard : S.card = ℓ ^ d := by
    rw [hS, Fintype.card_piFinset]
    simp
  calc (((ℓ ^ d : ℕ)) : ℕ∞) = (S.card : ℕ∞) := by rw [hScard]
    _ = ((S : Set (Fin d → ℤ)).encard) := (Set.encard_coe_eq_coe_finsetCard S).symm
    _ = (g '' (S : Set (Fin d → ℤ))).encard := (Set.InjOn.encard_image hginj).symm
    _ ≤ (block (ℓ : ℝ) c).encard := Set.encard_mono (by rintro _ ⟨s, hs, rfl⟩; exact hgmem s hs)


/-- **Lower bound for balls**: a ball of radius `R` about a lattice point contains
at least `ℓ^d` lattice points whenever the cube of side `ℓ` fits inside it, that
is when `ℓ√d/2 ≤ R`. With `encard_lattice_inter_closedBall_le` this is the
paper's `#(B_R ∩ ℤ^d) ≍ R^d`. -/
theorem le_encard_lattice_inter_closedBall {ℓ : ℕ} {R : ℝ}
    {c : EuclideanSpace ℝ (Fin d)} (hc : c ∈ lattice d)
    (hR : (ℓ : ℝ) / 2 * Real.sqrt d ≤ R) :
    (((ℓ ^ d : ℕ)) : ℕ∞) ≤ (lattice d ∩ closedBall c R).encard := by
  refine le_trans (le_encard_block hc) (Set.encard_mono ?_)
  rintro x ⟨hxlat, hxcube⟩
  exact ⟨hxlat, closedBall_subset_closedBall hR
    (closedCube_subset_closedBall (by positivity) c hxcube)⟩

/-! ## The size of a majority set -/

/-- **Pigeonhole for majority sets.** If a configuration realises at most `L`
cones on a finite block `Q`, then a cone favored by majority in `Q` is carried by
at least `#Q / L` of its points.

This is the paper's "each block `Q_{Δⁿ⁻¹}(x)` contains at least `Δ^{d(n-1)}/L`
lattice points where the associated cone is favored by majority": combined with
`le_encard_block` it gives the size `a` of the majority sets used in Step 2 of the
proof of Theorem 5.15. -/
theorem ncard_le_mul_ncard_blockFibre {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {Q : Set (EuclideanSpace ℝ (Fin d))} (hQfin : Q.Finite)
    {V : DCone (EuclideanSpace ℝ (Fin d))} (hV : FavoredIn Γ Q V)
    {L : ℕ} (hL : (Γ '' Q).ncard ≤ L) :
    Q.ncard ≤ L * (blockFibre Γ Q V).ncard := by
  classical
  have hVfin : (blockFibre Γ Q V).Finite := hQfin.subset (fun _ h => h.1)
  -- the favoured fibre dominates every other fibre, in `ncard`
  have hdom : ∀ W : DCone (EuclideanSpace ℝ (Fin d)),
      (blockFibre Γ Q W).ncard ≤ (blockFibre Γ Q V).ncard := by
    intro W
    have hWfin : (blockFibre Γ Q W).Finite := hQfin.subset (fun _ h => h.1)
    have := hV W
    rw [← hWfin.cast_ncard_eq, ← hVfin.cast_ncard_eq] at this
    exact_mod_cast this
  -- split `Q` into the fibres of `Γ`
  set s : Finset (EuclideanSpace ℝ (Fin d)) := hQfin.toFinset with hs
  set t : Finset (DCone (EuclideanSpace ℝ (Fin d))) := s.image (fun x => Γ x) with ht
  have hfib : s.card = ∑ W ∈ t, (s.filter fun x => Γ x = W).card :=
    Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image_of_mem _ hx)
  have hstep : ∀ W ∈ t, (s.filter fun x => Γ x = W).card ≤ (blockFibre Γ Q V).ncard := by
    intro W _
    refine le_trans ?_ (hdom W)
    have hsub : ((s.filter fun x => Γ x = W) : Set (EuclideanSpace ℝ (Fin d)))
        ⊆ blockFibre Γ Q W := by
      intro x hx
      rw [Finset.mem_coe, Finset.mem_filter, hs, Set.Finite.mem_toFinset] at hx
      exact ⟨hx.1, by rw [hx.2]⟩
    have := Set.ncard_le_ncard hsub (hQfin.subset (fun _ h => h.1))
    rwa [Set.ncard_coe_finset] at this
  have hQs : Q.ncard = s.card := by
    rw [hs, ← Set.ncard_coe_finset, hQfin.coe_toFinset]
  have htL : t.card ≤ L := by
    have : (Γ '' Q).ncard = t.card := by
      rw [ht, hs]
      rw [← Set.ncard_coe_finset]
      congr 1
      ext W
      simp
    omega
  calc Q.ncard = ∑ W ∈ t, (s.filter fun x => Γ x = W).card := by rw [hQs, hfib]
    _ ≤ ∑ _W ∈ t, (blockFibre Γ Q V).ncard := Finset.sum_le_sum hstep
    _ = t.card * (blockFibre Γ Q V).ncard := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ L * (blockFibre Γ Q V).ncard := Nat.mul_le_mul_right _ htL

end QFS
