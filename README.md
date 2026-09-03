# quadratic-forms-sobolev

A Lean 4 / Mathlib formalisation of parts of

> Kai-Uwe Bux, Moritz Kassmann and Tim Schulze,
> *Quadratic forms and Sobolev spaces of fractional order*,
> [arXiv:1707.09277](https://arxiv.org/abs/1707.09277).

The paper studies quadratic forms on `L²(ℝ^d)` in which a difference
`f(y) − f(x)` is only counted when `y` lies in a double cone `V^Γ[x]` with apex
at `x`. Its main results (Theorems 1.1 and 1.3) say that the resulting seminorm
is nevertheless comparable to the full `H^{α/2}` seminorm, in the continuous and
in the discrete setting.

## Scope

The paper's main theorems rest on a long chaining-and-renormalisation argument
(Sections 5 and 6) on top of a layer of point-set geometry and graph theory
(Sections 2, 3 and 4). **This repository formalises that lower layer**: the
function-space set-up of Section 1 (including equation (1.6)), the full
definitional set-up of Section 2, the geometric lemmas of Sections 2 and 3, the
whole of Section 4 — the paper's "continuous prelude", whose main result,
**Theorem 4.1**, is proved here (`QFS.cont_connectivity`) — and Section 5's
auxiliary results, Lemmas 5.1–5.6, the quantitative discrete counterparts of the
Section 4 lemmas. The paper's main theorems (1.1 and 1.3) are recorded as
type-checked `Prop`s, so what remains to be proved is stated precisely. See
*Not attempted* below for what is deliberately left out.

Along the way the formalisation turned up four defects in the paper; all are
recorded under *Deviations*, and two of them are accompanied by Lean proofs that
the statement as printed is false:

* **Lemma 3.4** is stated for `x, y ∈ ℤ^d` but is only true for `x, y ∈ hℤ^d`,
  which is what its own "follows by scaling" argument gives
  (`QFS.lemma_cubes_literal_false`).
* **Lemma 3.3** is false in dimension one at the radius `r = √d` at which
  Proposition 3.5 uses it (`QFS.lemma_new_config_false_dim_one`).
* **Lemma 4.6** needs a hypothesis `z ∈ U` that is not stated.
* **Theorem 4.1**'s induction is applied to a set that need not be connected;
  the repair is to run it on `B_r(x) ∩ Ṽ[x]` with the half-cone.
* **Lemma 5.6** is called obvious, but the obvious argument (stepping radially
  toward the tip) does not work; see *Deviations* 11.

## Coverage: every numbered result in the paper

One row per numbered statement, including the ones not attempted. ✅ proved,
❗ disproved as printed, ⚪ prose remark with nothing to prove, ❌ out of scope.

| # | Kind | Label | State |
| --- | --- | --- | --- |
| 1.1 | Theorem | main comparability, continuous | ⚪ statement recorded (`QFS.TheoremOneOne`), not proved |
| 1.2 | Remark | strength of the hypotheses | ⚪ (condition (M) is `QFS.CondM`) |
| 1.3 | Theorem | main comparability, discrete | ⚪ statement recorded (`QFS.TheoremOneThree`), not proved |
| 1.4 | Theorem | `H_k(Ω) = H^{α/2}(Ω)` | ❌ out of scope |
| 1.5 | Corollary | regular Dirichlet form | ❌ out of scope |
| 1.6 | Corollary | Harnack / Hölder regularity | ❌ out of scope (quoted from [DyKa15]) |
| 2.1 | Definition | cones, half-cones, configurations | ✅ |
| 2.2 | Lemma | finitely many reference cones | ✅ |
| 2.3 | Definition | family of reference cones | ✅ |
| 2.4 | Corollary | finite-image subconfiguration | ✅ |
| 2.5 | Definition | cubes | ✅ |
| 2.6 | Remark | half-closed cubes used once | ⚪ |
| 2.7 | Lemma | cone in intersection | ✅ |
| 3.1 | Corollary | `hℤ^d` rescaling | ❌ out of scope |
| 3.2 | Lemma | the indicator inequality | ✅ |
| 3.3 | Lemma | small cone inside `V^m_r` | ❗ **false for `d = 1`, `r = √d`** |
| 3.4 | Lemma | `\|s−t\|` vs `\|x−y\|` | ✅ for `hℤ^d`; ❗ **false as printed** |
| 3.5 | Proposition | test-function bound | ❌ out of scope (uses 3.3) |
| 3.6 | Corollary | the rescaled kernel | ❌ out of scope |
| 3.7 | Lemma | `H_k` on balls | ❌ out of scope |
| 4.1 | Theorem | **connectivity of `G[U]`** | ✅ **proved** |
| 4.2 | Definition | type of a point | ✅ |
| 4.3 | Lemma | same type ⟹ path of length ≤ 2 | ✅ |
| 4.4 | Definition | well-connected in `U` | ✅ |
| 4.5 | Lemma | three observations | ✅ (all three parts) |
| 4.6 | Lemma | "über Bande" | ✅ (needs an unstated `z ∈ U`) |
| 5.1 | Lemma | lattice points in cones | ✅ |
| 5.2 | Corollary | discrete same-type | ✅ |
| 5.3 | Definition | `r`-`R`-connected | ✅ |
| 5.4 | Lemma | density, discrete | ✅ |
| 5.5 | Lemma | "über Bande", discrete | ✅ |
| 5.6 | Lemma | the jump constant `δ` | ✅ |
| 5.7 | Lemma | the core induction | ⚪ statement recorded (`QFS.CoreInduction`); base case `k = 1` proved |
| 5.8 | Corollary | discrete template | ❌ out of scope |
| 5.9 | Lemma | apex shrinking | ❌ out of scope |
| 5.10 | Definition | towns | ❌ out of scope |
| 5.11 | Definition | town configurations | ❌ out of scope |
| 5.12 | Remark | — | ❌ out of scope |
| 5.13 | Definition | scales | ❌ out of scope |
| 5.14 | Proposition | renormalisation | ❌ out of scope |
| 5.15 | Theorem | path properties | ❌ out of scope |
| 5.16 | Lemma | the first jump | ❌ out of scope |
| 7.1 | Lemma | auxiliary integral estimate | ❌ out of scope |
| 7.2 | Lemma | a Lebesgue differentiation argument | ❌ out of scope |

Sections 2 and 4 are formalised completely, as is Section 5's auxiliary
subsection (Lemmas 5.1–5.5). Section 3 is formalised as far as it can be without
the machinery of Sections 5 and 6 (Lemma 3.3, which Proposition 3.5 needs, is
false as stated). From Section 1, the function-space definitions, assumption
(1.4), the reverse inequality and equation (1.6) are proved, and Theorems 1.1
and 1.3 are recorded as type-checked `Prop`s so the remaining target is precise.
Lemma 5.7 (the core induction, 185 lines of dense argument), the renormalisation
machinery of Lemmas 5.8–5.16, and Section 6 remain a project in their own
right.

## What is proved, in detail


| Result | Paper | Lean | State |
| --- | --- | --- | --- |
| Cone `Ṽ(v,ϑ)`, double cone `V(v,ϑ)` | Def. 2.1 | `QFS.cone`, `QFS.doubleCone` | ✅ defined |
| Cones are open | Def. 2.1 (used in §4) | `QFS.isOpen_cone`, `QFS.isOpen_doubleCone` | ✅ proved |
| Angle description of a cone | Def. 2.1 | `QFS.mem_cone_iff_angle` | ✅ proved |
| Double half-cone `V_r` | Def. 2.1 | `QFS.shrink`, `QFS.doubleHalfCone` | ✅ defined |
| Shifted cone `V[x]`, `V^Γ[x]` | Def. 2.1 | `QFS.shift`, `QFS.coneAt` | ✅ defined |
| The family `𝒱`; configurations | Def. 2.1 | `QFS.DCone`, `QFS.Configuration` | ✅ defined |
| `ϑ`-bounded, condition (M), `ϑ`-admissible | Def. 2.1 | `QFS.IsBounded`, `QFS.CondM`, `QFS.IsAdmissible` | ✅ defined |
| Open cube `A_h(u)`, half-closed `Ã_h(u)` | Def. 2.5 | `QFS.cube`, `QFS.halfClosedCube` | ✅ defined |
| Max norm `‖·‖_∞`; `‖v‖_∞ ≤ ‖v‖ ≤ √d ‖v‖_∞` | eq. (3.1) | `QFS.infNorm_le_norm`, `QFS.norm_le_sqrt_dim_mul_infNorm` | ✅ proved |
| `A_h(x) ⊆ B̄_{(h/2)√d}(x)` | Lem. 2.7 (last step) | `QFS.cube_subset_closedBall` | ✅ proved |
| Eq. (⋆): `V_ℓ = ⋂_{ξ∈B̄_ℓ} V[ξ]` | Lem. 2.7 proof | `QFS.shrink_eq_iInter_shift` | ✅ proved |
| Eq. (✝): `⋃_{ξ∈B̄_ℓ} V_{2ℓ}[ξ] ⊆ V_ℓ` | Lem. 2.7 proof | `QFS.iUnion_shift_shrink_subset` | ✅ proved |
| `V_{2ℓ}[ξ] ⊆ V_ℓ[x] ⊆ V[ξ]` for `ξ ∈ B̄_ℓ(x)` | Lem. 2.7 proof | `QFS.shift_shrink_sandwich` | ✅ proved |
| **Lemma 2.7**: cone in intersection | Lem. 2.7 | `QFS.cone_in_intersection`, `QFS.cone_in_intersection'` | ✅ **proved** |
| Angle between lines; triangle inequality | Lem. 2.2 proof | `QFS.dangle`, `QFS.dangle_triangle` | ✅ proved |
| `w ∈ V(v,θ)`, `2θ ≤ ϑ` ⟹ `V(v,θ) ⊆ V(w,ϑ)` | Lem. 2.2 proof | `QFS.doubleCone_subset_of_axis_mem` | ✅ proved |
| Finite subcover of `S^{d-1}` by cones | Lem. 2.2 proof | `QFS.exists_finite_axes` | ✅ proved |
| **Lemma 2.2**: finitely many reference cones | Lem. 2.2 | `QFS.ref_cones` | ✅ **proved** |
| Family of reference cones, `V^m_r`, `V^m_r[x]` | Def. 2.3 | `QFS.RefFamily`, `.shrunk`, `.shrunkAt` | ✅ defined |
| **Corollary 2.4**: finite-image subconfiguration | Cor. 2.4 | `QFS.ref_config` | ✅ **proved** |
| Lattices `ℤ^d`, `hℤ^d` | §3 | `QFS.lattice`, `QFS.scaledLattice` | ✅ defined |
| `‖·‖_∞` triangle inequality, sup attained | eq. (3.1) | `QFS.infNorm_add_le`, `QFS.exists_infNorm_eq` | ✅ proved |
| `‖x−y‖_∞ > h` ⟹ `≥ 2h` on `hℤ^d` | Lem. 3.4 proof | `QFS.two_mul_le_infNorm_sub` | ✅ proved |
| **Lemma 3.4**: `|s−t|` vs `|x−y|` | Lem. 3.4 | `QFS.lemma_cubes` | ✅ **proved** (corrected, see below) |
| Lemma 3.4 as literally stated is false | Lem. 3.4 | `QFS.lemma_cubes_literal_false` | ✅ **disproved** |
| `A_h^m(u)`; `h`-favoured index by majority | §3 | `QFS.cubeCone`, `QFS.IsFavoured` | ✅ defined |
| `A_h(u) = ⋃_i A_h^i(u)` | §3 | `QFS.cube_eq_biUnion_cubeCone` | ✅ proved |
| `λ_d(A_h^m(u)) ≥ L⁻¹ λ_d(A_h(u))` | §3 | `QFS.volume_cube_le_card_mul` | ✅ proved |
| **Lemma 3.2**: the indicator inequality | Lem. 3.2 | `QFS.lemma_min_dist`, `QFS.lemma_min_dist_favoured` | ✅ **proved** |
| **Lemma 3.3** fails in `d = 1` for `r = √d` | Lem. 3.3 | `QFS.lemma_new_config_false_dim_one` | ✅ **disproved** (`d=1`) |
| Ball inside a cone: `‖u − tv‖ < t sin ϑ ⟹ u ∈ Ṽ` | §4–5 (implicit) | `QFS.mem_cone_of_norm_sub_lt` | ✅ proved |
| Cones of apex `≤ π/2` are convex | (new; used for §4) | `QFS.convex_cone` | ✅ proved |
| `V[x] ∩ V[y] ≠ ∅` for one double cone | Lem. 4.3 proof | `QFS.shift_inter_shift_nonempty` | ✅ proved |
| The graph `G[U]`; undirected connectivity | §4 | `QFS.Edge`, `QFS.Conn` | ✅ defined |
| Type of a point | Def. 4.2 | `Γ x = Γ y` | ✅ defined |
| **Lemma 4.3**: same type ⟹ path of length ≤ 2 | Lem. 4.3 | `QFS.connect_two_of_same_type` | ✅ **proved** |
| Well-connected in `U` | Def. 4.4 | `QFS.WellConnected` | ✅ defined |
| **Lemma 4.5 (1)** | Lem. 4.5 | `QFS.wellConnected_of_mem_coneAt` | ✅ **proved** |
| **Lemma 4.5 (2)** | Lem. 4.5 | `QFS.wellConnected_mono`, `QFS.Conn.mono` | ✅ **proved** |
| **Lemma 4.5 (3)**: existence and density | Lem. 4.5 | `QFS.exists_wellConnected`, `QFS.wellConnected_dense` | ✅ **proved** |
| **Lemma 4.6** ("über Bande") | Lem. 4.6 | `QFS.ueber_bande` | ✅ **proved** |
| The constant `λ = (sin ϑ)/2` | Thm. 4.1 proof | `QFS.exists_mem_ball_inter_shift`, `'` | ✅ proved |
| Connectivity is monotone in `Γ` | Thm. 4.1 proof (WLOG) | `QFS.Conn.mono_config` | ✅ proved |
| Open classes + preconnected `U` ⟹ one class | Thm. 4.1, last step | `QFS.conn_of_wellConnected_of_isPreconnected` | ✅ proved |
| The induction on the number of cone types | Thm. 4.1 proof | `QFS.conn_of_isPreconnected_of_finite` | ✅ proved |
| **Theorem 4.1**: connectivity of `G[U]` | Thm. 4.1 | `QFS.cont_connectivity` | ✅ **proved** |
| Kernel `\|x−y\|^{-d-α}`; the quadratic form | §1 | `QFS.jumpKernel`, `QFS.form`, `QFS.formHs` | ✅ defined |
| Assumption (1.4) on `k`; discrete (1.7) on `ω` | eq. (1.4), (1.7) | `QFS.KernelBounds`, `QFS.DiscreteKernelBounds` | ✅ defined |
| `H_k(Ω)`, `H^{α/2}(Ω)` | §1 | `QFS.Hk`, `QFS.Hs` | ✅ defined |
| The "trivially true" reverse inequality of (1.5) | §1, after Thm. 1.1 | `QFS.form_le_formHs` | ✅ proved |
| **Equation (1.6)**: `H^{α/2}(Ω) ⊆ H_k(Ω)` | eq. (1.6) | `QFS.Hs_subset_Hk` | ✅ **proved** |
| Statement of Theorem 1.1 (with the `α`-uniform form) | Thm. 1.1 | `QFS.TheoremOneOne`, `QFS.TheoremOneOneUniform` | ⚪ stated, not proved |
| Statement of Theorem 1.3 | Thm. 1.3 | `QFS.discreteForm`, `QFS.TheoremOneThree` | ⚪ stated, not proved |
| Every `√d/2`-ball holds a lattice point | §5.1 preamble | `QFS.exists_lattice_mem_closedBall` | ✅ proved |
| Paths not leaving a set | Def. 5.3 | `QFS.ConnWithin` | ✅ defined |
| **Lemma 5.1 (1), (2)**: lattice points in cones | Lem. 5.1 | `QFS.exists_lattice_mem_cone`, `QFS.exists_lattice_mem_inter` | ✅ **proved** |
| **Corollary 5.2**: discrete same type | Cor. 5.2 | `QFS.discr_connect_two_of_same_type` | ✅ **proved** |
| `r`-`R`-connected | Def. 5.3 | `QFS.RRConnected` | ✅ defined |
| **Lemma 5.4**: discrete density | Lem. 5.4 | `QFS.exists_rrConnected` | ✅ **proved** |
| **Lemma 5.5**: discrete "über Bande" | Lem. 5.5 | `QFS.discr_ueber_bande` | ✅ **proved** |
| Signed distance to the cone boundary | (new; §§4–5 use it) | `QFS.coneGap` | ✅ defined |
| `p ∈ Ṽ ↔ gap > 0`; gap is `1`-Lipschitz | (new) | `QFS.mem_cone_iff_coneGap_pos`, `QFS.coneGap_sub_le` | ✅ proved |
| Ball of radius `< gap` sits in the cone | (new) | `QFS.closedBall_subset_cone` | ✅ proved |
| Axis step raises the gap by `a sin ϑ` | (new; key to Lem. 5.6) | `QFS.coneGap_add_smul_axis` | ✅ proved |
| **Lemma 5.6**: bounded jumps toward the tip | Lem. 5.6 | `QFS.exists_closer_lattice_nearby` | ✅ **proved** |
| Lattice points have integer squared norm | (new) | `QFS.exists_natCast_sq_norm` | ✅ proved |
| The descent principle | Lem. 5.6, "I.e." clause | `QFS.Jump`, `QFS.exists_min_of_jump` | ✅ proved |
| **Lemma 5.6 in full**, chain down to the tip | Lem. 5.6 | `QFS.exists_min_chain_in_cone` | ✅ **proved** |
| Points of large gap lie in the shrunk cone `Ṽ_ρ` | (new; needed by Lem. 5.7) | `QFS.mem_shrink_cone_of_lt_coneGap` | ✅ proved |
| **`Ṽ_ρ` is a half-cone with apex moved `ρ/sin ϑ` along the axis** | (new) | `QFS.coneGap_gt_eq_shift_cone`, `QFS.shift_cone_subset_shrink` | ✅ **proved** |
| Unconditional descent step toward the apex | (new; strengthens Lem. 5.6) | `QFS.exists_lattice_step_toward_apex` | ✅ proved |
| **Lemma 5.6 for a half-cone with arbitrary apex** | Lem. 5.6 (shifted) | `QFS.exists_closer_lattice_nearby_shift` | ✅ **proved** |
| Descent chain to the apex | Lem. 5.6, "I.e." (shifted) | `QFS.exists_chain_to_apex` | ✅ proved |
| **The jump statement and chain for a shrunk half-cone** | Lem. 5.7, step (2) | `QFS.exists_chain_to_apex_shrunk`, `QFS.shift_cone_apex_subset_shift_shrink` | ✅ **proved** |
| Cone types realised at the lattice points of a set | §5.2 | `QFS.typesIn` | ✅ defined |
| Statement of Lemma 5.7 | Lem. 5.7 | `QFS.CoreInduction` | ⚪ stated, not proved |
| **Lemma 5.7, base case `k = 1`** | Lem. 5.7 | `QFS.core_induction_base` | ✅ **proved** |

## Deviations

Each departure from the paper, and why.

1. **Lemma 2.7 is proved for an arbitrary set.** The paper states it for "a cone
   `V` with apex angle `ϑ`", but the proof it gives — equations (⋆) and (✝) —
   never uses that `V` is a cone, only that it is a subset of `ℝ^d`. The Lean
   proof follows the paper's argument verbatim; the statement it proves is
   therefore about an arbitrary `V : Set (EuclideanSpace ℝ (Fin d))`. The
   paper's own reading is the special case where `V` is a double cone.

2. **`ϑ`-boundedness is formalised as a positive lower bound.** Definition 2.1
   says `Γ` is `ϑ`-bounded when the *infimum* `ϑ` of the apex angles of `Γ(ℝ^d)`
   is positive. `QFS.IsBounded Γ ϑ` says `0 < ϑ` and `ϑ ≤ (Γ x).apex` for all
   `x`. These agree on what every later argument uses (a uniform positive lower
   bound), and avoid carrying an infimum that is never needed as such.

3. **Corollary 2.4: the apex angle of `Γ̃` is `ϑ/3`, not `ϑ`.** The corollary's
   last sentence reads "The minimum of apex angles of cones in `Γ̃(ℝ^d)` is
   `ϑ`". But `Γ̃` is built from the reference cones of Lemma 2.2, whose apex
   angle is `θ = ϑ/3`. `QFS.ref_config` proves `(Γ' x).apex = ϑ/3` and
   `IsBounded Γ' (ϑ/3)`. This is a slip in the paper with no consequences: every
   later use of Corollary 2.4 needs only that the angle is positive and depends
   on `d` and `ϑ` alone.

4. **Corollary 2.4: the sets `M_i` in the paper's proof.** The displayed
   definition ends with `M_L = {x | V^L ⊆ Γ(x)} \ M_{L-1}`, which does not make
   the union `⋃ M_i` disjoint (it should subtract `M_1 ∪ ⋯ ∪ M_{L-1}`). The Lean
   proof takes the equivalent and cleaner route of choosing, for each `x`, some
   index with `V^m ⊆ Γ(x)`; the paper's `M_i` are exactly the fibres of that
   choice.

5. **Lemma 3.4 is stated with `ℤ^d` but proved for `hℤ^d` — the literal
   statement is false.** The lemma reads "For every `h > 0`, all `x, y ∈ ℤ^d`
   with `|x − y| > √d·h` …". Its proof, however, treats the case `h = 1` and
   closes with "The general case for arbitrary `h > 0` follows by scaling" —
   and scaling `ℤ^d` by `h` produces `hℤ^d`, not `ℤ^d`. With `x, y` ranging
   over `ℤ^d` for arbitrary `h` the lower bound genuinely fails:

   > `d = 1`, `h = 3/2`, `x = 0`, `y = 2`, `s = 7/10`, `t = 13/10`.
   > Then `|x − y| = 2 > 3/2 = √d·h`, `s ∈ A_h(x)` and `t ∈ A_h(y)` (both
   > coordinates are within `h/2 = 3/4` of their centres), yet
   > `|s − t| = 3/5` while `(2√d)⁻¹|x − y| = 1`.

   `QFS.lemma_cubes_literal_false` is a Lean proof of exactly this. The
   corrected statement — `x, y ∈ hℤ^d`, which is what the paper's own scaling
   argument yields and what the applications (Proposition 3.5 with `h = 1`,
   Corollary 3.6 on `hℤ^d`) actually use — is `QFS.lemma_cubes`.

6. **Lemma 3.2 needs neither the lattice nor the favouring.** The lemma is
   stated for `x, y ∈ ℤ^d` and `1`-favoured indices `m` at `x`, `n` at `y`, with
   `s ∈ A_1^m(x)` and `t ∈ A_1^n(y)`. Its proof uses only `s ∈ A_1(x)` and
   `t ∈ A_1(y)`. `QFS.lemma_min_dist` proves that (more general) statement;
   `QFS.lemma_min_dist_favoured` is the paper's exact form, deduced from it.

7. **Lemma 3.3 is false in dimension one**, at the radius `r = √d` at which
   Proposition 3.5 applies it. The paper introduces it with "The assertion of
   the following lemma is obviously true". In `d = 1` every double cone
   `V(v, θ)` with `θ ∈ (0, π/2]` is all of `ℝ \ {0}`, so
   `V(v, θ) ∩ ℤ = ℤ \ {0}`, whereas `V^m_r ∩ ℤ = {n ∈ ℤ : |n| > r}` omits `±1`
   once `r ≥ 1`. Since `√d = 1` when `d = 1`, no `θ` and no axis `v` can give
   `V(v,θ) ∩ ℤ ⊆ V^m_{√d} ∩ ℤ`. `QFS.lemma_new_config_false_dim_one` is a Lean
   proof of this, for every `θ ∈ (0, π/2]`, every unit axis `v`, and every
   reference cone.

   This is a defect in the statement, not in the paper's results: for `d = 1`
   there is only one double cone, so `V^Γ[x] = ℝ \ {x}` and Theorems 1.1 and
   1.3 hold trivially. For `d ≥ 2` the lemma is true but not obvious — one must
   choose the axis `v(m)` to avoid the finitely many lines through the lattice
   points of norm below `r / sin(θ_m/2)`, and only then shrink `θ`. That
   argument is not in the paper and is not formalised here.

8. **Lemma 4.6 needs `z ∈ U`, which the paper does not state.** The lemma reads
   "Assume that the translated double cone `V[x]` contains a point `z` of type
   `V`. Then `x` and `y` are connected." The proof uses the edge from `z` to
   `x`, which exists in `G[U]` only if `z ∈ U`. `QFS.ueber_bande` therefore
   takes `z ∈ U` as a hypothesis. This costs nothing: Theorem 4.1 applies the
   lemma to a point of `U ∩ V[x]`. (Conversely, the hypothesis `x ∈ U` that the
   paper does state is not needed; it is kept for fidelity.)

9. **Theorem 4.1: the induction is run on a different open set.** The paper's
   induction is on the number of cone types realised in `U`, and in the
   inductive step it applies the inductive hypothesis to

   > `U' = U ∩ V[x]`, concluding "all points in `U'` are mutually connected in
   > `G[U']`".

   But `V[x]` is a *double* cone — the disjoint union of two open half-cones —
   so `U'` is in general not connected, while the inductive hypothesis is
   Theorem 4.1, a statement about *connected* open sets. As stated the step does
   not go through.

   The formalisation repairs this by running the induction on

   > `U'' = B_r(x) ∩ Ṽ[x]`, with the *half*-cone `Ṽ`,

   which does everything the argument needs and is connected:

   - `U''` is convex, hence preconnected (`QFS.convex_cone` shows a cone of apex
     angle at most `π/2` is convex — the "ice cream cone");
   - `U'' ⊆ U ∩ V[x]`, so the cone type `V` is still not realised in `U''` and
     the induction still descends (`Set.ncard_lt_ncard`);
   - the point supplied by the `λ`-observation is `x + (r/2)·v`, which lies in
     the *half*-cone, hence in `U''` (this is why
     `QFS.exists_mem_ball_inter_shift` is stated with `cone` rather than
     `doubleCone`; `QFS.exists_mem_ball_inter_shift'` is the paper's weaker
     form);
   - `U''` contains the points `x + t·v` for all small `t > 0`, hence points
     arbitrarily close to `x`, which is what the appeal to well-connectedness of
     `x` needs.

   The paper's closing sentence — "density of well-connected points implies that
   `U` is covered by overlapping open well-connected subsets" — is made precise
   as `QFS.conn_of_wellConnected_of_isPreconnected`: once every point of `U` is
   well-connected the connectivity classes are open, so a preconnected `U` is a
   single class.

10. **`DCone` carries a unit axis, not a point of projective space.** The paper's
    family `𝒱` is `(0, π/2] × ℙ^{d-1}`, so a double cone is named by a *line*.
    `QFS.DCone` bundles a unit vector instead, which is a 2:1 cover of `𝒱`:
    the axes `v` and `−v` give different `DCone`s with the same underlying set.
    Wherever the paper speaks of two points having the *same type*
    (Definition 4.2, Lemmas 4.3 and 4.6), the Lean statements therefore ask for
    equality of the underlying double cones — `(Γ x).carrier = (Γ y).carrier` —
    which is the paper's notion, rather than the finer `Γ x = Γ y`.

11. **Lemma 5.6 is not obvious.** The paper introduces it with "The assertion of
    the following lemma is obvious." The natural first attempt — step from `x`
    radially inward toward the tip — fails: scaling does not change the *angle*
    to the cone axis, so a lattice point close to the boundary of the cone stays
    close to it, and no ball of radius `√d/2` fits, so no lattice point is
    produced. The proof formalised here steps radially inward by a fixed amount
    *and* along the cone axis; the second move raises the distance to the cone
    boundary by exactly `a sin ϑ` (`QFS.coneGap_add_smul_axis`), which is what
    makes room for a lattice point.

    This motivated the auxiliary notion `QFS.coneGap v ϑ p = ⟪v,p⟫ sin ϑ −
    ‖p − ⟪v,p⟫v‖ cos ϑ`, the signed distance from `p` to the cone boundary. It is
    positive exactly on the cone, `1`-Lipschitz, and positively homogeneous, and
    `QFS.closedBall_subset_cone` subsumes the earlier
    `QFS.mem_cone_of_norm_sub_lt` (which is the case `p = t·v`, where the gap is
    `t sin ϑ` — recorded as `QFS.coneGap_smul_axis`).

## Not attempted

Recorded here rather than silently omitted. The paper's two main theorems and
the machinery specific to them are out of scope for this formalisation; what is
formalised is the geometric and graph-theoretic layer they are built on.

| Result | Paper | Why not |
| --- | --- | --- |
| Comparability on balls, continuous | Thm. 1.1 | Needs the whole of §§3, 5, 6. Statement recorded as `QFS.TheoremOneOne`. |
| Comparability on balls, discrete | Thm. 1.3 | The paper's main theorem; needs §§5–6. Statement recorded as `QFS.TheoremOneThree`. |
| `H_k(Ω) = H^{α/2}(Ω)`, density | Thm. 1.4 | Depends on Thm. 1.3 and on Lipschitz-domain extension theory not in scope. |
| Regular Dirichlet form; Markov process | Cor. 1.5 | Depends on Thm. 1.1 and on Dirichlet-form theory (Fukushima–Oshima–Takeda) absent from Mathlib. |
| Weak Harnack, Hölder regularity | Cor. 1.6 | Quoted from Dyda–Kassmann; not proved in the paper. |
| `hℤ^d` rescaling | Cor. 3.1 | Depends on Thm. 1.3. |
| Discrete kernel `ω^k_h`, test-function bound | Prop. 3.5, Cor. 3.6 | Integration against the kernel; depends on Thm. 1.3's setting, and on Lemma 3.3 (see Deviations 7). |
| Lemma 3.3 for `d ≥ 2` | Lem. 3.3 | True but needs an argument the paper does not give; see Deviations 7. |
| `H_k` on balls | Lem. 3.7 | Depends on Cor. 3.6. |
| Core induction; renormalisation | §5 (Lems. 5.7–5.16) | Lemma 5.7's base case is proved and its statement recorded (`QFS.CoreInduction`); the induction step is not — see below. 5.8–5.16 build the "town" and scale machinery. (Lemmas 5.1–5.6 **are** formalised.) |
| Proof of Theorem 1.3 | §6 | As above. |
| Auxiliary integral estimates | Lems. 7.1, 7.2 | Measure-theoretic, attached to §§3 and 6. |

## What the induction step of Lemma 5.7 still needs

The base case `k = 1` is `QFS.core_induction_base`: it is Corollary 5.2 applied
to `x` and each lattice point of `B_r(x)`. The step is where the work is. Given
`r_{k−1} ≤ ρ_{k−1} ≤ R_{k−1}`, the paper picks
`s > (ρ_{k−1}+√d)/sin ϑ`, `S > (s+√d)/sin ϑ`, sets `r_k = S`, takes an
`s`-`S`-connected `x̂ ∈ B_{r_k}(x)` (Lemma 5.4), and for `y ∈ B_{r_k}(x)` of type
`V` splits on whether `V` is realised in
`B_{ŝ+ρ_{k−1}}(x̂) ∩ V[x̂]`. The case where it is, is Lemma 5.5, which is proved
here. The other case needs four things that are not yet formalised:

1. **Type counting.** That the types realised in
   `B_{ŝ+ρ_{k−1}}(x̂) ∩ V[x̂]` number at most `k−1`, since they are among the `≤ k`
   types of `B_{ρ_k}(x)` and exclude `V`. Bookkeeping with `Set.encard`, given
   `ρ_k > S + ŝ + ρ_{k−1}`; routine but fiddly.

2. ~~**Descent inside a translated, shrunk half-cone.**~~ **Done.**
   `QFS.coneGap_gt_eq_shift_cone` shows that the points of gap more than `ρ` are
   exactly the half-cone with the same axis and angle whose apex has moved
   `ρ / sin ϑ` along the axis, so `Ṽ_ρ` contains such a half-cone
   (`QFS.shift_cone_subset_shrink`). Lemma 5.6 for a half-cone with an arbitrary
   apex is `QFS.exists_closer_lattice_nearby_shift`, and the paper's "connected
   to a lattice point near the tip" is `QFS.exists_chain_to_apex_shrunk`: from
   any lattice point of `c + Ṽ_ρ` the chain of jumps of length less than `δ`
   reaches a lattice point within `t₀` of the displaced apex, with `δ` and `t₀`
   depending only on `ϑ` and `d` — not on the apex, and not on `ρ`.

   The construction turned out not to need the hypothesis that a closer lattice
   point exists: outside a ball of radius `t₀` about the apex one can *always*
   step at least `1` closer (`QFS.exists_lattice_step_toward_apex`). That is what
   makes the descent terminate on `⌈‖x − c‖⌉₊`, with no appeal to finiteness of
   the lattice in a bounded region, and it strengthens Lemma 5.6 as stated.

3. **Assembling paths across different balls.** The conclusion is a `ConnWithin`
   inside `B_{R_k}(x)`, built from paths inside `B_{R_{k−1}}(p)` for various `p`,
   one inside `B_S(x̂)`, and single edges. `QFS.ConnWithin.mono` handles the
   inclusions; the arithmetic of `R_k > 2S + R_{k−1} + ŝ` and
   `R_k > (ŝ+ρ_{k−1}) + (2(ŝ+ρ_{k−1})+√d)/sin ϑ` has to be tracked.

4. **The recursion producing the constants.** `CoreInduction` is stated so that
   each `k` carries its own `r, ρ, R`, which avoids constructing three
   interleaved sequences; the paper's monotonicity `r_i < r_{i+1}` etc. is then
   not needed, only the invariant `δ < r_k`.

Of these, item 2 is now done; items 1, 3 and 4 remain. Nothing here looks false —
unlike Lemmas 3.3 and 3.4 — but it is still a substantial piece of work, and
Lemmas 5.8–5.16 and Section 6 sit on top of it.

## Verification

Every commit is checked with

```
lake build                                  # no errors, no warnings
grep -rn 'sorry' --include='*.lean' .       # no occurrences
#print axioms <headline theorem>            # [propext, Classical.choice, Quot.sound]
```

for each headline theorem, and the Lean names appearing in the status table above
are checked to resolve (`#check`). The paper's constants and hypotheses are
matched literally; where they could not be (Lemmas 3.3, 3.4, 4.6, Theorem 4.1)
the discrepancy is recorded under *Deviations*, with a Lean disproof of the
printed statement where one exists.

## Building

```
lake exe cache get   # or reuse an existing Mathlib build
lake build
```
