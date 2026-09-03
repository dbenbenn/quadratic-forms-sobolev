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
auxiliary results, core induction and discrete template, Lemmas 5.1–5.8 — the
quantitative discrete counterparts of the Section 4 lemmas, the induction that
assembles them, and its uniform consequence. The paper's main theorems (1.1 and 1.3) are recorded as
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
| 5.7 | Lemma | the core induction | ✅ (monotonicity clause omitted, see Deviations 12) |
| 5.8 | Corollary | discrete template | ✅ |
| 5.9 | Lemma | apex shrinking | ✅ (corrected constant, see Deviations 13) |
| 5.10 | Definition | blocks and towns | ✅ |
| 5.11 | Definition | favored by majority | ✅ |
| 5.12 | Remark | the favored cone is not unique | ⚪ (reflected in the design, see below) |
| 5.13 | Definition | the favored graph | ✅ |
| 5.14 | Proposition | renormalisation | ✅ |
| 5.15 | Theorem | path properties | ⚪ statement recorded (`QFS.PathPropsHolds`), not proved |
| 5.16 | Lemma | the first jump | ✅ |
| 7.1 | Lemma | auxiliary integral estimate | ❌ out of scope |
| 7.2 | Lemma | a Lebesgue differentiation argument | ❌ out of scope |

Sections 2 and 4 are formalised completely, as is Section 5's auxiliary
subsection (Lemmas 5.1–5.5). Section 3 is formalised as far as it can be without
the machinery of Sections 5 and 6 (Lemma 3.3, which Proposition 3.5 needs, is
false as stated). From Section 1, the function-space definitions, assumption
(1.4), the reverse inequality and equation (1.6) are proved, and Theorems 1.1
and 1.3 are recorded as type-checked `Prop`s so the remaining target is precise.
Theorem 5.15 (recorded as a statement) and Section 6 remain a project in their
own right.

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
| Types are monotone in the region | Lem. 5.7, step (1) | `QFS.typesIn_mono`, `QFS.mem_typesIn` | ✅ proved |
| Dropping a witnessed element from `≤ k+1` leaves `≤ k` | Lem. 5.7, step (1) | `QFS.encard_le_of_subset_diff` | ✅ proved |
| **Type counting**: a missing type drops the count | Lem. 5.7, step (1) | `QFS.encard_typesIn_le_of_missing` | ✅ **proved** |
| Push a path into a larger ball | Lem. 5.7, step (3) | `QFS.ConnWithin.mono_ball` | ✅ proved |
| An `r`-`R`-connected point joins its `r`-ball | Lem. 5.7, step (3) | `QFS.RRConnected.conn` | ✅ proved |
| Where a descent chain lives | Lem. 5.7, step (3) | `QFS.Jump.chain_dist_le`, `QFS.Jump.chain_mem` | ✅ proved |
| **Path assembly**: "the well-connected balls overlap" | Lem. 5.7, step (3) | `QFS.connWithin_of_chain` | ✅ **proved** |
| Cone types realised at the lattice points of a set | §5.2 | `QFS.typesIn` | ✅ defined |
| Statement of Lemma 5.7 | Lem. 5.7 | `QFS.CoreInduction` | ✅ defined |
| Lemma 5.7, base case `k = 1` alone | Lem. 5.7 | `QFS.core_induction_base` | ✅ proved |
| **Lemma 5.7, the induction step** | Lem. 5.7 | `QFS.core_induction_step` | ✅ **proved** |
| **Lemma 5.7** | Lem. 5.7 | `QFS.core_induction`, `QFS.coreInduction_holds` | ✅ **proved** |
| `ConnWithin` is not vacuous | (sanity check) | `QFS.connWithin_empty` | ✅ proved |
| Cor. 2.4 with a uniform bound on `L` | Cor. 2.4 / Cor. 5.8 proof | `QFS.ref_config_uniform` | ✅ proved |
| Connectivity is monotone in `Γ` and in `r` | Cor. 5.8 proof | `QFS.ConnWithin.mono_config`, `QFS.RRConnected.mono_radius` | ✅ proved |
| **Corollary 5.8**: the discrete template | Cor. 5.8 | `QFS.discrete_template` | ✅ **proved** |
| Closed cube `Ā_ℓ(u)` | §5.2 | `QFS.closedCube` | ✅ defined |
| **Gap = distance to the cone boundary** | (new; sharp) | `QFS.coneGap_eq_norm_mul_sin` | ✅ **proved** |
| Half-angle cone has gap `≥ ‖h‖ sin(ϑ/2)` | Lem. 5.9 proof | `QFS.coneGap_ge_of_mem_half` | ✅ proved |
| **Lemma 5.9**: apex shrinking | Lem. 5.9 | `QFS.renormalization_apex_shrink` | ✅ **proved** (corrected constant) |
| The paper's threshold in Lem. 5.9 is too small | Lem. 5.9 proof | `QFS.paper_threshold_insufficient` | ✅ **disproved** |
| Lemma 5.9's constant, explicitly | Lem. 5.9 | `QFS.apexShrinkConst` | ✅ defined |
| Lattice points in a ball are finite | (new; needed by Def. 5.11) | `QFS.lattice_inter_closedBall_finite` | ✅ proved |
| **Block, town, sparsely populated** | Def. 5.10 | `QFS.block`, `QFS.town`, `QFS.SparselyPopulated` | ✅ **defined** |
| Blocks are finite; the town–`ℤ^d` identification | Def. 5.10 | `QFS.block_finite`, `QFS.townIndex`, `QFS.townIndex_mem_town` | ✅ proved |
| **Favored by majority** | Def. 5.11 | `QFS.blockFibre`, `QFS.FavoredIn` | ✅ **defined** |
| A favored cone exists in a nonempty block | Def. 5.11 / Rem. 5.12 | `QFS.exists_favoredIn` | ✅ proved |
| **The favored graph** | Def. 5.13 | `QFS.FavoredEdge`, `QFS.FavoredConn` | ✅ **defined** |
| Cones are invariant under positive scaling | Prop. 5.14 proof | `QFS.smul_mem_cone` | ✅ proved |
| A double cone ignores the sign of its axis | Prop. 5.14 proof | `QFS.doubleCone_neg` | ✅ proved |
| Distinct lattice points are `≥ 1` apart | Prop. 5.14 proof | `QFS.one_le_norm_sub_of_lattice` | ✅ proved |
| Blocks within `R` of a point | Prop. 5.14 | `QFS.townBall` | ✅ defined |
| **Proposition 5.14**: renormalisation | Prop. 5.14 | `QFS.renormalization` | ✅ **proved** |
| The scale step `Δ`; towns at scale are sparse | §5.3 setup | `QFS.ScaleStep`, `QFS.exists_scaleStep`, `QFS.sparselyPopulated_of_scaleStep` | ✅ proved |
| **Lemma 5.16**: the first jump | Lem. 5.16 | `QFS.connect_first_jump` | ✅ **proved** |
| `G` as a `SimpleGraph`, with walks | §5.3 | `QFS.latticeGraph`, `QFS.LatticePt` | ✅ defined |
| Statement of Theorem 5.15 | Thm. 5.15 | `QFS.PathProps`, `QFS.PathPropsHolds` | ⚪ stated, not proved |
| Coordinates determine a point; rounding is injective | (new) | `QFS.euclidean_ext`, `QFS.round_injOn_lattice` | ✅ proved |
| **`#(B_M ∩ ℤ^d) ≤ (2⌈M⌉+1)^d`, uniformly in the centre** | Thm. 5.15, Steps 1–2 | `QFS.encard_lattice_inter_closedBall_le` | ✅ **proved** |
| **A block of side `ℓ` has `≥ ℓ^d` lattice points** | Thm. 5.15, Step 2 | `QFS.le_encard_block` | ✅ **proved** |
| `#(B_R ∩ ℤ^d) ≥ ℓ^d` when the cube fits | Thm. 5.15 | `QFS.le_encard_lattice_inter_closedBall` | ✅ proved |
| **Majority sets have `≥ #Q/L` points** | Thm. 5.15, Step 2 | `QFS.ncard_le_mul_ncard_blockFibre` | ✅ **proved** |
| Reachability chain ⟹ walk, confined | Thm. 5.15, Step 1 | `QFS.exists_walk_of_reflTransGen` | ✅ proved |
| **A walk in a finite set shortens to length `< #S`** | Thm. 5.15, Step 1 | `QFS.exists_walk_length_lt`, `QFS.exists_walk_of_reflTransGen_lt` | ✅ **proved** |
| **Concatenation through way-points** | Thm. 5.15, Step 1 | `QFS.exists_walk_through_list`, `QFS.exists_walk_covering` | ✅ **proved** |
| The bridge for `G`; walks from `RRConnected` | Thm. 5.15, Step 1 | `QFS.exists_walk_of_connWithin`, `QFS.exists_walk_of_rrConnected` | ✅ proved |
| **The favored graph as a `SimpleGraph`** | Def. 5.13 | `QFS.favoredAdj`, `QFS.favoredGraph`, `QFS.not_favoredEdge_self` | ✅ **defined** |
| The bridge for the favored graph | Thm. 5.15, Step 1 | `QFS.exists_favoredWalk_of_favoredConn`, `QFS.FavoredConn.mono` | ✅ proved |
| Town-balls: finite, counted, monotone | Thm. 5.15, Step 1 | `QFS.townBall_finite`, `QFS.ncard_townBall_le`, `QFS.townBall_mono` | ✅ proved |
| **Step 1 of Theorem 5.15** | Thm. 5.15, Step 1 | `QFS.exists_favoredWalk_covering` | ✅ **proved** |
| **A favored edge lifts to `G` on the majority set** | Thm. 5.15, Step 2 | `QFS.majority_adj_of_favoredEdge` | ✅ **proved** |
| `≥ #Q/L` points of `Q` adjacent to all of `P` | Thm. 5.15, Step 2 | `QFS.exists_large_adj_of_favoredEdge` | ✅ proved |
| The cyclic indices determine the scheme | Thm. 5.15, Step 2 | `QFS.cyclic_pair_injective` | ✅ proved |
| **The assignment `φ_z`, with bounded fibres** | Thm. 5.15, Step 2 | `QFS.exists_fun_fiber_le`, `QFS.exists_scheme_assignment` | ✅ **proved** |
| **Scale separation**: a length pins the scale | Thm. 5.15, Step 6 | `QFS.scale_separation` | ✅ **proved** |
| **Centre count** at a fixed scale | Thm. 5.15, Step 6 | `QFS.ncard_lattice_scaled_ball_le` | ✅ **proved** |
| **The multiplicity bound** from the three labels | Thm. 5.15, Step 6 | `QFS.card_le_mul_of_fiber_le` | ✅ **proved** |
| Blocks are nonempty and pairwise distinct | Thm. 5.15, Step 2 | `QFS.block_nonempty`, `QFS.townIndex_ne` | ✅ proved |
| **The favored graph relative to a cone choice** | Def. 5.13 (repaired) | `QFS.ConeChoice`, `QFS.choiceAdj`, `QFS.choiceGraph`, `QFS.favoredAdj_of_choiceAdj` | ✅ **defined** |
| **The both-majority lift** | Thm. 5.15, Step 2 | `QFS.latticeAdj_of_choiceAdj` | ✅ **proved** |
| **The alternating walk of the scheme** | Thm. 5.15, Step 2 | `QFS.exists_alternating_walk` | ✅ **proved** |
| **Proposition 5.14 for the choice graph** | Prop. 5.14 (refined) | `QFS.ChoiceConn`, `QFS.renormalization_choice` | ✅ **proved** |
| Step 1 for the choice graph | Thm. 5.15, Step 1 | `QFS.exists_choiceWalk_covering`, `QFS.exists_choiceWalk_of_choiceConn` | ✅ proved |
| `#(B_R ∩ ℤ^d)` in `ncard` form | Thm. 5.15 | `QFS.ncard_lattice_inter_ball_le` | ✅ proved |

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

12. **Lemma 5.7's monotonicity clause is not formalised — and is not what is
    needed.** The lemma asserts `r_i < r_{i+1}`, `ρ_i < ρ_{i+1}`, `R_i < R_{i+1}`
    and `δ < r_1`. The formalisation gives each `k` its own `r_k ≤ ρ_k ≤ R_k`
    with `δ < r_k`, which is all the proof of Lemma 5.7 itself uses — the
    monotonicity is never invoked there, and with `δ < r_k` for every `k` it is
    not needed to carry the invariant.

    Corollary 5.8 is the natural consumer, and it turns out monotonicity would
    not suffice there either: reaching an arbitrary `r` needs the radii to be
    *unbounded*, which strict monotonicity alone does not give. What Corollary
    5.8 actually needs is the growth bound `k ≤ r_k`, and that is recorded by
    `QFS.core_induction` and falls out of the construction
    (`r_{k+1} > ρ_k + 1 ≥ r_k + 1`).

13. **Lemma 5.9's constant is too small, and its intermediate estimate fails for
    every admissible apex angle.** The proof passes through

    > if `y ∈ Ṽ[x]` and `|x − y| ≥ ℓ√d/(2 sin ϑ)`, then `B_{ℓ√d/2}(y) ⊆ V̄[x]`,

    and concludes with `δ = 3√d/(2 sin ϑ)`. By `QFS.coneGap_eq_norm_mul_sin` the
    distance from `y` to the boundary of `V̄[x]` is exactly
    `‖y − x‖ sin(ϑ − ∠(v, y−x))`, and `y ∈ Ṽ[x]` bounds `∠(v, y−x)` only by
    `ϑ/2` — not by `0`. At the paper's threshold distance the guaranteed gap is
    therefore only

    > `ℓ√d sin(ϑ/2) / (2 sin ϑ) = ℓ√d / (4 cos(ϑ/2))`,

    which is less than the required `ℓ√d/2` precisely when `cos(ϑ/2) > 1/2`,
    i.e. for every `ϑ ≤ π/2`. `QFS.paper_threshold_insufficient` is a Lean proof
    of this. The same slip costs the final constant: `3√d/(2 sin ϑ)` is at least
    the necessary `√d/sin(ϑ/2)` only when `cos(ϑ/2) ≤ 3/4`, i.e. for
    `ϑ ≳ 82.8°`. Since `ϑ` is an infimum of apex angles and may be arbitrarily
    small, this is not a harmless slack.

    `QFS.renormalization_apex_shrink` proves the lemma with
    `δ = (√d + 1)/sin(ϑ/2)`, which is the sharp `√d/sin(ϑ/2)` plus enough to make
    the inequalities strict. Nothing downstream needs the particular value.

14. **Section 5.2 uses closed cubes, Definition 2.5 open ones.** The paper
    "recalls" the cube notation as `A_ℓ(x) = {y : ‖y−x‖_∞ ≤ ℓ/2}`, but
    Definition 2.5 defines `A_h(u)` with a strict inequality. `QFS.cube` and
    `QFS.closedCube` are both provided; Lemma 5.9 is proved for the closed cube,
    as Section 5.2 states it, which is the stronger reading.

15. **Remark 5.12 is reflected in the design.** The remark observes that a cone
    favored by majority in a block need not be unique. `QFS.FavoredIn` is
    therefore a *predicate* rather than a choice function, and
    `QFS.FavoredEdge` quantifies over *some* favored cone, as Definition 5.13
    does. `QFS.exists_favoredIn` supplies existence in a nonempty finite block —
    which needs blocks to be finite, hence
    `QFS.lattice_inter_closedBall_finite`. Without finiteness the phrase "has
    maximal size" in Definition 5.11 would be satisfied by every cone.

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
| Path properties | §5 (Thm. 5.15) | The quantitative path estimates; statement recorded as `QFS.PathPropsHolds`. See below. (Results 5.1–5.14 and 5.16 **are** formalised.) |
| Proof of Theorem 1.3 | §6 | As above. |
| Auxiliary integral estimates | Lems. 7.1, 7.2 | Measure-theoretic, attached to §§3 and 6. |

## Lemma 5.7

`QFS.core_induction` proves it, in a form slightly stronger than the paper's
statement: the constants are produced **before** the configuration is mentioned,

```
∃ δ > 0, ∀ k, ∃ r ρ R, δ < r ∧ r ≤ ρ ∧ ρ ≤ R ∧
  ∀ Γ, (∀ z, ϑ ≤ (Γ z).apex) → ∀ x ∈ ℤ^d,
    (types realised at the lattice points of B_ρ(x)).encard ≤ k → RRConnected Γ r R x
```

which is the paper's assertion that they depend only on `ϑ` and `d`, made
visible in the quantifier order (as in Lemma 2.2). `QFS.coreInduction_holds` is
the same for a fixed configuration, discharging the recorded `CoreInduction`.

The induction runs from the vacuous case `k = 0` — a lattice point always
realises its own type in `B_ρ(x)`, so the hypothesis is contradictory — with
`QFS.core_induction_step` doing the work. `QFS.core_induction_base` records the
paper's own base case `k = 1` separately.

Three departures from the paper's proof, all forced:

* The paper's `s` and the region radius need enlarging. A descent chain
  decreases distance to the **displaced apex** `x̂ + (ρ'/sin ϑ_V)·v`, not to `x̂`,
  so it leaves `B_ŝ(x̂)`; the inductive hypothesis is therefore invoked on a
  larger ball, and the case distinction made on the correspondingly larger
  region. And the chain ends within `t₀` of that apex, so `s` must exceed
  `ρ'/sin ϑ + t₀` for `x̂` to reach it. Since the paper only imposes lower bounds
  on `s` and `ŝ`, both are free adjustments.
* Lemma 5.1(2) is applied at the **displaced apex**, so that the lattice point it
  produces lands in the shrunk cone `x̂ + Ṽ_{ρ'}` rather than merely in `V[x̂]`.
  Applying it at `x̂`, as the wording suggests, would not put the point where the
  inductive hypothesis can be used.
* `Set.encard` is used for "at most `k` cone types", never `Set.ncard`: the
  latter is `0` on infinite sets, which would make the hypothesis vacuously
  satisfiable and the lemma false as stated in Lean.

`core_induction` also records that `k ≤ r_k`, so the radii grow without bound.
That is not part of the paper's statement, but Corollary 5.8 needs it: the paper
derives 5.8 from 5.7 "and the observation that an `r`-`R`-connected point is
`r'`-`R`-connected for `r' ≤ r`", which only lowers the small radius. To reach an
arbitrary `r` one must instead take `k` large — the index is the *number of cone
types*, capped at `L`, but nothing stops using a larger `k`, whose hypothesis is
weaker. Presumably this is what the paper's unformalised monotonicity clause
`r_i < r_{i+1}` is for; the growth bound `k ≤ r_k` is what the argument actually
needs, and it comes out of the construction.

## Corollary 5.8

`QFS.discrete_template`. Two supporting results the paper uses implicitly:

* `QFS.ref_config_uniform` — Corollary 2.4 with the number `L` of reference cones
  produced *before* the configuration, which is the proof's "`L` is a constant
  that depends only on `ϑ` and `d`". The formalisation of Corollary 2.4 itself
  only records finiteness.
* The hypothesis `0 < r` is not needed: for `r ≤ 0` the ball is empty and the
  conclusion vacuous. It is kept, to match the paper.

## Proposition 5.14

`QFS.renormalization`, following the paper: the town is identified with `ℤ^d` by
`x ↦ Q_ℓ(hx)` (`QFS.townIndex`), the configuration sending `x` to the cone of
apex angle `ϑ/2` with the axis of a cone favored in `Q_ℓ(hx)` is `ϑ/2`-bounded,
Lemma 5.9 turns each of its edges into an edge of the favored graph, and
Corollary 5.8 supplies the connectivity.

Sparse population enters at exactly one point, and it is the point the definition
was made for: an edge joins *distinct* lattice indices, so `‖hx − hy‖ ≥ h`, and
`δ < h/ℓ` gives `δℓ < h`, which is Lemma 5.9's distance hypothesis.

The apex bound needed at the end — that the favored cone `W(Q)` has apex angle at
least `ϑ`, so that `Ṽ(v, ϑ) ⊆ W(Q)` — is why `QFS.exists_favoredIn` returns a
cone *realised at a point of the block* rather than merely one of maximal fibre.
A maximal-fibre cone that is not realised would carry no information about its
apex angle. The block is nonempty exactly when the edge condition is non-vacuous,
so the two cases fit together.

## Theorem 5.15

`QFS.PathPropsHolds` records the statement; the proof is not formalised. Its four
claims count and measure edges, which the `Relation.ReflTransGen` used up to this
point cannot express — that records only that a path exists, not which one. So
the paths are Mathlib `SimpleGraph.Walk`s in `QFS.latticeGraph`, which carry a
length, a list of darts and a list of edges: claim (1) is the walk's type, (2)
bounds `length`, (3) bounds the number of pairs whose walk contains a given edge,
and (4) compares each dart's length to `‖x − y‖`.

Its prerequisite **Lemma 5.16 is proved** (`QFS.connect_first_jump`), together
with the scale-step setup: `QFS.ScaleStep` is the paper's even `Δ` exceeding
`max(δ, R₀)` and divisible by `L`, `QFS.exists_scaleStep` shows one exists, and
`QFS.sparselyPopulated_of_scaleStep` checks that every town `T(Δⁿ⁺¹, Δⁿ)` is then
sparsely populated. The proof of 5.16 uses one point the paper leaves implicit:
Lemma 5.1(1) produces a lattice point *whose `ρ`-ball* lies in the cone, and that
forces the point to be at distance more than `ρ` from the apex — which is exactly
the lower bound Lemma 5.9 needs, and which a bare "the cone contains a lattice
point" would not give.

What the proof of 5.15 still needs, beyond what is here:

1. ~~**Lattice-point counting.**~~ **Done.**
   `QFS.encard_lattice_inter_closedBall_le` bounds `#(B_M ∩ ℤ^d)` by
   `(2⌈M⌉+1)^d` *uniformly in the centre* — which is what the argument needs,
   since it counts balls around many different points;
   `QFS.le_encard_lattice_inter_closedBall` is the matching lower bound, giving
   the paper's `≍`. `QFS.le_encard_block` shows a block of integer side `ℓ`
   centred at a lattice point holds at least `ℓ^d` lattice points, and
   `QFS.ncard_le_mul_ncard_blockFibre` is the pigeonhole: a cone favored by
   majority is carried by at least `#Q/L` points of the block. Together these are
   the paper's "each block contains at least `Δ^{d(n-1)}/L` lattice points where
   the associated cone is favored by majority".

   Both directions rest on `QFS.euclidean_ext` and `QFS.round_injOn_lattice`:
   rounding coordinates injects the lattice into `ℤ^d`, which gives the upper
   bound, and translating a box of integers into a cube gives the lower one.
2. ~~**Concatenating favored-graph paths.**~~ **Done, abstractly.**
   `QFS.exists_walk_covering` is Step 1's conclusion in general form: if every two
   way-points of a finite nonempty `T` are joined by a walk inside `S` of length
   at most `N`, then a single walk inside `S` of length at most `#T · N` passes
   through all of `T` — the paper's `t ≤ #(B_r∩ℤ^d) · #(B_R∩ℤ^d)`, with its
   properties (1), (2) and (3).

   The length bounds come from a fact worth isolating. `Relation.ReflTransGen`,
   which carries every connectivity result of Sections 4 and 5, records only that
   a path *exists*. But a walk confined to a **finite** vertex set shortens to a
   path — delete the cycles, `SimpleGraph.Walk.bypass` — whose support is
   duplicate-free and hence no longer than `#S`. So
   `QFS.exists_walk_of_reflTransGen_lt` upgrades any confined reachability chain
   to a walk of length `< #S` for free, with no change to Lemma 5.7, Corollary
   5.8 or Proposition 5.14. Specialised to `G` this is
   `QFS.exists_walk_of_rrConnected`: an `r`-`R`-connected point reaches every
   lattice point of its `r`-ball by a walk of length less than `(2⌈R⌉+1)^d`, which
   is where the counting of item 1 enters.

   **Step 1 itself is now proved**, as `QFS.exists_favoredWalk_covering`: in a
   `ϑ`-sparsely populated town, every centre `z` of the index lattice admits one
   walk in the favored graph that visits every block indexed within `r` of `z`,
   never leaves the blocks indexed within `R`, and has length at most
   `(2⌈r⌉+1)^d · (2⌈R⌉+1)^d` — the paper's `t ≤ #(B_r∩ℤ^d) · #(B_R∩ℤ^d)`,
   with its properties (1), (2) and (3).

   This needed the favored graph as an actual `SimpleGraph` (`QFS.favoredGraph`).
   Its adjacency carries an explicit `Q ≠ P`, because `FavoredEdge Γ ∅ ∅` holds
   vacuously — the empty block is "adjacent to itself", which no `SimpleGraph`
   allows. On nonempty blocks the guard is free
   (`QFS.not_favoredEdge_self`: `FavoredEdge Γ Q Q` would put `0` in a cone), so
   nothing of the paper's Definition 5.13 is lost.
3. ~~**The cyclic scheme.**~~ **Its three ingredients are done.**

   *The lift.* `QFS.majority_adj_of_favoredEdge`: if `Q` and `P` are joined by a
   favored edge, every point of the majority set of `Q` — for the cone that
   witnesses the edge — is adjacent in `G` to *every* point of `P`. This is why
   the block walk of Step 1 becomes walks in `G`, and why any of the `a` majority
   points may be used at each step. With the pigeonhole of item 1,
   `QFS.exists_large_adj_of_favoredEdge` says at least `#Q/L` points of `Q` have
   this property.

   *The cyclic indexing.* The scheme reads indices in `ZMod a`, using `q^k_i` at
   odd `k` and `q^k_{i+j}` at even `k`. A consecutive pair of indices is
   `(i, i+j)`, and `QFS.cyclic_pair_injective` says that determines `(i, j)` —
   which is exactly why the `a²` walks do not share an edge at any position, the
   fact Step 6's multiplicity count rests on.

   *The assignment.* `QFS.exists_fun_fiber_le` is a balanced partition: if
   `#A ≤ K · #M` and `M ≠ ∅`, the elements of `A` can be assigned to `M` with no
   fibre exceeding `K`. `QFS.exists_scheme_assignment` is the instance with `M`
   the `a²` index pairs, giving the paper's `φ_z` with `#φ_z⁻¹(p) ≤ K`. The
   paper's remark that "`a` and `#A` are comparable" is made precise by the
   counting of item 1: `#A ≲ Δ^{2nd}` while `a² ≳ Δ^{2d(n-1)}/L²`, a ratio of
   `Δ^{2d}L²`.

   What is left is assembly: building the `a²` walks as `SimpleGraph.Walk`s along
   the Step 1 block walk with alternating representatives, which needs the
   majority sets indexed by `ZMod a` — bookkeeping rather than new mathematics.
4. ~~**The edge-multiplicity count.**~~ **Its three ingredients are done.**
   An edge is used by a pair only through a logarithmic scale, a centre of the
   index lattice at that scale, and `φ_z`; each ranges over a bounded set.

   *Scales.* `QFS.scale_separation`: the edges of the walk for a pair at scale `m`
   have length in `[Δ^m, 2Δ^{m+1}R)` (Step 5), and these windows overlap only
   boundedly — two scales sharing a length differ by at most `C`, where
   `2^C ≥ 2ΔR`. This is what lets the paper "fix `n`".

   *Centres.* `QFS.ncard_lattice_scaled_ball_le`: at a fixed scale `s`, only
   `(2⌈R⌉+1)^d` centres of the index lattice have their ball of radius `sR`
   containing a given point. Rescaling reduces this to the ball count of item 1;
   the paper's `#(B_{2R} ∩ ℤ^d)` is the two-endpoint version of the same bound.

   *Combination.* `QFS.card_le_mul_of_fiber_le`: if each element of a set carries
   two labels ranging in `S × C` and no label pair carries more than `K`
   elements, the set has at most `#S · #C · K` elements. With the labels the
   scale and the centre, and `K` the fibre bound of `φ_z`, this is Step 6.

All four items are discharged, Step 1 is proved outright, and the assembly of
Step 2 is built (see below). What remains is to package the result as
`PathPropsHolds`: choosing the representatives `ρ` explicitly from the majority
sets, and deriving claims (3) and (4) from `card_le_mul_of_fiber_le`,
`cyclic_pair_injective` and `scale_separation`. Section 6 sits on top.

## A gap in Definition 5.13

Definition 5.13 puts an edge between blocks `Q` and `P` when **some** cone favored
in `Q` contains `P` based at `Q`. That is too weak for Step 2. The scheme picks
*one* representative per block and runs it along the whole block walk, so a block
sitting between two edges must be a majority point for both witnessing cones at
once — and different edges may be witnessed by different favored cones, a block
having several only when there is a tie.

The paper's own Step 2 repairs this in passing — "choose for every block in
(bigpath) a favored cone" — so the object actually needed is the favored graph
*relative to a choice of cones*, `QFS.choiceGraph`. It is a subgraph of
Definition 5.13's (`QFS.favoredAdj_of_choiceAdj`), and Proposition 5.14 produces
it: the proof already fixes a favored cone per block before anything else, and
only the statement discarded that. `QFS.renormalization_choice` records the
stronger conclusion, and `QFS.exists_choiceWalk_covering` is Step 1 in that graph.

With the choice fixed, `QFS.latticeAdj_of_choiceAdj` gives the **both-majority
lift**: a majority point of `Q` and a majority point of `P` are adjacent in `G`
whichever way the favored edge points — so one representative per block does
serve both incident edges. `QFS.exists_alternating_walk` then lifts a block walk
to a walk in `G` of the same length, alternating between two indices of `ZMod a`
and ending at the index determined by the parity of the length, which is exactly
the paper's `q^k_i` at odd `k` and `q^k_{i+j}` at even `k`.

The `Q ≠ P` in `choiceAdj` needs blocks at distinct centres to be distinct:
`QFS.block_nonempty` (a cube of side `≥ 1` holds a lattice point) and
`QFS.townIndex_ne`, where sparse population is used again — it gives
`h > √d ℓ`, so distinct centres have disjoint cubes.

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
