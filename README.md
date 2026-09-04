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

The paper's main results are **Theorem 1.3** (comparability of discrete quadratic
forms on `ℤ^d`) and **Theorem 1.1** (its continuous counterpart), the second
deduced from the first by a discrete approximation.

**Theorem 1.3 is proved here** (`QFS.theoremOneThree`), and with it everything it
rests on: Section 2's definitional set-up and reference cones, Section 4's
"continuous prelude" and its Theorem 4.1, the whole of Section 5 including
**Theorem 5.15** (`QFS.path_props`), and Section 6.

Of the road to Theorem 1.1, Section 3 is formalised as far as the discrete
kernel goes — Corollary 3.1, Lemmas 3.2–3.4, **Proposition 3.5** and **Corollary
3.6** — as is §3.2's scaffolding (the step functions, their almost-everywhere
convergence, and the tiling identity that turns the discrete sums into
integrals). The paper's dominated-convergence step is proved under the a priori
hypothesis `f ∈ H^{α/2}(B*)`, which reduces §3.2 to the single qualitative
statement `H_k(B*) ⊆ H^{α/2}(B*)`. Theorem 1.1 itself is recorded as
a type-checked `Prop`, together with the enlarged-ball form
(`QFS.TheoremOneOneBall`) that §3.2 alone would give; its last step, from a ball
`B*` down to `B`, is Lemma 7.1, whose chain (6.14) is proved here with the
Whitney family and Dyda's inequality (13) — the two things the paper quotes
rather than proves — as explicit hypotheses. Theorem 1.4 for `Ω = ℝ^d` is
proved granted Theorem 1.1. See *Not attempted*.

Two results carry hypotheses the paper does not: Proposition 3.5 and Corollary
3.6 need `d ≥ 2`, because Lemma 3.3 is false in dimension one, and they take as
given the measurability the paper obtains by quoting Debreu's theorem
(`QFS.CondMeas`).

Along the way the formalisation turned up a number of defects in the paper. All
are recorded under *Deviations*; three come with Lean proofs that the statement
as printed is false:

* **Lemma 3.4** is stated for `x, y ∈ ℤ^d` but is only true for `x, y ∈ hℤ^d`,
  which is what its own "follows by scaling" argument gives
  (`QFS.lemma_cubes_literal_false`).
* **Lemma 3.3** is false in dimension one at the radius `r = √d` at which
  Proposition 3.5 uses it (`QFS.lemma_new_config_false_dim_one`); for `d ≥ 2` it
  is true, and proved here (`QFS.lemma_new_config`), by an argument the paper
  does not give.
* **Lemma 5.9**'s intermediate estimate fails for *every* `ϑ ≤ π/2`, and its
  constant is too small (`QFS.paper_threshold_insufficient`).

and the rest are gaps or slips repaired silently:

* **Lemma 4.6** needs a hypothesis `z ∈ U` that is not stated.
* **Theorem 4.1**'s induction is applied to a set that need not be connected;
  the repair is to run it on `B_r(x) ∩ Ṽ[x]` with the half-cone. Its proof also
  opens with an observation that is false as printed for cones of small apex
  (Deviation 18).
* **Lemma 5.6** is called obvious, but the obvious argument (stepping radially
  toward the tip) does not work.
* **Definition 5.13**'s favored graph is too weak for Step 2 of Theorem 5.15.
* **Step 2 of Theorem 5.15** asks only that `φ_z` be balanced, which does not
  bound the multiplicity of a first-jump edge, so claim (3) fails for an
  adversarial choice (Deviation 16).
* **Section 6** chains along edges longer than `R₀`, which claim (4) of Theorem
  5.15 does not provide (Deviation 17).
* Four smaller printed slips are listed in Deviation 19.

## Beyond the paper — new mathematics, clearly separated

**One file, `QuadraticFormsSobolev/BeyondThePaper.lean`, is not a formalisation
of Bux–Kassmann–Schulze.** Nothing in it appears in arXiv:1707.09277 — not the
statements, not the constants, not the proofs. It is an attempt at the single
open statement recorded under *What remains*, and it should be read as new and
**incomplete** research, not as a record of what the authors wrote.

Its results are deliberately **excluded from the coverage and detail tables
below**, which are the audit instrument for the paper and must stay that way: a
table that credits the repository with results the paper does not contain is
exactly the drift those tables exist to catch. Nothing else in the repository
depends on this file, so deleting it would leave the certification intact.

The route it attempts is a local Poincaré inequality on a cube `Q` of side `h`,

  (★)  `∫∫_{Q×Q}(f(s) − f(t))² ≤ C(d,ϑ,α,Λ)·h^{d+α}·∫∫_{Q*×Q*}(f(s) − f(t))²k(s,t)`,

which summed over the tiles bounds `A_h` uniformly and closes the theorem with
Fatou alone. `(★)` follows by chaining: join `s` to `t` through intermediate points that *do*
see the relevant cones, and average over a positive-measure set of chains.

**The chaining argument is now complete for pairs sharing a cone direction**, and
that case of the open statement is proved:

> `QFS.formHs_le_form_of_commonDirection` — if every cone of `Γ` contains a fixed
> `Ṽ(v,ϑ)`, then `|f|²_{H^{α/2}(ℝ^d)} ≤ 2Λ(C + C')·|f|²_{H_k(ℝ^d)}` with explicit
> constants, i.e. `H_k ⊆ H^{α/2}`.

Underneath it is a theorem of independent interest,
`QFS.localPoincare_sameDirection`: for any unit `v` and `ϑ ∈ (0,π/2]`, the **full**
fractional energy of `ℝ^d` is bounded by the energy restricted to pairs whose
difference lies in the fixed cone `Ṽ(v,ϑ)`. That is "directional regularity
implies full regularity", proved by chaining rather than by Fourier, with
constants depending only on `d`, `ϑ` and `α`.

The pieces, all proved:

| Input | Lean | State |
| --- | --- | --- |
| A **ball** of common cone-neighbours of `s` and `t`, radius `‖s−t‖`, inside both cones and within `O(‖s−t‖/sin ϑ)` of each | `QFS.exists_ball_in_two_cones`, `QFS.mem_two_cones_of_mem_midBall` | ✅ proved |
| The compression bound: for fixed `s`, `z`, the admissible `t` lie in a ball of radius comparable to `‖z−s‖` | `QFS.midBall_fibre_subset_closedBall`, `QFS.inner_mem_Icc_of_mem_midBall` | ✅ proved |
| The averaging ball has volume exactly `c_d‖s−t‖^d` | `QFS.volume_midBall` | ✅ proved |
| The `t`-side mirrors of the fibre lemmas | `QFS.inner_mem_Icc_of_mem_midBall'`, `QFS.midBall_fibre_subset_closedBall'`, `QFS.fibre_subset_singleton_of_notMem_cone'`, `QFS.lintegral_midBall_fibre_le'`, `QFS.chainConst'` | ✅ proved |
| The fibre vanishes off the cone, so the exchange keeps the cone membership | `QFS.fibre_subset_singleton_of_notMem_cone` | ✅ proved |
| Joint measurability of the averaging integral, so Tonelli applies | `QFS.measurable_param_midBall` | ✅ proved |
| On a cone pair, `jumpKernel ≤ Λ·k` | `QFS.jumpKernel_le_of_mem_coneAt` | ✅ proved |
| **The fibre estimate**: `∫_{t : z ∈ W(s,t)} ‖s−t‖^{-2d-α} dt ≤ C(d,ϑ,α)·‖z−s‖^{-d-α}` | `QFS.lintegral_midBall_fibre_le`, `QFS.chainConst` | ✅ proved |
| **The averaging step**: `(f(t)−f(s))²·|W(s,t)| ≤ ∫_{W(s,t)} 2(f(z)−f(s))² + 2(f(t)−f(z))²` | `QFS.osc_mul_volume_le`, `QFS.osc_weighted_le` | ✅ proved |
| **The exchange, abstractly**: any measurable family of averaging sets with a fibre bound | `QFS.lintegral_swap_of_fibre_bound` | ✅ proved |
| **The exchange at fixed `s`**: Tonelli plus the fibre estimate, returning the weight `‖z−s‖^{-d-α}` | `QFS.lintegral_swap_fibre`, `QFS.lintegral_swap_fibre'` | ✅ proved |
| **`(★)` for a common cone direction** | `QFS.localPoincare_sameDirection` | ✅ **proved** |
| **`H_k ⊆ H^{α/2}` for a common cone direction** | `QFS.formHs_le_form_of_commonDirection` | ✅ **proved** |
| **The same, with both endpoints confined to a set `U`** — the diagonal blocks of the type decomposition | `QFS.localPoincare_sameDirection_on`, `QFS.formHs_le_form_of_commonDirection_on` | ✅ **proved** |
| **Every diagonal block of the canonical decomposition is controlled, by one constant** | `QFS.diagonal_blocks_of_bounded` | ✅ **proved** |
| **One intermediate point provably cannot do the cross blocks** | `QFS.no_common_neighbour_of_skew_axes`, `QFS.abs_inner_gt_of_mem_doubleCone` | ✅ **proved** (a disproof) |

The fibre estimate is what has to survive the exchange of the chaining average with the
integration in `t`, and it is why the argument is scale-invariant: the singular
weight comes back as exactly the weight of the `H_k` form on the pair `(s,z)`,
which the lower bound of (1.4) then converts into `k(s,z)`.

**How the same-direction case goes.** The chained integrand
`2(f(z)−f(s))² + 2(f(t)−f(z))²` is split, and each half is sent through the
exchange that handles it — `QFS.lintegral_swap_fibre` on the `s` side,
`QFS.lintegral_swap_fibre'` on the `t` side — with Tonelli in the outer pair
taken once in each order. The mirror statements are the same computation with
`⟪v, z − t⟫ ∈ [δ(3/sin ϑ − 2), δ(3/sin ϑ + 2)]` in place of
`⟪v, z − s⟫ ∈ [δ(3/sin ϑ − 1), δ(3/sin ϑ + 1)]`: the displacement from `s` to `t`
costs one extra unit and nothing else. Then `z − s ∈ Ṽ(v,ϑ) ⊆ Γ(s)` converts
`‖z−s‖^{-d-α}` into `Λ k(s,z)`.

The first input is the substantive one. The paper's Lemma 4.3 produces a *single*
intermediate point; a point is a null set and cannot absorb an average, so a
chaining argument needs a set of positive measure. The construction exploits
that `coneGap` increases by exactly `sin ϑ` per unit step along the axis
(`QFS.coneGap_add_smul_axis`, which the formalisation of §5 already needed):
walking `3‖s−t‖/sin ϑ` from `s` opens the cone past `3‖s−t‖`, leaving `‖s−t‖` of
room for the ball and `2‖s−t‖` to absorb the displacement from `s` to `t`.

**What is not proved, and is open.** Corollary 2.4 (`QFS.ref_config`) reduces a
configuration to finitely many cone types, splitting `ℝ^d` into measurable pieces
`U_1, …, U_L` and the `H^{α/2}` energy into `L²` blocks. The localised theorem
settles every **diagonal** block `U_m × U_m`. What remains is the `L² − L`
**cross** blocks `U_m × U_{m'}`, `m ≠ m'`, where the two endpoints admit no
common cone direction.

`QFS.diagonal_blocks_of_bounded` makes that precise: Corollary 2.4 supplies the
finite family of reference cones of aperture `ϑ/3`, Debreu's condition (as the
hypothesis `QFS.CondMeas`) makes the pieces measurable, and every diagonal block
is controlled by a *single* constant — `chainConst` depends on the aperture,
`ϑ/3` throughout, and not on the axis.

The cross case is not merely harder — one intermediate point provably cannot do it,
and `QFS.no_common_neighbour_of_skew_axes` proves so: in `ℝ³`, for `ϑ < π/4`, the
double cone about `e₁` at the origin and the one about `e₂` at `e₃` are
**disjoint**, so the set the averaging ball would live in is empty. Chains of
length at least two are unavoidable, and their middle edge runs between two
points whose cones the configuration assigns arbitrarily. That is the continuous
analogue of §§5–6, which the paper establishes only in the discrete setting;
going through `ℤ^d` is precisely how it avoids this.

The analytic machinery is stated abstractly enough to be reused: the exchange
asks only that a family of averaging sets have measurable graph and a fibre
bound (`QFS.lintegral_swap_of_fibre_bound`), so an attack on the cross blocks
need only supply a construction of averaging sets — the analysis is done.

Nothing here is claimed beyond what Lean checks: every row of the table above is
proved, including `(★)` and the inclusion `H_k ⊆ H^{α/2}` for a common cone
direction; the cross-type case is open and nothing here bears on it.

## Coverage: every numbered result in the paper

One row per numbered statement, including the ones not attempted. ✅ proved,
❗ disproved as printed, ⚪ prose remark with nothing to prove, 🚧 partly done or
blocked on a recorded gap, ❌ out of scope.

| # | Kind | Label | State |
| --- | --- | --- | --- |
| 1.1 | Theorem | main comparability, continuous | ⚪ statement recorded (`QFS.TheoremOneOne`), not proved |
| 1.2 | Remark | strength of the hypotheses | ⚪ (condition (M) is `QFS.CondM`) |
| 1.3 | Theorem | main comparability, discrete | ✅ **proved** (`QFS.theoremOneThree`) |
| 1.4 | Theorem | `H_k(Ω) = H^{α/2}(Ω)` | 🚧 the case `Ω = ℝ^d` **proved** granted Theorem 1.1 (`QFS.theoremOneFourUniv_of_theoremOneOne`); the Lipschitz-domain case needs Lemma 7.1, the density assertions are quoted from [DeDe12] |
| 1.5 | Corollary | regular Dirichlet form | ❌ out of scope |
| 1.6 | Corollary | Harnack / Hölder regularity | ❌ out of scope (quoted from [DyKa15]) |
| 2.1 | Definition | cones, half-cones, configurations | ✅ |
| 2.2 | Lemma | finitely many reference cones | ✅ |
| 2.3 | Definition | family of reference cones | ✅ |
| 2.4 | Corollary | finite-image subconfiguration | ✅ |
| 2.5 | Definition | cubes | ✅ |
| 2.6 | Remark | half-closed cubes used once | ⚪ |
| 2.7 | Lemma | cone in intersection | ✅ |
| 3.1 | Corollary | `hℤ^d` rescaling | ✅ **proved** (`QFS.corollaryThreeOne`) |
| 3.2 | Lemma | the indicator inequality | ✅ |
| 3.3 | Lemma | small cone inside `V^m_r` | ❗ false for `d = 1`; ✅ **proved for `d ≥ 2`** (`QFS.lemma_new_config`) |
| 3.4 | Lemma | `\|s−t\|` vs `\|x−y\|` | ✅ for `hℤ^d`; ❗ **false as printed** |
| 3.5 | Proposition | test-function bound | ✅ **proved** for `d ≥ 2` (`QFS.prop_test_fct`), with `QFS.CondMeas` as hypothesis |
| 3.6 | Corollary | the rescaled kernel | ✅ **proved** for `d ≥ 2` (`QFS.cor_rescaled_kernel`), with `QFS.CondMeas` as hypothesis |
| 3.7 | Lemma | comparability on a ball, `\|·\|_{H^{α/2}(B)} ≤ c\|·\|_{H_k(B)}` | 🚧 the target of §3.2. Its **final step is proved** (`QFS.formHs_le_form_of_theoremOneOneBall`): granted the enlarged-ball form and Lemma 7.1's quoted input, the same-ball form follows. What is missing is the enlarged-ball form, i.e. §3.2's remaining inclusion |
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
| 5.15 | Theorem | path properties | ✅ **proved** (`QFS.path_props`) |
| 5.16 | Lemma | the first jump | ✅ |
| 7.1 | Lemma | from balls to a bounded Lipschitz domain | 🚧 its chain (6.14) **proved** (`QFS.lemma_ball_to_domain`), including the finite-overlap step (`QFS.tsum_setLIntegral_le_of_overlap`); the Whitney family and Dyda's inequality (13) are hypotheses, as in the paper |
| 7.2 | Lemma | a Lebesgue differentiation argument | ✅ **proved** (`QFS.lemma_lebesgue_diff`) |

Sections 2, 4, 5 and 6 are formalised completely, apart from one remark of
Section 2 that the paper itself quotes rather than proves (see *Not attempted*).
Of Section 3, everything up to and including Corollary 3.6 is formalised; what
remains there is §3.2's qualitative inclusion `H_k(B*) ⊆ H^{α/2}(B*)` and
Lemma 3.7. From Section 1,
the function-space definitions, assumption (1.4), the reverse inequality and
equation (1.6) are proved, Theorem 1.3 is proved, and Theorem 1.1 is recorded as
a type-checked `Prop` alongside its enlarged-ball form.

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
| `A_h^m(u)`; `h`-favoured index by majority | §2 (prose before Lem. 2.7) | `QFS.cubeCone`, `QFS.IsFavoured` | ✅ defined |
| `A_h(u) = ⋃_i A_h^i(u)` | §2 | `QFS.cube_eq_biUnion_cubeCone` | ✅ proved |
| `λ_d(A_h^m(u)) ≥ L⁻¹ λ_d(A_h(u))` | §3 | `QFS.volume_cube_le_card_mul` | ✅ proved |
| The discrete form over an arbitrary lattice | Cor. 3.1 | `QFS.discreteFormOn`, `QFS.discreteForm_eq_discreteFormOn`, `QFS.discreteFormOn_congr`, `QFS.discreteFormOn_const_mul` | ✅ defined |
| `hℤ^d` as the image of `ℤ^d`; scaling as an equivalence | Cor. 3.1 | `QFS.smul_mem_scaledLattice`, `QFS.inv_smul_mem_lattice`, `QFS.smulEquiv` | ✅ proved |
| Cones are invariant under positive scaling | Cor. 3.1 | `QFS.smul_mem_doubleCone`, `QFS.smul_mem_doubleCone_iff` | ✅ proved |
| **The form and the kernel under `x ↦ hx`** | Cor. 3.1 | `QFS.discreteFormOn_smul`, `QFS.jumpKernel_smul`, `QFS.ofReal_rpow_mul_jumpKernel`, `QFS.preimage_smul_ball` | ✅ **proved** |
| **"every `ω ∈ M` is `h^{-d-α} ω̃(h⁻¹·, h⁻¹·)`"** | Cor. 3.1 | `QFS.discreteKernelBounds_rescale`, `QFS.indE_congr` | ✅ **proved** |
| **Corollary 3.1** | Cor. 3.1 | `QFS.corollaryThreeOne` | ✅ **proved** |
| The volume of a cube; cubes are measurable | §2, §3 | `QFS.cube_eq_preimage`, `QFS.measurableSet_cube`, `QFS.volume_cube` | ✅ proved |
| **The discrete kernel `ω^k_h`** | §3.1 | `QFS.discreteKernel` | ✅ **defined** |
| **The upper bound of Prop. 3.5 / Cor. 3.6(ii)** | §3.1 | `QFS.discreteKernel_le` | ✅ **proved** |
| A favoured index exists; Lemma 3.2 in `ℝ≥0∞` | §3.1 | `QFS.exists_isFavoured`, `QFS.lemma_min_dist_E`, `QFS.indE_le_indE`, `QFS.indE_eq_ofReal_ind` | ✅ proved |
| **The pointwise estimate of Prop. 3.5** | Prop. 3.5 | `QFS.discreteKernel_integrand_ge` | ✅ **proved** |
| Debreu's measurability, as a hypothesis | §2, Prop. 3.5 | `QFS.CondMeas`, `QFS.measurableSet_cubeCone` | ✅ stated |
| Integrating the estimate; the `1/L` share | Prop. 3.5 | `QFS.discreteKernel_ge_volume`, `QFS.inv_card_le_volume_cubeCone` | ✅ proved |
| **Proposition 3.5**, with the paper's `α`-free constant | Prop. 3.5 | `QFS.prop_test_fct` | ✅ **proved** (`d ≥ 2`) |
| The upper bound with an `α`-free constant | Prop. 3.5, Cor. 3.6 | `QFS.discreteKernel_le'` | ✅ proved |
| Lemma 3.2 and the cube step, at scale `h` | Cor. 3.6 | `QFS.cube_subset_of_mem_shift_shrink_scaled`, `QFS.lemma_min_dist_scaled`, `QFS.lemma_min_dist_E_scaled` | ✅ proved |
| Shrinking commutes with scaling; Lemma 3.3 on `hℤ^d` | Cor. 3.6 | `QFS.mem_shrink_smul`, `QFS.thin_cone_subset_scaled`, `QFS.sub_mem_scaledLattice` | ✅ proved |
| Proposition 3.5's estimate at scale `h` | Cor. 3.6 | `QFS.discreteKernel_integrand_ge_scaled`, `QFS.discreteKernel_ge_volume_scaled`, `QFS.inv_card_le_volume_cubeCone_scaled` | ✅ proved |
| **Corollary 3.6** | Cor. 3.6 | `QFS.cor_rescaled_kernel` | ✅ **proved** (`d ≥ 2`) |
| Cubes are closed / open; a cube containing `x` lies in `B̄_{h√d}(x)` | Lem. 7.2 | `QFS.continuous_coord`, `QFS.isClosed_closedCube`, `QFS.isOpen_cube`, `QFS.closedCube_subset_closedBall_of_mem` | ✅ proved |
| **The Vitali family of cubes** | Lem. 7.2 | `QFS.unitBallVol`, `QFS.volume_closedBall_eq`, `QFS.cubeVitaliConst`, `QFS.cubeVitali_doubling`, `QFS.cubeVitali`, `QFS.closedCube_mem_setsAt`, `QFS.tendsto_closedCube_filterAt` | ✅ **proved** |
| **Lemma 7.2**: differentiation along cubes | Lem. 7.2 | `QFS.lemma_lebesgue_diff` | ✅ **proved** |
| **The half-closed cubes tile `ℝ^d`** | §3.2 | `QFS.existsUnique_mem_halfClosedCube` | ✅ **proved** |
| **The tiling as a countable measurable partition** | §3.2 | `QFS.latticePt`, `QFS.latticePt_injective`, `QFS.halfClosedCube_eq_preimage`, `QFS.measurableSet_halfClosedCube`, `QFS.volume_halfClosedCube`, `QFS.iUnion_halfClosedCube`, `QFS.pairwiseDisjoint_halfClosedCube` | ✅ **proved** |
| **The step index `x_h(s)`** | §3.2 | `QFS.stepIndex`, `QFS.stepIndex_mem_scaledLattice`, `QFS.mem_halfClosedCube_stepIndex`, `QFS.mem_closedCube_stepIndex`, `QFS.stepIndex_eq_of_mem`, `QFS.halfClosedCube_subset_closedCube` | ✅ **proved** |
| **`f_h(x_h(s)) → f(s)` almost everywhere** | §3.2 | `QFS.tendsto_avg_stepIndex`, `QFS.tendsto_avg_stepIndex_indicator` | ✅ **proved** |
| **A step function integrates to `∑ c(x)·h^d`** | §3.2 | `QFS.lintegral_eq_tsum_halfClosedCube`, `QFS.lintegral_stepFun` | ✅ **proved** |
| **The tile-averaging operator, and that it preserves the integral** | §3.2 | `QFS.tileAvg`, `QFS.lintegral_tileAvg` | ✅ **proved** |
| **Generalized (Vitali) dominated convergence, dominants allowed to move** | §3.2 | `QFS.limsup_lintegral_le_of_dominant` | ✅ **proved** |
| **A Lipschitz function has finite `H^{α/2}` seminorm on a ball (`α < 2`)** | §3.2 | `QFS.formHs_lt_top_of_lipschitzOn`, `QFS.lintegral_ball_rpow_lt_top` | ✅ **proved** |
| **Pairs in a common tile; the tiling of pairs** | §3.2 | `QFS.sameTile`, `QFS.sameTile_eq_iUnion`, `QFS.measurableSet_sameTile`, `QFS.norm_sub_le_of_sameTile`, `QFS.coneSet` | ✅ **proved** |
| **On close cone pairs the kernel dominates the flat measure** | §3.2 (new) | `QFS.lintegral_sq_le_form_of_close` | ✅ **proved** |
| **The cone part of the modulus `A_h` is bounded uniformly in `h`** | §3.2 (new) | `QFS.oscillation_sameTile_le_form` | ✅ **proved** |
| **Granted Theorem 1.1, an approximation bounded on `H^{α/2}` is bounded on `H_k`** — the circularity in the mollification route | §3.2 | `QFS.form_le_of_theoremOneOneBall` | ✅ **proved** |
| **The form on `ℝ^d` as a supremum over balls** | Thm. 1.4 | `QFS.lintegral_univ_prod_eq_iSup`, `QFS.form_univ_eq_iSup` | ✅ **proved** |
| **Theorem 1.4 for `Ω = ℝ^d`**, granted Theorem 1.1 | Thm. 1.4 | `QFS.TheoremOneFourUniv`, `QFS.theoremOneFourUniv_of_theoremOneOne`, `QFS.form_univ_le_formHs_univ` | ✅ **proved** |
| **The finite-overlap estimate** of (6.14) | Lem. 7.1 | `QFS.tsum_setLIntegral_le_of_overlap`, `QFS.tsum_setLIntegral_le_of_overlap_sq` | ✅ **proved** |
| **The chain (6.14)**, with the Whitney family and Dyda's inequality as hypotheses | Lem. 7.1 | `QFS.lemma_ball_to_domain` | ✅ **proved** |
| **The quoted Whitney/Dyda input for a ball**, and that it is satisfiable | Lem. 7.1 | `QFS.WhitneyBallData`, `QFS.whitneyBallData_one` | ✅ **stated, non-vacuous** |
| **Enlarged ball ⟹ same ball**: the last step of §3.2 | §3.2, Lem. 7.1 | `QFS.formHs_le_form_of_theoremOneOneBall` | ✅ **proved** |
| **Lemma 3.2**: the indicator inequality | Lem. 3.2 | `QFS.lemma_min_dist`, `QFS.lemma_min_dist_favoured` | ✅ **proved** |
| **Lemma 3.3** fails in `d = 1` for `r = √d` | Lem. 3.3 | `QFS.lemma_new_config_false_dim_one` | ✅ **disproved** (`d=1`) |
| The lattice is closed under negation | (new) | `QFS.neg_mem_lattice` | ✅ proved |
| Only finitely many lattice points in a ball | §3, §5.2 | `QFS.lattice_inter_closedBall_finite` | ✅ proved |
| **An orthogonal unit vector, for `d ≥ 2`** | Lem. 3.3 | `QFS.exists_orthogonal_unit` | ✅ **proved** |
| Rotating the axis inside the cone | Lem. 3.3 | `QFS.rotAxis`, `QFS.inner_rotAxis`, `QFS.norm_rotAxis`, `QFS.angle_rotAxis` | ✅ proved |
| **Lemma 3.3 for `d ≥ 2`, one cone** | Lem. 3.3 | `QFS.exists_thin_cone_subset` | ✅ **proved** |
| **Lemma 3.3 for `d ≥ 2`, the paper's form** | Lem. 3.3 | `QFS.lemma_new_config` | ✅ **proved** |
| Ball inside a cone: `‖u − tv‖ < t sin ϑ ⟹ u ∈ Ṽ` | §4–5 (implicit) | `QFS.mem_cone_of_norm_sub_lt` | ✅ proved |
| Cones of apex `≤ π/2` are convex | (new; used for §4) | `QFS.convex_cone` | ✅ proved |
| `V[x] ∩ V[y] ≠ ∅` for one double cone | Lem. 4.3 proof | `QFS.shift_inter_shift_nonempty` | ✅ proved |
| The graph `G[U]`; undirected connectivity | §4 | `QFS.Edge`, `QFS.Conn` | ✅ defined |
| Type of a point | Def. 4.2 | `Γ x = Γ y` | ✅ defined |
| **Lemma 4.3**: same type ⟹ path of length ≤ 2 | Lem. 4.3 | `QFS.connect_two_of_same_type_two` (with the length bound), `QFS.connect_two_of_same_type` | ✅ **proved** |
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
| The enlarged-ball form of Theorem 1.1 | §3.2 | `QFS.TheoremOneOneBall` | ⚪ stated, not proved |
| **Non-vacuity of the hypotheses** | (new) | `QFS.constConfig`, `QFS.isBounded_constConfig`, `QFS.condMeas_constConfig`, `QFS.indE_add_indE_le_two`, `QFS.kernelBounds_jumpKernel`, `QFS.discreteKernelBounds_jumpKernel`, `QFS.theoremOneThree_nonvacuous` | ✅ **proved** |
| Statement of Theorem 1.3 | Thm. 1.3 | `QFS.discreteForm`, `QFS.TheoremOneThree` | ✅ stated |
| **Theorem 1.3** | Thm. 1.3, §6 | `QFS.theoremOneThree` | ✅ **proved** |
| Telescoping and Cauchy–Schwarz along a walk | §6 | `QFS.walk_telescope`, `QFS.list_sq_sum_le`, `QFS.walk_sq_le` | ✅ proved |
| A walk stays within its total length of its start | §6 | `QFS.norm_sub_start_le` | ✅ proved |
| **Assumption (1.7) at an edge of `G`** | §6 | `QFS.jumpKernel_le_of_dart` | ✅ **proved** |
| **The chain estimate for one pair** | §6 | `QFS.chain_estimate` | ✅ **proved** |
| Both sides are finite sums | §6 | `QFS.pairSet`, `QFS.pairSet_finite`, `QFS.discreteForm_eq_sum`, `QFS.tsum_subtype_eq_finset_sum` | ✅ proved |
| A list sum against the values it takes | §6 | `QFS.list_sum_le_card_mul_sum`, `QFS.ofReal_list_sum` | ✅ proved |
| **Step 6's double counting, as a sum bound** | §6 | `QFS.sum_select_le`, `QFS.card_le_of_encard_le` | ✅ **proved** |
| Dimension `0` is degenerate | §6 | `QFS.discreteForm_dim_zero` | ✅ proved |
| **Theorem 5.15 with edges longer than `R₀`** | Thm. 5.15 (strengthened) | `QFS.PathPropsLong`, `QFS.PathPropsLongHolds`, `QFS.path_props_long` | ✅ **proved** |
| Forgetting the extra clause; transfer along `Γ' ≤ Γ` | Thm. 5.15 | `QFS.PathPropsLong.toPathProps`, `QFS.PathPropsLongHolds.toPathPropsHolds`, `QFS.PathPropsLong.mono_config` | ✅ proved |
| Every `√d/2`-ball holds a lattice point | §5.1 preamble | `QFS.exists_lattice_mem_closedBall` | ✅ proved |
| Paths not leaving a set | Def. 5.3 | `QFS.ConnWithin` | ✅ defined |
| **Lemma 5.1 (1), (2)**: lattice points in cones | Lem. 5.1 | `QFS.exists_lattice_mem_cone`, `QFS.exists_lattice_mem_inter` | ✅ **proved** |
| **Corollary 5.2**: discrete same type | Cor. 5.2 | `QFS.discr_connect_two_of_same_type_two` (two edges, each shorter than `R`), `QFS.discr_connect_two_of_same_type` | ✅ **proved** |
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
| Statement of Theorem 5.15 | Thm. 5.15 | `QFS.PathProps`, `QFS.PathPropsHolds` | ✅ stated |
| **Theorem 5.15** | Thm. 5.15 | `QFS.path_props` | ✅ **proved** |
| Theorem 5.15, Steps 3–6 | Thm. 5.15 | `QFS.pathPropsLong_of_scaleData`, `QFS.pathPropsHolds_of_scaleData`, `QFS.pathPropsLongHolds_of_scaleData` | ✅ proved |
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
| Centres containing an edge: finitely many | Thm. 5.15, Step 6 | `QFS.lattice_scaled_ball_subset`, `QFS.lattice_scaled_ball_finite` | ✅ proved |
| **Scale selection**: `L ≥ 1` lies in one window | Thm. 5.15, Step 3 | `QFS.exists_scale` | ✅ **proved** |
| Centre selection: `x` is near `sℤ^d` | Thm. 5.15, Step 3 | `QFS.exists_centre` | ✅ proved |
| **Step 3 of Theorem 5.15** | Thm. 5.15, Step 3 | `QFS.exists_scale_of_lattice`, `QFS.exists_scale_and_centre`, `QFS.exists_admissible` | ✅ **proved** |
| The length of an unoriented edge | Thm. 5.15, claim (4) | `QFS.edgeLen`, `QFS.edgeLen_mk`, `QFS.dart_edge_mem_edges` | ✅ defined |
| The admissible pairs `A` of Step 2 | Thm. 5.15, Step 2 | `QFS.Admissible` | ✅ defined |
| **The local data of Steps 1–2** | Thm. 5.15, Steps 1–2 | `QFS.ScaleData` | ✅ **defined** |
| Step 5's upper bound, from `edge_near` | Thm. 5.15, Step 5 | `QFS.ScaleData.edgeLen_lt` | ✅ proved |
| The fibre bound on the lattice as a type | Thm. 5.15, Step 6 | `QFS.ScaleData.fibre_le_latticePt` | ✅ proved |
| **Steps 3–6: the assembly** | Thm. 5.15, Steps 3–6 | `QFS.pathPropsLong_of_scaleData` | ✅ **proved** |
| **Theorem 5.15 from Steps 1–2** | Thm. 5.15 | `QFS.pathPropsHolds_of_scaleData` | ✅ **proved** |
| Balanced hashes; the paper's "WLOG `#` majority set `= a`" | Thm. 5.15, Step 2 | `QFS.exists_hash`, `QFS.exists_indexed_rep` | ✅ proved |
| The one-point part of admissibility | Thm. 5.15, Step 2 | `QFS.AdmissiblePt`, `QFS.Admissible.left`, `QFS.Admissible.right` | ✅ defined |
| **What an edge reveals about its pair** | Thm. 5.15, Step 6 | `QFS.Reveals`, `QFS.encard_reveals_le` | ✅ **proved** |
| **The local data of Steps 1–2** | Thm. 5.15, Steps 1–2 | `QFS.BlockData` | ✅ **defined** |
| **Step 2: the assembly** | Thm. 5.15, Step 2 | `QFS.scaleData_of_blockData` | ✅ **proved** |
| Block separation, and disjointness | Thm. 5.15, Step 5 | `QFS.infNorm_smul_sub_lattice`, `QFS.block_sep`, `QFS.block_disjoint` | ✅ proved |
| The index is recoverable from its representative | Thm. 5.15, Step 6 | `QFS.exists_retraction` | ✅ proved |
| **The paper's `a = Δ^{d(n−1)}/L`** | Thm. 5.15, Step 2 | `QFS.schemeIndex`, `QFS.pow_le_mul_schemeIndex`, `QFS.schemeIndex_le` | ✅ **proved** |
| A natural multiple of a lattice point | (new) | `QFS.nsmul_mem_lattice` | ✅ proved |
| **The ball holds `≲ Δ^{md}` admissible points** | Thm. 5.15, Step 2 | `QFS.encard_admissiblePt_le` | ✅ **proved** |
| **The majority set has `≥ a` points** | Thm. 5.15, Step 2 | `QFS.schemeIndex_le_ncard_blockFibre` | ✅ **proved** |
| **Steps 1 and 2** | Thm. 5.15, Steps 1–2 | `QFS.exists_blockData` | ✅ **proved** |
| Edges come from darts; the graph shrinks with `Γ` | (new) | `QFS.exists_dart_edge`, `QFS.latticeGraph_mono` | ✅ proved |
| **Theorem 5.15 transfers along `Γ' ≤ Γ`** | Cor. 2.4 + Thm. 5.15 | `QFS.PathProps.mono_config` | ✅ **proved** |

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
   1.3 hold trivially.

   **For `d ≥ 2` the lemma is true, and it is proved here** — but not obviously,
   and the argument is not in the paper. `QFS.exists_thin_cone_subset` is the
   single-cone version and `QFS.lemma_new_config` the paper's form, with one
   apex angle for the whole family. The construction:

   * `V^m_r` omits every point within `r` of the boundary of `V^m`, in
     particular every point of norm at most `r/sin θ_m`. Only finitely many
     lattice points are that short (`QFS.lattice_inter_closedBall_finite`), so
     the axis must avoid their directions.
   * `QFS.exists_orthogonal_unit` produces a unit vector orthogonal to the axis.
     **This is the only place `d ≥ 2` is used**, and it is exactly what fails in
     `d = 1`: with no orthogonal direction the cone cannot be made thin.
   * `QFS.rotAxis u w t = cos t · u + sin t · w` rotates the axis inside the
     cone, with `angle u (rotAxis u w t) = t` (`QFS.angle_rotAxis`). Each short
     lattice point is parallel to at most one rotation, because a rotation is
     determined by its angle to `u`; an interval of rotations is infinite
     (`Set.Ioo_infinite`) while the short lattice points are finite, so some
     rotation avoids all of them.
   * The apex angle is then taken below the least of the resulting angles. A
     lattice point of the resulting thin cone is therefore *long* — longer than
     `r/sin(ϑ/4)` — and *nearly parallel* to `u`, and
     `QFS.coneGap_eq_norm_mul_sin` turns that into a gap of more than `r` to the
     boundary of `V^m`, which is membership in `V^m_r`
     (`QFS.closedBall_subset_cone`).

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

16. **Step 2's assignment `φ_z` is too weak for Step 6, and the paper's own
    scheme repairs it.** This is the one substantive gap found in Section 5.

    Step 2 asks only that `φ_z : A → M` be *globally* balanced,
    `#φ_z⁻¹(p) ≤ K`, and Step 6 then asserts that "the usage of paths that start
    in some point `x` and end in some other point `y` … is bounded by `K`". That
    does not follow. Consider the **first-jump edge** `{x, q}`, where `q` is the
    vertex of `φ_z(x, y)` lying in `x`'s own block. It is used by every partner
    `y` of `x` whose assigned walk carries `q`'s index at `x`'s position along
    the block walk. The walks with a fixed index at a fixed position number `a`,
    so their total capacity under a merely balanced `φ_z` is `K a`, which is
    larger than the `≍ Δ^{nd}` partners `x` has. An adversarial balanced `φ_z`
    may therefore route all of them through the single edge `{x, q}`, and its
    multiplicity is unbounded in the scale. Claim (3) fails for that `φ_z`.

    The repair stays inside the paper's scheme and only *fixes its parameters*.
    Take two maps `f, g` of the ball to `ZMod a`, each with fibres of size at
    most `K₁` (`QFS.exists_hash`), and set

    > `i = f(y) + g(x)` and `i + j = g(x)`,

    so that the scheme's alternating labels are `α = f(y) + g(x)` at odd
    positions and `β = g(x)` at even ones. Then

    * every consecutive pair `{α, β}` determines `g(x) = β` and
      `f(y) = α − β`, so an interior edge is used by at most `K₁²` pairs — this
      is `QFS.cyclic_pair_injective` in its intended role;
    * at `x`'s end the label is a translate of `f`, hence balanced in `y` for
      fixed `x`, bounding the first-jump edge at `x` by `K₁`;
    * at `y`'s end the label is `α` or `β`, and *both* are translates of `g`,
      hence balanced in `x` for fixed `y`, bounding the first-jump edge at `y` —
      **whatever the parity** of the block walk's length.

    The last point is why `α` must carry both hashes. With the more obvious
    choice `α = f(y)`, `β = g(x)` an even-length block walk ends on `α`, which
    is constant in `x`, and the multiplicity at `y`'s end is again unbounded.
    Since the choice-graph may be bipartite, one cannot arrange the parity away.

    `QFS.encard_reveals_le` is the resulting count: whichever of the three
    shapes an edge has, it confines `g(x)` to eight values and `f(y)` to nine,
    all computed from the edge alone, so at most `72 K₁²` pairs used it.

    A second, purely simplifying consequence: once the scheme's parameters are
    functions of `x` and `y` alone, the walk for a pair need not be a sub-walk
    of one *global* covering walk, so Step 1 is used only in its pairwise form
    (Proposition 5.14 plus `QFS.exists_choiceWalk_of_choiceConn`). Step 1 as the
    paper states it is nevertheless proved, as
    `QFS.exists_favoredWalk_covering` and `QFS.exists_choiceWalk_covering`.

17. **Section 6's chaining needs edges longer than `R₀`, and claim (4) does not
    give it.** The computation displayed in Section 6 applies the *lower* bound
    of assumption (1.7) at each edge `{z_i, z_{i+1}}` of `p_xy`, to replace
    `|z_{i+1} − z_i|^{-d-α}` by `Λ ω(z_i, z_{i+1})`. That bound is only assumed
    for `|x − y| > R₀`. But claim (4) of Theorem 5.15 bounds an edge below only
    by `λ^{-1}|x − y|`, and `λ ≥ R₀`, so for a pair with `|x − y|` just above
    `R₀` the guaranteed edge length is about `R₀/λ ≤ 1` — well short of `R₀`.
    Restricting to pairs with `|x − y| > λR₀` does not help either: the pairs
    with `R₀ < |x − y| ≤ λR₀` still need chains, and `ω(x, y)` may vanish for
    them, since the indicator in (1.7) is `0` unless one point lies in the
    other's cone.

    The repair is in the construction, not in the estimate. Theorem 5.15 routes
    a pair at the scale `n` with `|x − y| ∈ [Δ^{n-1}, Δ^n)`, and at the bottom
    scale `n = 1` the town is `T(Δ, 1)`, whose edges can be as short as `1`.
    Routing **one scale up** — the admissible window becomes `[Δ^{m-1}, Δ^m)`
    with `m ≥ 1`, which is `QFS.Admissible` — makes every edge at least
    `Δ^m ≥ Δ` long, and `Δ > R₀` by `QFS.ScaleStep`. The cost is a factor `Δ` in
    `λ`, which becomes `2Δ²R`.

    `QFS.PathPropsLong` is Theorem 5.15 with the extra clause `R₀ < |edge|`, and
    `QFS.path_props_long` proves it; `QFS.PathPropsLong.toPathProps` forgets the
    clause, so `QFS.path_props` still records exactly the paper's statement.

18. **The `λ`-observation in the proof of Theorem 4.1 is false as printed.** The
    proof opens the case `#Γ(U) > 1` with

    > There is a constant `λ > 0` depending only on the minimum apex angle `ϑ`
    > such that for **any double cone `V ∈ 𝒱`** and any two points `x, y ∈ ℝ^d`
    > of distance `|x − y| < λ`, the intersection `V[x] ∩ V[y]` contains a point
    > in `B_1(x)`.

    But `𝒱 = (0, π/2] × ℙ^{d-1}` contains cones of arbitrarily small apex, and
    for a cone of apex `ε` the points of `V[x] ∩ V[y]` are at distance about
    `|x − y| / (2 sin ε)` from `x`. With `λ` fixed in advance by `ϑ`, no such
    `λ` works for all `V ∈ 𝒱`. The observation is only ever *applied* to
    `V = Γ(y)`, whose apex is at least `ϑ`, so the repair is to say so:
    `QFS.exists_mem_ball_inter_shift` carries `ϑ ≤ V.apex`, and with it the
    paper's constant `λ = (sin ϑ)/2` is correct.

19. **Four smaller slips in printed statements, each repaired silently.**

    * **Definition 2.3** writes `V^m_r = {u ∈ V^m | B̄_r ⊂ V^m}` — the ball has
      no centre, so read literally `V^m_r` is `V^m` or `∅`. Definition 2.1
      writes the same condition correctly as `B̄_r(y) ⊂ V`.
      `QFS.RefFamily.shrunk` uses the centred version.
    * **Lemma 5.9** says "there is a constant `δ = δ(ϑ)`", but its own value
      `3√d/(2 sin ϑ)` depends on `d` as well. `QFS.apexShrinkConst d ϑ` takes
      both, as it must.
    * **Proposition 5.14** says "there exists `R ≥ r` depending only on `ϑ` and
      `d`", but `R ≥ r` cannot be independent of `r`. `QFS.renormalization`
      takes `r` first, as Corollary 5.8 correctly states.
    * **Definition 5.3** restricts to `r ≤ R` and `x ∈ ℤ^d`; `QFS.RRConnected`
      imposes neither, which only widens the definition and is never used.

    Two more definitional notes, neither a defect: `QFS.CondM` asks for
    measurability with respect to the ambient `MeasurableSpace` instance, which
    for `EuclideanSpace ℝ (Fin d)` is the Borel σ-algebra the paper names; and
    `QFS.RefFamily` does not constrain its apex angle `θ` to `(0, π/2]`, which
    only weakens the hypothesis of everything proved from it.

20. **Two further notes on hypotheses, neither a defect.** Theorem 1.3's
    dependency sentence — "the constant `c` depends on `Λ`, `ϑ`, `R₀` and on the
    dimension `d`" — omits `α`, but the paper's own proof produces `λ^{d+α}`, so
    `c` does depend on `α`. `QFS.TheoremOneThree` quantifies `κ` and `c` after
    `α`, which is what the proof supports. And Proposition 3.5 assumes `k`
    measurable; `QFS.KernelBounds` does not, because the argument runs entirely
    through the lower Lebesgue integral and never needs it — a weaker hypothesis,
    hence a stronger result. That omission does bite once, and only once:
    `QFS.formHs_le_form_of_theoremOneOneBall` carries measurability of the
    integrand as an explicit hypothesis, because summing the forms over a Whitney
    family goes through `lintegral_tsum`, which needs it.

21. **Lemma 7.1's overlap constant can be `M`, not `M²`.** Display (6.14) bounds
    `∑_{B∈ℬ} ∫_{B*×B*} … ≤ M² ∫_{Ω×Ω} …` from the finite-overlap property
    "each point of `Ω` belongs to at most `M` balls `B*`". One factor suffices: a
    pair `(x,y)` lies in `B* × B*` only for those `B` with `x ∈ B*`, of which
    there are at most `M`. `QFS.tsum_setLIntegral_le_of_overlap` proves the sharper
    form and `QFS.tsum_setLIntegral_le_of_overlap_sq` the printed one. Nothing
    downstream depends on the difference.

22. **Two rows of this README were mislabelled, and are corrected.** The coverage
    table described Lemma 7.1 as an "auxiliary integral estimate" and marked
    Lemma 3.7 "out of scope". Re-reading the source with the numbering settled
    (`\newtheorem{theorem}{Theorem}[section]`, one counter per section) shows that
    **Lemma 7.1 is `lem:new6.9`**, the passage from balls to a bounded Lipschitz
    domain, and **Lemma 3.7 is `lem:H-are-equal-on-balls`**, the same-ball
    comparability that §3.2 exists to prove — not an out-of-scope aside but the
    section's target. Both rows now say so. The prose elsewhere in this file had
    the dependency right; only the table was wrong.

## What remains

The repository now proves every link in the chain from the discrete theory to
Theorem 1.1 except one, and that one is a single statement:

> **Open.** Every `f ∈ H_k(B*)` already lies in `H^{α/2}(B*)`.

It is enough to prove something weaker. Decomposing
`f_h(x) − f_h(y) = (f_h(x) − f(s)) + (f(s) − f(t)) + (f(t) − f_h(y))`, weighting by
`k(s,t)` and summing over the pairs, the middle term contributes
`|f|²_{H_k(B*)}` and each outer term contributes `‖f − E_hf‖²_{L²(B*)}` times
`sup_s ∫_{|s−t|>h/2} k(s,t)dt = O(Λ h^{-α})`:

  `∫∫ g_h ≤ 9|f|²_{H_k(B*)} + C(d,α,Λ)·A_h`,   `A_h := h^{-α}‖f − E_hf‖²_{L²(B*)}`.

Fatou on the left of `(discret)` then closes the theorem — with **no** dominated
convergence and no limit on the right — as soon as

> **Enough.** `liminf_{h→0} h^{-α}‖f − E_hf‖²_{L²(B*)} < ∞` for `f ∈ H_k(B*)`.

An attempt on this, which is **new mathematics rather than formalisation**, is in
`BeyondThePaper.lean`; see *Beyond the paper* above for what it does and does not
establish.

`A_h` is an `L²` modulus of continuity at one scale, a Besov `B^{α/2}_{2,∞}`
quantity with no singular kernel in it — strictly weaker than the
`B^{α/2}_{2,2} = H^{α/2}` membership the paper's argument silently assumes.

**Half of it is proved.** `A_h` splits into a cone part and an off-cone part, and
`QFS.oscillation_sameTile_le_form` bounds the cone part by `Λ d^{(d+α)/2}|f|²_{H_k}`,
uniformly in `h`. The mechanism is that the lower bound of (1.4) is used in the
one direction that costs nothing: on pairs at distance `≤ r` the singular kernel
is bounded *below* by `Λ^{-1}r^{-d-α}`, so it dominates the flat measure
(`QFS.lintegral_sq_le_form_of_close`); with `r = √d·h` and the tiles of the
`h`-tiling, the powers of `h` cancel exactly.

**What is left** is the off-cone oscillation inside a single tile: for `s,t` in one
cube of side `h` with `t ∉ V^Γ[s]`, the difference `f(s) − f(t)` has to be
recovered by chaining through cone pairs. That is precisely what §§4–6 achieve —
but in the discrete setting, where a tile is a single point and the oscillation
inside it is invisible. Discretising to apply Theorem 1.3 destroys the very
quantity to be estimated, which is why the two-scale attempts recurse the wrong
way (they bound `A_h` by `A_{h'}` for `h' < h`).

For a **constant** configuration the statement is true and easy: if `Γ ≡ V` then
`f ∈ H_k` says `∫_{z ∈ V}|z|^{-d-α}‖f(·+z) − f‖²_{L²}dz < ∞`, and on the Fourier
side `∫_V |z|^{-d-α}|e^{iξ·z} − 1|²dz = |ξ|^α J(ξ/|ξ|)` with `J` continuous and
strictly positive on the sphere (it vanishes only if `e^{iθ·w} = 1` throughout a
cone with interior), so the cone-restricted energy is comparable to the full one.
Every difficulty is in the variation of `Γ` from point to point, which is exactly
what Corollary 2.4 tames only down to *finitely many* cone types, on measurable
pieces that admit no Fourier transform.

The chain, with each link's status:

| Step | Status |
| --- | --- |
| Theorem 1.3 (discrete comparability) | ✅ `QFS.theoremOneThree` |
| Corollary 3.1 (rescaled to `hℤ^d`) | ✅ `QFS.corollaryThreeOne` |
| Proposition 3.5, Corollary 3.6 (the discrete kernel `ω^k_h`) | ✅ `QFS.prop_test_fct`, `QFS.cor_rescaled_kernel` (`d ≥ 2`, with `QFS.CondMeas`) |
| §3.2: the step functions and their convergence | ✅ `QFS.tendsto_avg_stepIndex`, `QFS.lintegral_stepFun` |
| §3.2: Fatou on the left of `(discret)` | ✅ available (`lintegral_liminf_le`) |
| §3.2: dominated convergence on the right, **for `f ∈ H^{α/2}(B*)`** | ✅ `QFS.lintegral_tileAvg`, `QFS.limsup_lintegral_le_of_dominant` |
| §3.2: removing that hypothesis | ❌ **the open statement above** |
| Enlarged ball ⟹ same ball (Lemma 7.1 for a ball) | ✅ `QFS.formHs_le_form_of_theoremOneOneBall`, modulo the quoted `QFS.WhitneyBallData` |
| Lemma 3.7, Theorem 1.1 | follows from the two lines above |
| Theorem 1.4 on `ℝ^d` | ✅ `QFS.theoremOneFourUniv_of_theoremOneOne` |
| Theorem 1.4 on a Lipschitz domain | follows from Lemma 7.1 for domains (`QFS.lemma_ball_to_domain`) |

Everything else outstanding is an input the paper itself quotes — Debreu's
measurability, the Whitney decomposition, Dyda's inequality (13), the density
results of [DeDe12], the regularity results of [DyKa15] — each carried here as a
named hypothesis rather than assumed silently, or Corollary 1.5, which needs
Dirichlet-form theory that Mathlib does not have.

## Not attempted

Recorded here rather than silently omitted. What is not formalised is the
continuous half of the paper — Theorem 1.1 and everything downstream of it —
together with the results the paper itself quotes from elsewhere.

| Result | Paper | Why not |
| --- | --- | --- |
| Comparability on balls, continuous | Thm. 1.1 | Needs §3's discrete kernel and limiting argument, and a final step the paper quotes from a Whitney decomposition and Dyda's inequality (13). Statement recorded as `QFS.TheoremOneOne`. |
| `H_k(Ω) = H^{α/2}(Ω)`, density | Thm. 1.4 | Depends on Thm. 1.1 and on Lipschitz-domain extension theory not in scope. |
| Regular Dirichlet form; Markov process | Cor. 1.5 | Depends on Thm. 1.1 and on Dirichlet-form theory (Fukushima–Oshima–Takeda) absent from Mathlib. This is the one result here whose obstacle is the library rather than the paper. |
| Weak Harnack, Hölder regularity | Cor. 1.6 | Quoted from Dyda–Kassmann; not proved in the paper. |
| The Whitney decomposition of a bounded Lipschitz domain | Lem. 7.1 | Asserted, not proved: "The Whitney decomposition technique provides a family `ℬ` of balls with the following properties." Carried as the hypotheses of `QFS.lemma_ball_to_domain`. |
| Dyda's inequality (13) | Lem. 7.1 | Quoted from [Dyda06, proof of Thm. 1]; carried as the hypothesis `hdyda` of `QFS.lemma_ball_to_domain`. |
| Density of `C^∞(Ω̄)` and `C_c^∞(ℝ^d)` in `H^{α/2}` | Thm. 1.4 | Quoted from [DeDe12, Props. 4.52 and 4.27]. |
| `H_k` on balls | Lem. 3.7 | Depends on Cor. 3.6. |
| `{x | V ⊆ Γ(x)}` is Lebesgue measurable | §2 (after Cor. 2.4) | The paper does not prove it — "This implication is due to [Debreu67, Thm. 4.4]". It is what makes the sets `A_h^m(u)` measurable, which Proposition 3.5 integrates over, so it is carried there as the explicit hypothesis `QFS.CondMeas`. |
| Auxiliary integral estimate | Lem. 7.1 | An integral computation feeding the appendix lemma, which is itself quoted rather than proved. |
| The passage to the limit `h → 0` | §3.2 | Not formalised, but reduced to one qualitative statement; see the note below. The discrete estimates it feeds on (Corollaries 3.1 and 3.6), the almost-everywhere convergence `f_h(x_h(s)) → f(s)` (`QFS.tendsto_avg_stepIndex`), the identity turning the sums into integrals (`QFS.lintegral_stepFun`) and **the paper's dominated-convergence step itself, for `f ∈ H^{α/2}(B*)`** (`QFS.lintegral_tileAvg`, `QFS.limsup_lintegral_le_of_dominant`) are all proved. What is missing is that every `f ∈ H_k(B*)` already lies in `H^{α/2}(B*)`. |

### §3.2's dominated convergence, and what is left of it

Section 3.2 passes from the discrete inequality `(discret)` to the continuous
one by letting `h → 0`. On the left it uses Fatou, which needs nothing extra. On
the right it writes

> For the right hand side in (discret) this implies with help of dominated
> convergence … `∫ g_h → ∫ g`

without exhibiting a dominating function. No fixed dominant exists, and the
obvious candidates fail:

* bounding `f_h(x)` by the Hardy–Littlewood maximal function `Mf` gives
  `(Mf(s) + Mf(t))² k(s,t)`, whose integral over `B* × B*` need not be finite —
  the factor does not vanish on the diagonal, where `k` is not integrable;
* applying Jensen to `(f_h(x) − f_h(y))²` and using Lemma 3.4 leads back to
  `|f|_{H^{α/2}(B*)}`, which is the quantity being bounded.

**The step is nonetheless repairable, and the repair is formalised.** What
dominated convergence needs is not a *fixed* dominant but a sequence of them
whose integrals converge, and the tile-averaging operator supplies exactly that:

| | Lean |
| --- | --- |
| `E_h Φ(s) = ⨍_{tile ∋ s} Φ`, the conditional expectation onto the tiling | `QFS.tileAvg` |
| `∫ E_h Φ = ∫ Φ` — averaging preserves the integral, so the dominants all have the *same* integral | `QFS.lintegral_tileAvg` |
| the generalized (Vitali) dominated convergence theorem, dominants allowed to move | `QFS.limsup_lintegral_le_of_dominant` |

Writing `Φ(u,v) = (f(u) − f(v))²|u − v|^{-d-α}·1_{B*×B*}`, Jensen and Lemma 3.4
give `g_h ≤ Λ(2√d)^{d+α}·E_hΦ` (the tiles of the product tiling are the sets
`Ã_h(x) × Ã_h(y)`, and on them `|u − v| ≍ |s − t|` because the sum is restricted
to `|x − y| > √d h`), while `E_hΦ → Φ` almost everywhere is Lemma 7.2. So

> **the paper's dominated-convergence step is valid for every `f ∈ H^{α/2}(B*)`.**

That hypothesis is the theorem's own conclusion, so this is an a priori
estimate. Removing it is what remains open.

### Why the Lipschitz/mollification reduction does not remove it

The natural way to supply the a priori hypothesis is to prove the theorem first
for mollifications `f_ε = f * ρ_ε` and pass to the limit. Its two halves have
opposite fates, and both are recorded in Lean.

**The half that works.** `f_ε` is smooth, hence Lipschitz on a ball, hence in
`H^{α/2}` for every `α < 2`:

| A Lipschitz function has finite `H^{α/2}` seminorm on a ball | `QFS.formHs_lt_top_of_lipschitzOn` | ✅ **proved** |
| --- | --- | --- |

so mollification does put `f_ε` into the class where the step above is valid.
Fatou then handles the left-hand side of the limit `ε → 0`, since
`f_ε → f` almost everywhere.

**The half that does not.** The reduction also needs
`|f_ε|_{H_k(B*)} ≲ |f|_{H_k(B**)}` — mollification must not inflate the
right-hand side. Mollifying is averaging over translates, and

  `f_ε(s) − f_ε(t) = ∫ ρ_ε(z)(f(s−z) − f(t−z)) dz`,

so Jensen turns the requirement into `k(u+z, v+z) ≲ k(u,v)` for `|z| ≤ ε`.
**`k` is not translation-stable in this sense**: it is built from a configuration
of cones that may vary arbitrarily from point to point, and `k(u,v)` is allowed
to vanish — the lower bound in (1.4) carries the indicator `1_E` — while
`k(u+z, v+z)` is comparable to `|u − v|^{-d-α}`. No such constant exists.

This is *not* a refutation. Granted Theorem 1.1, `H_k(B)` and `H^{α/2}(B)`
coincide with comparable seminorms, so mollification *is* bounded on `H_k`; the
deduction simply runs through the theorem. `QFS.form_le_of_theoremOneOneBall`
makes that precise: **assuming Theorem 1.1, any approximation bounded on
`H^{α/2}` is bounded on `H_k`.** So the missing half of the reduction is
equivalent to the statement it would prove, not weaker than it — which is why
the route is circular rather than wrong.

Three further reductions were tried and also fail.

* **Truncation.** It *is* enough to prove the theorem for bounded `f`: the
  truncations `f_N = max(−N, min(N, f))` satisfy `|f_N(x) − f_N(y)| ≤
  |f(x) − f(y)|`, so `|f_N|_{H_k(B*)} ≤ |f|_{H_k(B*)}`, while Fatou gives
  `|f|_{H^{α/2}(B)} ≤ liminf_N |f_N|_{H^{α/2}(B)}`. Truncation is therefore
  `H_k`-nonincreasing — the property mollification lacks — but it gains no
  smoothness, so it does not supply the a priori hypothesis either. Boundedness
  alone yields no dominant, since `∫∫_{B*×B*} k = ∞`.
* **A uniform-in-`h` bound instead of a limit.** Fatou on the left plus
  `∫∫ g_h ≤ C|f|_{H_k(B*)}` uniform in `h` would finish the proof with no
  right-hand limit at all. Jensen reduces this to
  `[⨍⨍_{A×A'}(f(s)−f(t))²]·[∫∫_{A×A'} k] ≤ C h^{2d} ∫∫_{A×A'}(f(s)−f(t))² k(s,t)`
  on each pair of cubes — a correlation inequality that is false in general, and
  false in exactly the relevant configuration: `k` carries the cone structure, so
  it can vanish on precisely the part of `A × A'` where `(f(s) − f(t))²` is
  large.
* **Jensen against the `k`-weighted measure.** Jensen with respect to
  `k(s,t)·d(s,t)/∫∫_{A×A'}k` does give the required per-cube inequality, but for
  the `k`-weighted average of `f(s) − f(t)`, whereas `f_h(x) − f_h(y)` is its
  Lebesgue average; the two are not comparable without further information about
  `k`.

What is missing, then, is a single qualitative statement: that every
`f ∈ H_k(B*)` already lies in `H^{α/2}(B*)`. Given it, the chain
Corollary 3.1 → Corollary 3.6 → `(discret)` → Fatou on the left →
`QFS.limsup_lintegral_le_of_dominant` on the right closes, with all the
constants the paper claims. This is recorded as an obstacle encountered in
formalising the step, not as a claim that the step is wrong.

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

`QFS.PathPropsHolds` records the statement and **`QFS.path_props` proves it**:
for every `d ≥ 1` and every `0 < ϑ ≤ π/2` and every `R₀`, the path family exists
with constants independent of the configuration. Its four
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

   The assignment is where the paper's proof needed repair: a merely balanced
   `φ_z` does not bound the multiplicity of a first-jump edge, and the fix is to
   fix the scheme's parameters by two balanced hashes. See **Deviation 16**;
   `QFS.exists_scheme_assignment` is kept as the paper's own statement.
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
Step 2 is built.

### Steps 3–6 are proved: `pathPropsHolds_of_scaleData`

Steps 1 and 2 are *local*: they fix a logarithmic scale and a centre
`z ∈ Δⁿℤ^d` and produce one walk per admissible pair near `z`. Steps 3–6 are the
global assembly, and they are now formalised, so the whole of Theorem 5.15
follows from that local data.

`QFS.ScaleData Γ Δ R t K m z` is the local package — exactly the output of Steps
1–2 at one scale and one centre:

| Field | The paper |
| --- | --- |
| `path` | a walk in `G` for every pair of `A` (Step 2) |
| `length_le` | at most `t` edges, `t ≍ r^d R^d` (Step 1) |
| `edge_lb` | every edge is at least `Δ^m` long (Step 5's lower bound) |
| `edge_near` | every endpoint lies in `B_{Δ^{m+1}R}(Δ^{m+1}z)` (Steps 1, 6) |
| `fibre_le` | at most `K` pairs share a walk through a given edge (`φ_z`) |

`QFS.Admissible` is the paper's set `A` — lattice pairs in the ball
`B_{2√d Δ^{m+1}}(Δ^{m+1}z)` at distance in `[Δ^{m-1}, Δ^m)`, with `m ≥ 1`. The
paper's window is one scale lower; routing a scale up is what makes every edge
longer than `R₀`, which Section 6 needs (Deviation 17). Then
`QFS.pathPropsLong_of_scaleData` proves

```
PathPropsLong Γ t ((2C+1)(2⌈R⌉+1)^d K) (2Δ²R) R₀
```

whenever `Δ ≥ 2`, `R ≥ 1`, `R₀ < Δ` and `2^C ≥ 2ΔR`, and
`QFS.pathPropsLongHolds_of_scaleData` wraps that into `PathPropsLongHolds`. The
four steps:

* **Step 3** is `QFS.exists_scale_and_centre`. `QFS.exists_scale` puts every
  `L ≥ 1` in exactly one window `[Δ^m, Δ^{m+1})` (`Nat.findGreatest` on
  `Δ^k ≤ L`, which is where Archimedeanity enters), and `QFS.exists_centre`
  puts every point within `(s/2)√d` of `sℤ^d`. Distinct lattice points are at
  distance at least `1 = Δ⁰` (`QFS.one_le_norm_sub_of_lattice`), so the scale
  exists; `y` is then a further `< Δⁿ` from the centre, and `√d/2 + 1 ≤ 2√d`
  for every `d ≥ 1` is what makes the paper's radius `2√d Δⁿ` sufficient.
* **Step 4** is `length_le` verbatim.
* **Step 5** turns the absolute edge bounds into bounds relative to `‖x − y‖`.
  Since `Δ^{m-1} ≤ ‖x − y‖ < Δ^m` and every edge has length in
  `[Δ^m, 2Δ^{m+1}R)`, both comparisons hold with `λ = 2Δ²R` — the paper's
  `2ΔR`, times the scale shift. The upper bound is not an extra hypothesis:
  `QFS.ScaleData.edgeLen_lt` derives `2Δ^{m+1}R` from `edge_near` alone, since
  both endpoints sit in a ball of that diameter, which is how the paper gets it
  too.
* **Step 6** is the multiplicity count, and it is the only step where the paper
  is terser than a proof. For a fixed edge `e`, `QFS.scale_separation` confines
  the scales that can carry `e` to an interval of `2C + 1` values around the
  scale of any one pair using it; `QFS.ncard_lattice_scaled_ball_le` (with the
  new `QFS.lattice_scaled_ball_finite`) bounds the centres at each scale by
  `(2⌈R⌉+1)^d`; and `fibre_le` bounds each `(scale, centre)` cell by `K`. The
  three multiply through `Finset.set_encard_biUnion_le`, giving
  `M = (2C+1)(2⌈R⌉+1)^d K`.

  The paper writes "according to step 5, it is enough to prove the third claim
  for one fixed logarithmic scale", which drops the `2C + 1`; the formalisation
  keeps it, so `M` is explicit.

Claims (1)–(4) are all four discharged, and the reduction is not vacuous:
`QFS.exists_admissible` shows every pair of distinct lattice points really is
admissible at some scale and centre, so `ScaleData` is obliged to supply the
walk that `PathProps` then returns.

### Steps 1 and 2: `exists_blockData`

`QFS.BlockData` is the local package Steps 1–2 produce, and `QFS.exists_blockData`
builds it at every scale and centre. Its fields and their sources:

| Field | Where it comes from |
| --- | --- |
| `W` | `QFS.renormalization_choice` — one favored cone per block |
| `walk` | Proposition 5.14 plus `QFS.exists_choiceWalk_of_choiceConn`, length `≤ (2⌈R⌉+1)^d` |
| `jump` | Lemma 5.16, `QFS.connect_first_jump` |
| `rep`, `idx` | `QFS.exists_indexed_rep` and `QFS.exists_retraction` |
| `sep` | `QFS.block_sep` with `QFS.infNorm_smul_sub_lattice` |
| `near` | the cube radius `(ℓ/2)√d` against the town-ball radius |
| `hf`, `hg` | `QFS.exists_hash` on the admissible points |

The constants are the paper's: `Δ` is the scale step of `QFS.ScaleStep` (even,
divisible by `L`, and larger than both `δ` and `R₀`), `R₁` the first-jump radius,
`r = 2√d + R₁`, and `R` what Proposition 5.14 returns for that `r`. The number of
representatives per block is `QFS.schemeIndex Δ L d m = max 1 (Δ^{md}/L)` — the
paper's `a = Δ^{d(n−1)}/L`, floored at `1` because at the bottom scale a block is
a single lattice point and `Δ^{md}/L` is not a positive integer; there the ball
holds only boundedly many points anyway, so the hashes are trivially balanced.
`QFS.schemeIndex_le_ncard_blockFibre` is the paper's "each block contains at
least `Δ^{d(n−1)}/L` lattice points where the associated cone is favored by
majority", and `QFS.encard_admissiblePt_le` is the matching upper bound on the
ball, giving `K₁ = (2⌈2√dΔ⌉+1)^d L`.

The assumption Step 2 opens with — "assume `#Γ(ℤ^d) ≤ L`" — is discharged rather
than assumed: `QFS.ref_config_uniform` (Corollary 2.4) replaces `Γ` by a
configuration with at most `L` types whose cones sit inside `Γ`'s, and
`QFS.PathProps.mono_config` carries the conclusion back up, since a subgraph's
walks are walks.

The one substantive change is to Step 2's assignment `φ_z`, which as stated does
not bound the multiplicity of a first-jump edge; see **Deviation 16**. A second
change, needed by Section 6, routes every pair one scale up so that every edge is
longer than `R₀`; see **Deviation 17**.

## Section 6: Theorem 1.3

Section 6 is short — the paper calls it "an easy consequence of Theorem 5.15" —
and `QFS.theoremOneThree` is its proof, with no hypothesis on the dimension.
Given a pair `x, y ∈ B_R(x₀) ∩ ℤ^d` at distance more than `R₀`, take the path
`p_xy = (x = z_1, …, z_k = y)` of Theorem 5.15 and:

* **telescope and Cauchy–Schwarz.** `QFS.walk_telescope` sums the increments
  along a walk, `QFS.list_sq_sum_le` is `(∑ aᵢ)² ≤ n ∑ aᵢ²`, and
  `QFS.walk_sq_le` combines them: `(f(x) − f(y))² ≤ k ∑ᵢ (f(z_{i+1}) − f(z_i))²`.
* **rescale the kernel.** Claim (4) gives `|z_{i+1} − z_i| ≤ λ|x − y|`, so
  `|x − y|^{-d-α} ≤ λ^{d+α}|z_{i+1} − z_i|^{-d-α}` — the `rpow` is antitone in
  its base for a nonpositive exponent.
* **apply (1.7).** `QFS.jumpKernel_le_of_dart`: an edge of `G` means one endpoint
  lies in the other's cone, so the indicator in (1.7) is `1`; and the edge is
  longer than `R₀` by `QFS.PathPropsLong`, so the lower bound applies and
  `|z_{i+1} − z_i|^{-d-α} ≤ Λ ω(z_i, z_{i+1})`.

`QFS.chain_estimate` is those three steps for one pair. Summing over pairs is
where claim (3) enters: `QFS.sum_select_le` is the double count — if every pair
selects a set of edges, and no edge is selected by more than `M` pairs, summing
over the selected sets costs a factor `M`. Both balls hold finitely many lattice
points (`QFS.pairSet_finite`), so both sides of Theorem 1.3 are finite sums
(`QFS.discreteForm_eq_sum`) and the exchange is `Finset.sum_comm`.

The constants are `κ = 1 + 2Nλ` — a walk of at most `N` edges each at most
`λ|x − y| < 2λR` long stays within `2NλR` of `x` — and
`c = N λ^{d+α} Λ (N M)`. The paper's `c = (2Λλ^{d+α}(N−1)M)^{-1}` (it states the
reciprocal, comparing in the other direction) carries a factor `2` where this
carries the second `N`: the extra `N` bounds the number of *darts* a single walk
can devote to one edge, which the paper's "for simplicity we assume every path is
of length `N`" elides.

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

## Non-vacuity

A formalisation of this size is worth checking against vacuity: every headline
result quantifies over configurations and kernels constrained by (1.4) or (1.7),
and if those constraints were unsatisfiable the theorems would be empty.
`Nonvacuous.lean` exhibits witnesses. For every `ϑ ∈ (0, π/2]` the constant
configuration is `ϑ`-bounded (`QFS.isBounded_constConfig`) and satisfies the
measurability Proposition 3.5 assumes (`QFS.condMeas_constConfig`), and the plain
jump kernel `|x − y|^{-d-α}` satisfies both (1.4) and (1.7) with `Λ = 2`
(`QFS.kernelBounds_jumpKernel`, `QFS.discreteKernelBounds_jumpKernel`), because
the indicator bracket never exceeds `2` (`QFS.indE_add_indE_le_two`).
`QFS.theoremOneThree_nonvacuous` collects these.

Two earlier non-vacuity checks are recorded with their results:
`QFS.exists_admissible` shows every pair of distinct lattice points really is
admissible at some scale and centre, so `QFS.ScaleData` must supply the walk that
`PathProps` returns; and the reduction `QFS.pathPropsLong_of_scaleData` is therefore
not vacuous either.

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

## The files

| File | Contents |
| --- | --- |
| `Translate` | shifting and shrinking sets; the steps (⋆) and (✝) of Lemma 2.7 |
| `Defs` | Definition 2.1: cones, double cones, configurations, condition (M) |
| `ConeGap`, `ConeGeometry` | the signed distance `coneGap` to a cone's boundary |
| `Cubes` | the maximum norm, cubes, Lemma 2.7 |
| `RefCones` | Lemma 2.2 and Corollary 2.4: finitely many reference cones |
| `Section3` | lattices, Lemmas 3.2 and 3.4, cube volumes, the tiling |
| `Section32` | §3.2: the moving dominant, generalized dominated convergence, Lipschitz functions in `H^{α/2}`, and the circularity of the mollification route |
| `Section7` | Theorem 1.4 on `ℝ^d`, and the finite-overlap chain (6.14) of Lemma 7.1 |
| `BeyondThePaper` | **not the paper** — new, incomplete research on the open statement; see *Beyond the paper* |
| `ThinCones` | Lemma 3.3 for `d ≥ 2` |
| `Section4` | the continuous prelude; Theorem 4.1 |
| `Section5` | Lemmas 5.1–5.7, Corollary 5.8 |
| `Renormalization` | Lemmas 5.9–5.10, Definitions 5.11/5.13, Proposition 5.14 |
| `Counting`, `Paths`, `CyclicScheme`, `Multiplicity`, `Assembly` | the ingredients of Theorem 5.15's Steps 1, 2 and 6 |
| `FirstJump` | the scale step, Lemma 5.16, the statement of Theorem 5.15 |
| `PathAssembly` | Steps 3–6 of Theorem 5.15 |
| `BlockPaths` | Steps 1–2, and Theorem 5.15 |
| `Section1` | the quadratic forms and function spaces; the statements of Theorems 1.1 and 1.3 |
| `Section6` | Theorem 1.3 |
| `Rescaling` | Corollary 3.1 |
| `Section3Kernel` | the discrete kernel, Proposition 3.5, Corollary 3.6 |
| `LebesgueDiff` | Lemma 7.2 |
| `Nonvacuous` | witnesses that the hypotheses are satisfiable |

## Building

```
lake exe cache get   # or reuse an existing Mathlib build
lake build
```
