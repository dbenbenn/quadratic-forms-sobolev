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
(Sections 2, 3 and 4). **This repository formalises that lower layer**: the full
definitional set-up of Section 2, the geometric lemmas of Sections 2 and 3, and
the whole of Section 4 (the paper's "continuous prelude", whose main result is
Theorem 4.1). See *Not attempted* below for what is deliberately left out.

## Status

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

## Not attempted

Recorded here rather than silently omitted. The paper's two main theorems and
the machinery specific to them are out of scope for this formalisation; what is
formalised is the geometric and graph-theoretic layer they are built on.

| Result | Paper | Why not |
| --- | --- | --- |
| Comparability on balls, continuous | Thm. 1.1 | Needs the whole of §§3, 5, 6. |
| Comparability on balls, discrete | Thm. 1.3 | The paper's main theorem; needs §§5–6. |
| `H_k(Ω) = H^{α/2}(Ω)`, density | Thm. 1.4 | Depends on Thm. 1.3 and on Lipschitz-domain extension theory not in scope. |
| Regular Dirichlet form; Markov process | Cor. 1.5 | Depends on Thm. 1.1 and on Dirichlet-form theory (Fukushima–Oshima–Takeda) absent from Mathlib. |
| Weak Harnack, Hölder regularity | Cor. 1.6 | Quoted from Dyda–Kassmann; not proved in the paper. |
| `hℤ^d` rescaling | Cor. 3.1 | Depends on Thm. 1.3. |
| Discrete kernel `ω^k_h`, test-function bound | Prop. 3.5, Cor. 3.6 | Integration against the kernel; depends on Thm. 1.3's setting, and on Lemma 3.3 (see Deviations 7). |
| Lemma 3.3 for `d ≥ 2` | Lem. 3.3 | True but needs an argument the paper does not give; see Deviations 7. |
| `H_k` on balls | Lem. 3.7 | Depends on Cor. 3.6. |
| Chaining and renormalisation | §5 (Lems. 5.1–5.16) | The technical heart of the paper; a formalisation project in its own right. |
| Proof of Theorem 1.3 | §6 | As above. |
| Auxiliary integral estimates | Lems. 7.1, 7.2 | Measure-theoretic, attached to §§3 and 6. |

## Building

```
lake exe cache get   # or reuse an existing Mathlib build
lake build
```
