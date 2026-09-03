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

## Not attempted

Recorded here rather than silently omitted.

*(to be filled in as the scope is fixed)*

## Building

```
lake exe cache get   # or reuse an existing Mathlib build
lake build
```
