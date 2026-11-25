# Allard 2: Preliminaries, items 2.1–2.4 (printed pp. 420–422)

[README](../README.md) · [Divergences](divergences.md) · [Axiom audit](assumptions.log)

Source numbering and printed pages refer to W. K. Allard, “On the first
variation of a varifold”, *Ann. of Math. (2)* 95 (1972), 417–491
(bibliography key `Allard1972`); blueprint labels refer to
[blueprint/sections2to5.tex](../blueprint/sections2to5.tex). The notation is
Federer's: Hom(V, W) is the space of linear maps, f^* the adjoint, f ∘ g the
composition, f • g the inner product of Hom(V, W) and ∧_k f the induced map
of exterior algebras. A covector ω ∈ Hom(V, R) and a vector b ∈ W give the
map ω · b = [v ↦ ω(v) b] of Hom(V, W).

The formal objects live in eight files.

| File | Contents |
| --- | --- |
| [AllardHomInnerProduct.v](../theories/AllardHomInnerProduct.v) | 2.2: the inner product and the two norms of Hom(V, W); the map ω · b. |
| [AllardExteriorPowers.v](../theories/AllardExteriorPowers.v) | 2.2(1) and 2.2(2). |
| [AllardOrthogonalProjectors.v](../theories/AllardOrthogonalProjectors.v) | Orthogonal projectors of rank k on a finite dimensional inner product space V; 2.3(1)–(5). |
| [AllardGrassmann.v](../theories/AllardGrassmann.v) | G(n, k) as a compact metric space and G_k(R^n) = R^n × G(n, k). |
| [AllardGrassmannSubspaces.v](../theories/AllardGrassmannSubspaces.v) | The homeomorphism between G(n, k) and Federer's G(n, k) of subspaces. |
| [AllardJacobians.v](../theories/AllardJacobians.v) | 2.4 and 2.4(1). |
| [AllardProjectionFormula.v](../theories/AllardProjectionFormula.v) | Blueprint new:projection_formula: the operators A and P and their algebraic properties. |
| [AllardProjectionContinuity.v](../theories/AllardProjectionContinuity.v) | Blueprint new:projection_formula: openness of the domain and continuity of [(L, S) ↦ P]. |

[tests/Assumptions.v](../tests/Assumptions.v) prints the assumptions of the
principal results; `make audit` writes them to
[assumptions.log](assumptions.log). Every listed result depends only on
`boolp.propositional_extensionality`, `boolp.functional_extensionality_dep`
and `boolp.constructive_indefinite_description`.

## Item map

| Allard | Assertion | Rocq | Status |
| --- | --- | --- | --- |
| 2.1 | Notation of Federer's book. | Federer library | Used as is. |
| 2.2 | f • g = trace(f^* ∘ g) for f, g ∈ Hom(V, W). | [`allard_2_2_hom_inner`](../theories/AllardHomInnerProduct.v#L118) | Formalised. |
| 2.2 | \|f\| = (f • f)^{1/2}. | [`allard_2_2_hom_norm`](../theories/AllardHomInnerProduct.v#L124) | Formalised. |
| 2.2 | ‖f‖ ≤ \|f\| ≤ (dim V)^{1/2} ‖f‖. | [`allard_2_2_norm_comparison`](../theories/AllardHomInnerProduct.v#L135) | Formalised. |
| 2.2 | (ω · b) • A = ω(A^*(b)). | [`rank_one_map`](../theories/AllardHomInnerProduct.v#L156), [`rank_one_map_hom_inner`](../theories/AllardHomInnerProduct.v#L169) | Formalised. |
| 2.2(1) | det(1 + t f) = Σ_{i=0}^{m} t^i trace(∧_i f). | [`allard_2_2_1`](../theories/AllardExteriorPowers.v#L32) | Formalised. |
| 2.2(2) | (∧_k f)^* = ∧_k(f^*). | [`allard_2_2_2`](../theories/AllardExteriorPowers.v#L56) | Formalised. |
| 2.3 | Orthogonal projectors of rank k: S ∘ S = S, S^* = S, trace S = k. | [`is_orthogonal_projector`](../theories/AllardOrthogonalProjectors.v#L61), [`orthogonal_projector_frame`](../theories/AllardOrthogonalProjectors.v#L192) | Formalised; see the divergences. |
| 2.3 | S^⊥ = 1 − S ∈ G(n, n − k) and im S^⊥ = (im S)^⊥. | — | Not formalised. |
| 2.3 | G(n, k) with the metric \|S − T\|, compact. | [`orthogonal_projectors`](../theories/AllardGrassmann.v#L66), [`projection_grassmann`](../theories/AllardGrassmann.v#L71), [`projection_grassmann_distanceE`](../theories/AllardGrassmann.v#L107), [`projection_grassmann_compact`](../theories/AllardGrassmann.v#L220) | Formalised. |
| 2.3 | Correspondence with Federer's G(n, k). | [`subspace_projector`](../theories/AllardGrassmannSubspaces.v#L172), [`projector_subspace`](../theories/AllardGrassmannSubspaces.v#L185), [`allard_2_3_identification`](../theories/AllardGrassmannSubspaces.v#L241) | Formalised. |
| 2.3 | G_k(R^n) = R^n × G(n, k). | [`grassmann_bundle`](../theories/AllardGrassmann.v#L254), [`grassmann_bundle_distanceE`](../theories/AllardGrassmann.v#L260), [`grassmann_bundle_locally_compact`](../theories/AllardGrassmann.v#L267), [`grassmann_bundle_separable`](../theories/AllardGrassmann.v#L276) | Formalised. |
| 2.3(1) | S(x) • S(y) = S(x) • y. | [`allard_2_3_1`](../theories/AllardOrthogonalProjectors.v#L254) | Formalised for every V. |
| 2.3(2) | \|S(x)\|^2 = S(x) • x. | [`allard_2_3_2`](../theories/AllardOrthogonalProjectors.v#L261) | Formalised for every V. |
| 2.3(3) | 1 • S = trace S = k = \|S\|^2. | [`allard_2_3_3`](../theories/AllardOrthogonalProjectors.v#L268) | Formalised for every V. |
| 2.3(4) | (ω · v) • S = ω(S(v)). | [`allard_2_3_4`](../theories/AllardOrthogonalProjectors.v#L285) | Formalised for every V. |
| 2.3(5) | f • S = f^* • S = trace(f ∘ S). | [`allard_2_3_5`](../theories/AllardOrthogonalProjectors.v#L296) | Formalised for every V. |
| 2.4 | ‖∧_k(f ∘ S)‖ = \|f(u_1) ∧ ⋯ ∧ f(u_k)\| and its Gram form. | [`allard_2_4`](../theories/AllardJacobians.v#L227), [`allard_2_4_gram`](../theories/AllardJacobians.v#L243) | Partly formalised; see the divergences. |
| 2.4(1) | (d/dt) ‖∧_k((1 + t f) ∘ S)‖ at t = 0 equals f • S. | [`allard_2_4_1`](../theories/AllardJacobians.v#L280) | Formalised. |
| new:projection_formula | A = S ∘ L^* ∘ L ∘ S + 1 − S is invertible if and only if L \| im S is injective. | [`projection_formula_operator`](../theories/AllardProjectionFormula.v#L52), [`projection_formula_operator_injective`](../theories/AllardProjectionFormula.v#L119) | Formalised. |
| new:projection_formula | P = L ∘ S ∘ A^{-1} ∘ L^* is the orthogonal projection onto L[im S]. | [`projection_formula_map`](../theories/AllardProjectionFormula.v#L155), [`projection_formula_map_symmetric`](../theories/AllardProjectionFormula.v#L208), [`projection_formula_map_idempotent`](../theories/AllardProjectionFormula.v#L227), [`projection_formula_map_image`](../theories/AllardProjectionFormula.v#L232), [`projection_formula_orthogonal_projector`](../theories/AllardProjectionFormula.v#L320) | Formalised. |
| new:projection_formula | L \| im S is injective if and only if ‖∧_k(L ∘ S)‖ > 0. | [`projection_formula_jacobian`](../theories/AllardProjectionFormula.v#L281), [`projection_formula_domainE`](../theories/AllardProjectionContinuity.v#L156) | Formalised. |
| new:projection_formula | The set {(L, S) ∈ Hom(R^n, R^p) × G(n, k) : ‖∧_k(L ∘ S)‖ > 0} is open. | [`projection_formula_grassmann_open`](../theories/AllardProjectionContinuity.v#L259) | Formalised. |
| new:projection_formula | [(L, S) ↦ P] is continuous on {(L, S) : A is invertible}, an open subset of Hom(R^n, R^p) × Hom(R^n, R^n) whose intersection with Hom(R^n, R^p) × G(n, k) is {‖∧_k(L ∘ S)‖ > 0}. | [`projection_formula_domain`](../theories/AllardProjectionContinuity.v#L150), [`projection_formula_domain_open`](../theories/AllardProjectionContinuity.v#L182), [`projection_formula_on`](../theories/AllardProjectionContinuity.v#L196), [`projection_formula_onP`](../theories/AllardProjectionContinuity.v#L201), [`projection_formula_continuous`](../theories/AllardProjectionContinuity.v#L209) | Formalised; see the divergences. |

## 2.2: Hom(V, W) as an inner product space

Let V and W be finite dimensional inner product spaces; in the formal
statements V carries a basis `b` with `is_basis b`, and the inner products
are `B` and `C` with `is_inner_product B` and `is_inner_product C`. Federer's
inner product of Hom(V, W) (1.7.9) is `hom_inner hB hC hb`, its norm is
`hom_norm hB hC hb` and the operator norm is `hom_operator_norm hB hC hb`.
The theorem [`allard_2_2_hom_inner`](../theories/AllardHomInnerProduct.v#L118) identifies `hom_inner` with
f • g = trace(f^* ∘ g), and [`allard_2_2_norm_comparison`](../theories/AllardHomInnerProduct.v#L135) gives
‖f‖ ≤ \|f\| ≤ (dim V)^{1/2} ‖f‖, where dim V is the length of `b`.

The map ω · b of Allard 2.3(4) is [`rank_one_map`](../theories/AllardHomInnerProduct.v#L156): for `omega : Hom V R^o`
and `y : W`, `rank_one_map omega y` is [v ↦ ω(v) y]
([`rank_one_mapE`](../theories/AllardHomInnerProduct.v#L161)). The identity (ω · y) • A = ω(A^*(y)) is
[`rank_one_map_hom_inner`](../theories/AllardHomInnerProduct.v#L169).

The same file contains the auxiliary results
[`orthonormal_basis_exists_finite`](../theories/AllardHomInnerProduct.v#L70), [`orthonormal_expansion`](../theories/AllardHomInnerProduct.v#L84) and
[`trace_orthonormal`](../theories/AllardHomInnerProduct.v#L94); the last computes the trace in an orthonormal basis.

## 2.2(1) and 2.2(2)

The theorem [`allard_2_2_1`](../theories/AllardExteriorPowers.v#L32) states, for f ∈ Hom(V, V) and t ∈ R,

    det(1_V + t f) = Σ_{i=0}^{m} t^i trace(∧_i f),

where `m` is the length of the basis `e` of V, `det h2 he` is Federer's
determinant (1.3.4) and `exterior_trace h2 he f i` is trace(∧_i f) (1.4.5).

The theorem [`allard_2_2_2`](../theories/AllardExteriorPowers.v#L56) states that the adjoint of ∧_k f, for the
inner products of ∧_k V and ∧_k W of Federer 1.7.5, agrees at every point
with ∧_k(f^*).

## 2.3: orthogonal projectors and G(n, k)

For a finite dimensional inner product space V, the predicate
`is_orthogonal_projector hB hb k S` ([`is_orthogonal_projector`](../theories/AllardOrthogonalProjectors.v#L61)) states
S ∘ S = S, S^* = S and trace S = k. For an orthonormal family
u : {1, …, k} → V, the map [`frame_projector`](../theories/AllardOrthogonalProjectors.v#L68) is
[x ↦ Σ_i (x • u_i) u_i]. The theorem [`orthogonal_projector_frame`](../theories/AllardOrthogonalProjectors.v#L192) states
that S is an orthogonal projector of rank k if and only if S is the frame
projector of an orthonormal family of k vectors. The results
[`orthogonal_projector_symmetric`](../theories/AllardOrthogonalProjectors.v#L175) and [`orthogonal_projector_idempotent`](../theories/AllardOrthogonalProjectors.v#L181)
extract the pointwise identities, and [`frame_projector_image`](../theories/AllardOrthogonalProjectors.v#L237) identifies
the image.

### 2.3(1)–(5)

The section `Projector` of
[AllardOrthogonalProjectors.v](../theories/AllardOrthogonalProjectors.v)
fixes V, its inner product `B`, its basis `b` and an orthogonal projector
`S` of rank `k` (hypothesis `hS : is_orthogonal_projector hB hb k S`). The
five identities are

- [`allard_2_3_1`](../theories/AllardOrthogonalProjectors.v#L254): `B (S x) (S y) = B (S x) y`;
- [`allard_2_3_2`](../theories/AllardOrthogonalProjectors.v#L261): `inner_norm hB (S x) ^+ 2 = B (S x) x`;
- [`allard_2_3_3`](../theories/AllardOrthogonalProjectors.v#L268): `hom_inner hB hB hb ident S = k%:R /\ hom_norm hB hB hb S ^+ 2 = k%:R`;
- [`allard_2_3_4`](../theories/AllardOrthogonalProjectors.v#L285): `hom_inner hB hB hb (rank_one_map omega v) S = omega (S v)`;
- [`allard_2_3_5`](../theories/AllardOrthogonalProjectors.v#L296): `hom_inner hB hB hb f S = hom_inner hB hB hb (adj f) S /\ hom_inner hB hB hb f S = tr (hom_comp f S)`.

Outside the section each takes the arguments `hB hb hS` followed by the
points; for S ∈ G(n, k) use `hS = projection_grassmannP S`.

### G(n, k)

Write `HE` for Hom(R^n, R^n) with the metric of its inner product,
`inner_metric_space (hom_inner_productP hBn hBn hbn)`, where `hBn` is
`euclidean_inner_productP R n` and `hbn` is `coordinate_basisP R n`. Then

    orthogonal_projectors R n k : set HE
    projection_grassmann R n k : metricType R

where [`orthogonal_projectors`](../theories/AllardGrassmann.v#L66) is the set of orthogonal projectors of rank
k and [`projection_grassmann`](../theories/AllardGrassmann.v#L71) is this set as a metric subspace of `HE`.
A member `S : projection_grassmann R n k` has the underlying map
`set_val S : Hom (R_n R n) (R_n R n)`, and `projection_grassmannP S` proves
`is_orthogonal_projector hBn hbn k (set_val S)`. Conversely
[`projection_grassmann_of`](../theories/AllardGrassmann.v#L82) packs a proof of that predicate into a member;
[`projection_grassmann_ofE`](../theories/AllardGrassmann.v#L87) computes its value and
[`projection_grassmann_ext`](../theories/AllardGrassmann.v#L93) is extensionality. The distance is
\|S − T\| ([`projection_grassmann_distanceE`](../theories/AllardGrassmann.v#L107)).

The set is closed ([`orthogonal_projectors_closed`](../theories/AllardGrassmann.v#L159)), bounded
([`orthogonal_projectors_bounded`](../theories/AllardGrassmann.v#L199)) and compact
([`orthogonal_projectors_compact`](../theories/AllardGrassmann.v#L212)); hence G(n, k) is compact
([`projection_grassmann_compact`](../theories/AllardGrassmann.v#L220)), Hausdorff
([`projection_grassmann_hausdorff`](../theories/AllardGrassmann.v#L226)), locally compact
([`projection_grassmann_locally_compact`](../theories/AllardGrassmann.v#L232)), complete
([`projection_grassmann_complete`](../theories/AllardGrassmann.v#L237)) and separable
([`projection_grassmann_separable`](../theories/AllardGrassmann.v#L243)). The continuity of
[S ↦ S • T] is [`hom_inner_continuous`](../theories/AllardGrassmann.v#L125).

### Correspondence with Federer's G(n, k)

Federer's G(n, k) of 1.6.2, with the topology of 2.7.16, is
`euclidean_grassmann_space R n k`. The map [`subspace_projector`](../theories/AllardGrassmannSubspaces.v#L172) sends a
subspace W to its orthogonal projection `grassmann_projection W`
([`grassmann_projection_orthogonal_projector`](../theories/AllardGrassmannSubspaces.v#L79)), and
[`projector_subspace`](../theories/AllardGrassmannSubspaces.v#L185) sends S to its image
([`orthogonal_projector_image`](../theories/AllardGrassmannSubspaces.v#L118)). The theorem
[`allard_2_3_identification`](../theories/AllardGrassmannSubspaces.v#L241) states that the two maps are mutually inverse
and continuous.

### G_k(R^n)

The space [`grassmann_bundle`](../theories/AllardGrassmann.v#L254) is `grassmann_bundle R n k : metricType R`,
the product R^n × G(n, k) with the distance
max{\|x − y\|, \|S − T\|} ([`grassmann_bundle_distanceE`](../theories/AllardGrassmann.v#L260)). It is locally
compact ([`grassmann_bundle_locally_compact`](../theories/AllardGrassmann.v#L267)) and separable
([`grassmann_bundle_separable`](../theories/AllardGrassmann.v#L276)). Its members are pairs `(x, S)` with
`x : R_n R n` and `S : projection_grassmann R n k`.

## 2.4 and 2.4(1)

Let L ∈ Hom(R^n, R^p) and let u : {1, …, k} → R^n be orthonormal. The
theorem [`allard_2_4`](../theories/AllardJacobians.v#L227) states

    J_k(L ∘ S) = |L(u_1) ∧ ⋯ ∧ L(u_k)|,

where S is the frame projector of u, J_k is Federer's
`euclidean_linear_jacobian k` (the norm ‖∧_k(L ∘ S)‖ of 3.2.1) and the right
side is the norm of `e_lambda (fun i => L (u i)) (ord_tuple k)` in ∧_k R^p.
The theorem [`allard_2_4_gram`](../theories/AllardJacobians.v#L243) expands the square as
Σ_σ sign(σ) Π_i L(u_{σ(i)}) • L(u_i).

The theorem [`allard_2_4_1`](../theories/AllardJacobians.v#L280) reads

```coq
Theorem allard_2_4_1 (f : Hom Rn Rn) (S : projection_grassmann R n k) :
  has_real_curve_derivative
    (fun t => euclidean_linear_jacobian k
      (hom_comp (hom_of_linear (linear_id Rn) + t *: f) (set_val S : Hom Rn Rn))) 0
    (hom_inner hBn hBn hbn f (set_val S)).
```

that is, the derivative of [t ↦ ‖∧_k((1 + t f) ∘ S)‖] at 0 is f • S.
The curve lemmas [`real_curve_derivative_sum`](../theories/AllardJacobians.v#L59),
[`real_curve_derivative_prod_two_zero`](../theories/AllardJacobians.v#L114) and
[`real_curve_derivative_quadratic`](../theories/AllardJacobians.v#L136) support the proof.

## new:projection_formula

Let L ∈ Hom(R^n, R^p) and S ∈ Hom(R^n, R^n) with S ∘ S = S and S^* = S.
The operator [`projection_formula_operator`](../theories/AllardProjectionFormula.v#L52) is

    A = S ∘ L^* ∘ L ∘ S + 1_{R^n} − S,

with L^* = `euclidean_rectangular_adjoint L`. The theorem
[`projection_formula_operator_injective`](../theories/AllardProjectionFormula.v#L119) states that A is injective if and
only if L(x) = 0 and S(x) = x imply x = 0. Given `hA : injective A`,
[`projection_formula_inverse`](../theories/AllardProjectionFormula.v#L150) is A^{-1}, the inverse in Federer's linear
group of R^n, and [`projection_formula_map`](../theories/AllardProjectionFormula.v#L155) is

    P = L ∘ S ∘ A^{-1} ∘ L^* ∈ Hom(R^p, R^p).

The map P is symmetric ([`projection_formula_map_symmetric`](../theories/AllardProjectionFormula.v#L208)), idempotent
([`projection_formula_map_idempotent`](../theories/AllardProjectionFormula.v#L227)) and has image L[im S]
([`projection_formula_map_image`](../theories/AllardProjectionFormula.v#L232)). If S is an orthogonal projector of rank
k, then [`projection_formula_jacobian`](../theories/AllardProjectionFormula.v#L281) states that L | im S is injective if
and only if J_k(L ∘ S) > 0, and [`projection_formula_orthogonal_projector`](../theories/AllardProjectionFormula.v#L320)
states that P is an orthogonal projector of rank k on R^p.

The continuity part is in
[AllardProjectionContinuity.v](../theories/AllardProjectionContinuity.v).
The set [`projection_formula_domain`](../theories/AllardProjectionContinuity.v#L150), written
`projection_formula_domain R n p`, is the set of (L, S) ∈ Hom(R^n, R^p) ×
Hom(R^n, R^n) for which A is injective. It is open
([`projection_formula_domain_open`](../theories/AllardProjectionContinuity.v#L182)), and for S ∈ G(n, k) the theorem
[`projection_formula_domainE`](../theories/AllardProjectionContinuity.v#L156) states that (L, S) belongs to it if and only
if J_k(L ∘ S) > 0. The map [`projection_formula_on`](../theories/AllardProjectionContinuity.v#L196) sends a point of the
domain, with the relative topology, to P; it is continuous
([`projection_formula_continuous`](../theories/AllardProjectionContinuity.v#L209)), and its value lies in G(p, k) whenever
S ∈ G(n, k) ([`projection_formula_onP`](../theories/AllardProjectionContinuity.v#L201)). The set
{(L, S) ∈ Hom(R^n, R^p) × G(n, k) : J_k(L ∘ S) > 0} is open
([`projection_formula_grassmann_open`](../theories/AllardProjectionContinuity.v#L259)). The continuity of [(L, S) ↦ P] on
this open subset of Hom(R^n, R^p) × G(n, k) is not stated as a separate
theorem. Since G(n, k) carries the relative topology of Hom(R^n, R^n), it
follows by composing the continuous inclusion of that subset into the domain
with [`projection_formula_on`](../theories/AllardProjectionContinuity.v#L196).

## Interface for Allard section 3

Import

```coq
From Allard Require Import AllardHomInnerProduct AllardExteriorPowers
  AllardOrthogonalProjectors AllardGrassmann AllardGrassmannSubspaces
  AllardJacobians AllardProjectionFormula AllardProjectionContinuity.
```

and use these objects.

- G(n, k): `projection_grassmann R n k : metricType R`, compact by
  [`projection_grassmann_compact`](../theories/AllardGrassmann.v#L220); underlying map `set_val S`; defining
  properties `projection_grassmannP S`; construction
  `projection_grassmann_of hS`.
- G_k(R^n): `grassmann_bundle R n k : metricType R`, locally compact
  ([`grassmann_bundle_locally_compact`](../theories/AllardGrassmann.v#L267)) and separable
  ([`grassmann_bundle_separable`](../theories/AllardGrassmann.v#L276)).
- The inner product S • T and the norm \|S\| of Hom(R^n, R^n):
  `hom_inner hBn hBn hbn` and `hom_norm hBn hBn hbn`.
- The identities 2.3(1)–(5): `allard_2_3_1 hBn hbn (projection_grassmannP S)` and so on.
- The first variation of area, 2.4(1): `allard_2_4_1 f S`.
- The Jacobian ‖∧_k(L ∘ S)‖: `euclidean_linear_jacobian k (hom_comp L (set_val S))`.
- Subspaces: `projector_subspace S : euclidean_grassmann_space R n k`, with
  `allard_2_3_identification` to move between the two models.
- The projection formula: `projection_formula_map hA` for
  `hA : injective (projection_formula_operator L S)`, with
  `projection_formula_orthogonal_projector`, `projection_formula_jacobian`,
  `projection_formula_continuous` and `projection_formula_grassmann_open`.

## Divergences

The [divergence register](divergences.md) lists every divergence from
Allard's text and from the blueprint. In brief:

- G(n, k) is defined by S ∘ S = S, S^* = S and trace S = k, following the
  blueprint; the equivalence with Allard's description is
  [`orthogonal_projector_frame`](../theories/AllardOrthogonalProjectors.v#L192), and [`allard_2_3_identification`](../theories/AllardGrassmannSubspaces.v#L241) relates
  it to Federer's G(n, k).
- The metric of G(n, k) is \|S − T\|, and G_k(R^n) carries the maximum of the
  distances of its factors.
- The identities 2.3(1)–(5) are proved for an arbitrary finite dimensional
  inner product space.
- Of 2.4, the rank-one assertion, the equality with the Hilbert–Schmidt norm
  \|∧_k(f ∘ S)\| and the determinant form det((f ∘ j)^* ∘ f ∘ j)^{1/2} are not
  formalised; the formal theorems use the operator norm ‖∧_k(f ∘ S)‖.
- The proof of 2.4(1) differentiates the Leibniz expansion of the Gram
  determinant.
- The projection formula is stated for X = R^n and Y = R^p; P depends on a
  proof that A is injective, and continuity is stated on the open set of
  (L, S) ∈ Hom(R^n, R^p) × Hom(R^n, R^n) for which A is invertible.
- The assertions on S^⊥ in 2.3 are not formalised.
