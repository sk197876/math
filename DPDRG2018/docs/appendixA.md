# Appendix A of De Philippis, De Rosa and Ghiraldin (2018)

[README](../README.md) · [Divergences](divergences.md)

Source numbering and pages refer to G. De Philippis, A. De Rosa and
F. Ghiraldin, “Rectifiability of varifolds with locally bounded first
variation with respect to anisotropic surface energies”, *Comm. Pure
Appl. Math.* 71 (2018), 1123–1148, Appendix A, pp. 1143–1144 (bibliography
key `DePhilippis2018`, cited as DDG). Item labels A.1–A.9 and the labels in
the second column refer to [blueprint/dpdrg_blueprint.tex](../blueprint/dpdrg_blueprint.tex);
def:BF and mr:integrands are the blueprint entries shared with DPGPR2026.

Throughout, R^n = `R_n R n`, End(R^n) = `Hom Rn Rn` with the inner product
A • B = trace(A^* ∘ B) of Allard 2.2 (`hom_inner`, Federer 1.7.9) and the
norm |A| = (A • A)^{1/2} (`hom_norm`), A^* is
`euclidean_rectangular_adjoint A`, and G(n, d) is Allard's
`orthogonal_projectors R n d`. Derivatives of curves are the two-sided
derivatives of Federer 2.9.19 and 2.9.22 (`has_real_curve_derivative`,
`has_normed_curve_derivative`), tangent cones those of Federer 3.1.21
(`norm_tangent_cone`), and relative differentials those of Federer 3.1.22
(`has_relative_norm_differential`).

## Files

| File | Contents |
| --- | --- |
| [DdgLinearAlgebra.v](../theories/DdgLinearAlgebra.v) | Pointwise arithmetic of Hom, adjoints, the norm estimates \|A ∘ B\| ≤ n^{1/2} \|A\| \|B\| and \|A\| ≤ n^{1/2} sup_{\|v\| ≤ 1} \|A v\|. |
| [DdgGrassmann.v](../theories/DdgGrassmann.v) | A.1: (A.1) and the elementary properties of T ∈ G(n, d) and T^⊥ = 1 − T. |
| [DdgMovingPlane.v](../theories/DdgMovingPlane.v) | A.3 (new:projformula): the orthogonal projection T(t) onto (1 + t L)[im T] and the estimate \|T(t) − T\| ≤ 3 n^{1/2} \|t\| \|L\|. |
| [DdgLemmaA1.v](../theories/DdgLemmaA1.v) | A.5: Lemma A.1. |
| [DdgGrassmannTangent.v](../theories/DdgGrassmannTangent.v) | A.4 (tangent part) and the membership assertion of Lemma A.1. |
| [DdgHomInner.v](../theories/DdgHomInner.v) | Identities for A • B used for B_F. |
| [DdgAnisotropicIntegrandUP.v](../theories/DdgAnisotropicIntegrandUP.v) | def:BF: the characterising predicate of B_F(T), uniqueness, differentiability of integrands of class 1. |
| [DdgAnisotropicIntegrandConstruction.v](../theories/DdgAnisotropicIntegrandConstruction.v) | Existence of B_F(T) (private; imported only by the sealed file). |
| [DdgAnisotropicIntegrandSealed.v](../theories/DdgAnisotropicIntegrandSealed.v) | Opaque choice of B_F(T). |
| [DdgAnisotropicIntegrand.v](../theories/DdgAnisotropicIntegrand.v) | Public interface of B_F(T) and C_F(T). |
| [DdgWeightedJacobian.v](../theories/DdgWeightedJacobian.v) | A.6 (new:BFderiv). |
| [DdgFlow.v](../theories/DdgFlow.v) | A.7 (new:flow) for Ω = R^n. |
| [DdgWeightedJacobianEstimate.v](../theories/DdgWeightedJacobianEstimate.v) | Bounds (1 − c)^d ≤ ‖∧_d((1 + t L) ∘ T)‖ ≤ (1 + c)^d with c = \|t\| \|L\|, and the uniform estimate of F(T(t)) ‖∧_d((1 + t L) ∘ T)‖ − F(T) used for A.9. |
| [DdgFirstVariation.v](../theories/DdgFirstVariation.v) | A.9 (ddg:A.2const): differentiation of t ↦ ∫ F d(φ_t)_# V at t = 0, with a sequential dominated convergence lemma. |
| [DdgFirstVariationPoint.v](../theories/DdgFirstVariationPoint.v) | A.8 (ddg:A.2): Lemma A.2 for integrands depending on the point, on R^n × End(R^n) with the product inner product; differentiation under the integral sign. |
| [tests/Assumptions.v](../tests/Assumptions.v) | Axiom audit of the principal theorems. |

## Item map

| Item | Assertion | Rocq | Status |
| --- | --- | --- | --- |
| A.1, ddg:A.1 | G(n, d) = {T : T ∘ T = T, T^* = T, trace T = d}. | [`ddg_A_1`](../theories/DdgGrassmann.v#L159) | Formalised (G(n, d) is defined by (A.1), Allard 2.3). |
| A.1 | \|T\| = d^{1/2}, d ≤ n, T^⊥ ∈ G(n, n − d), T ∘ T^⊥ = 0 = T^⊥ ∘ T, im T^⊥ = ker T. | [`ddg_A_1_norm`](../theories/DdgGrassmann.v#L169), [`ddg_A_1_dimension`](../theories/DdgGrassmann.v#L178), [`ddg_A_1_perp`](../theories/DdgGrassmann.v#L198), [`ddg_A_1_composition`](../theories/DdgGrassmann.v#L209), [`ddg_A_1_image`](../theories/DdgGrassmann.v#L218) | Formalised. |
| A.3, new:projformula | For \|t\| \|L\| < 1, T(t) is the orthogonal projection onto (1 + t L)[im T], given by Allard's projection formula. | [`ddg_moving_plane`](../theories/DdgMovingPlane.v#L57), [`ddg_moving_planeP`](../theories/DdgMovingPlane.v#L93), [`is_ddg_plane_projection`](../theories/DdgMovingPlane.v#L49) | Formalised. |
| A.3 | \|(T(t) − T)(v)\| ≤ 3 \|t\| \|L\| \|v\| and \|T(t) − T\| ≤ 3 n^{1/2} \|t\| \|L\| for \|t\| \|L\| ≤ 1/2. | [`ddg_plane_estimate`](../theories/DdgMovingPlane.v#L212), [`ddg_plane_hom_estimate`](../theories/DdgMovingPlane.v#L225) | Formalised (new). |
| A.4, ddg:A.tan | Tan(G(n, d), T) = SymEnd ∩ {T ∘ A ∘ T = 0 = T^⊥ ∘ A ∘ T^⊥} = SymEnd ∩ {A = A ∘ T + T ∘ A} = {X + X^* : X ∈ H_T}. | [`ddg_grassmann_tangent`](../theories/DdgGrassmannTangent.v#L334), [`ddg_tangent_S1`](../theories/DdgGrassmannTangent.v#L111) – [`ddg_tangent_S3`](../theories/DdgGrassmannTangent.v#L128) | Formalised. |
| A.4 | Tan(G(n, d), T) is a vector subspace. | [`ddg_tangent_cone_linear`](../theories/DdgGrassmannTangent.v#L352) | Formalised. |
| A.4 | G(n, d) is a submanifold of class ∞ and dimension d(n − d). | — | Not formalised. |
| A.5, ddg:A.lemma1 | Lemma A.1: T'(0) = T^⊥ ∘ L ∘ T + (T^⊥ ∘ L ∘ T)^*. | [`ddg_lemma_A_1`](../theories/DdgLemmaA1.v#L231), [`ddg_lemma_A_1_moving_plane`](../theories/DdgLemmaA1.v#L276) | Formalised. |
| A.5 | T'(0) ∈ Tan(G(n, d), T). | [`ddg_tangent_direction_tangent`](../theories/DdgGrassmannTangent.v#L143) | Formalised. |
| def:BF | B_F(T) • L = F(T) (T • L) + D F(T)(T^⊥ ∘ L ∘ T + (T^⊥ ∘ L ∘ T)^*), C_F(T) = B_F(T) − F(T) T, for F not depending on the point. | [`is_ddg_B`](../theories/DdgAnisotropicIntegrandUP.v#L59), [`ddg_B_unique`](../theories/DdgAnisotropicIntegrandUP.v#L69), [`ddg_B`](../theories/DdgAnisotropicIntegrand.v#L45), [`ddg_C`](../theories/DdgAnisotropicIntegrand.v#L49), [`ddg_B_spec`](../theories/DdgAnisotropicIntegrand.v#L54), [`ddg_B_characterisation`](../theories/DdgAnisotropicIntegrand.v#L62), [`ddg_B_formula`](../theories/DdgAnisotropicIntegrand.v#L76), [`ddg_B_class_one`](../theories/DdgAnisotropicIntegrand.v#L90) | Formalised. |
| mr:integrands | An integrand of class 1 relative to G(n, d) is differentiable relative to G(n, d). | [`ddg_relative_differentiable`](../theories/DdgAnisotropicIntegrandUP.v#L85) | Formalised. |
| A.6, new:BFderiv | ‖∧_d T‖ = 1. | [`ddg_jacobian_projection`](../theories/DdgWeightedJacobian.v#L100) | Formalised. |
| A.6 | d/dt ‖∧_d((1 + t L) ∘ T)‖ at 0 is L • T. | [`ddg_jacobian_derivative`](../theories/DdgWeightedJacobian.v#L116) | Formalised (Allard 2.4(1)). |
| A.6 | B_F(T) • L = d/dt (F(T(t)) ‖∧_d((1 + t L) ∘ T)‖) at 0. | [`ddg_weighted_jacobian_derivative`](../theories/DdgWeightedJacobian.v#L128), [`ddg_B_derivative`](../theories/DdgWeightedJacobian.v#L188) | Formalised for F not depending on the point. |
| A.7, new:flow | φ_t = 1 + t g: φ_t(x) = x where g(x) = 0, \|φ_t(x) − x\| ≤ \|t\| sup \|g\|, φ_t of class 1 with Dφ_t(x) = 1 + t Dg(x), φ_t and Dφ_t(x) univalent and φ_t proper for \|t\| Lip g < 1. | [`ddg_flow`](../theories/DdgFlow.v#L52), [`ddg_flow_differential`](../theories/DdgFlow.v#L56), [`ddg_flow_fixed`](../theories/DdgFlow.v#L60), [`ddg_flow_displacement`](../theories/DdgFlow.v#L65), [`ddg_flow_class_one`](../theories/DdgFlow.v#L77), [`ddg_flow_injective`](../theories/DdgFlow.v#L165), [`ddg_flow_differential_injective`](../theories/DdgFlow.v#L184), [`ddg_flow_proper`](../theories/DdgFlow.v#L249), [`ddg_flow_immersion`](../theories/DdgFlow.v#L270) | Formalised for Ω = R^n; class ∞ not formalised. |
| A.8 | Differentiation under the integral sign: if \|H(t, ·) − H(0, ·)\| ≤ \|t\| w with w μ summable and ∂_t H(0, x) = β(x), then β is μ summable and t ↦ ∫ H(t, ·) − H(0, ·) dμ has derivative ∫ β dμ at 0. | [`ddg_integral_derivative`](../theories/DdgFirstVariationPoint.v#L68) | Formalised (new). |
| A.8 | The frozen integrand F(x, ·) is of class 1 on {S : (x, S) ∈ U}, hence differentiable relative to G(n, d); B_F(x, S) is defined through it. | [`ddg_frozen_class_one`](../theories/DdgFirstVariationPoint.v#L215), [`ddg_frozen_differentiable`](../theories/DdgFirstVariationPoint.v#L247) | Formalised. |
| A.8 | d/dt F(φ_t(x), Dφ_t(x)(S)) ‖∧_d(Dφ_t(x) ∘ S)‖ at t = 0 equals D_x F(x, S)(g(x)) + B_F(x, S) • Dg(x). | [`ddg_point_flow_integrand`](../theories/DdgFirstVariationPoint.v#L280), [`ddg_point_first_variation_integrand`](../theories/DdgFirstVariationPoint.v#L289), [`ddg_point_flow_integrand_derivative`](../theories/DdgFirstVariationPoint.v#L328) | Formalised. |
| A.8, ddg:A.2 | Lemma A.2: d/dt F(φ_t# V) at t = 0 equals ∫ D_x F(x, S)(g(x)) + B_F(x, S) • Dg(x) dV(x, S). | [`ddg_lemma_A_2`](../theories/DdgFirstVariationPoint.v#L686), [`ddg_lemma_A_2_image`](../theories/DdgFirstVariationPoint.v#L708) | Formalised for Ω = R^n and g vanishing outside a ball; for F(V) = ∞ in the form d/dt ∫ (F(φ_t(x), Dφ_t(x)(S)) ‖∧_d(Dφ_t(x) ∘ S)‖ − F(x, S)) dV(x, S). |
| A.9 | \|‖∧_d((1 + t L) ∘ T)‖ − 1\| ≤ 2^d \|t\| \|L\| and \|F(T(t)) ‖∧_d((1 + t L) ∘ T)‖ − F(T)\| ≤ 2^d (3 n^{1/2} Λ + Φ) \|t\| \|L\| for \|t\| \|L\| ≤ 1/2, Lip F ≤ Λ and \|F\| ≤ Φ on G(n, d). | [`ddg_jacobian_estimate`](../theories/DdgWeightedJacobianEstimate.v#L163), [`ddg_weighted_jacobian_estimate`](../theories/DdgWeightedJacobianEstimate.v#L185) | Formalised (new). |
| A.9, ddg:A.2const | Lemma A.2 for F not depending on the point: d/dt ∫ F d(φ_t)_# V at t = 0 equals ∫ B_F(T) • Dg(x) dV(x, T). | [`ddg_lemma_A_2_constant`](../theories/DdgFirstVariation.v#L557), [`ddg_lemma_A_2_constant_lipschitz`](../theories/DdgFirstVariation.v#L398) | Formalised for Ω = R^n, V of finite mass and F of class 1 on a neighbourhood of G(n, d). |
