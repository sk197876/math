# Symbols: notations of the book and Rocq declarations

Source numbering and printed pages refer to
[Federer1969](bibliography.md#federer1969); see the
[bibliography](bibliography.md) for source editions.

This map follows the two lists of notations in Federer, *Geometric Measure
Theory* (1969): the glossary of standard notations used but not defined in
the text (p. 669), and the list of basic notations defined in the text, in
the order of their appearance (pp. 670–671). Each row gives the Rocq
notation or declaration expressing the symbol, with links to the defining
statements. Most standard notations are those of MathComp. "Not formalised" marks notations without a corresponding declaration.
See the section accounts linked from [toc.md](toc.md) for current completed
and pending numbered items and for degree and coverage qualifications.
The notions of the book's index are mapped in [index.md](index.md).

## Standard notations (p. 669)

The glossary notations are mostly expressed by MathComp or Rocq notation; project declarations are linked.

| Symbol | Meaning | Rocq |
| --- | --- | --- |
| $\in$ | membership | MathComp `classical_sets`: a set is a predicate, `A x`; boolean form `x \in A` |
| $\subset$ | inclusion | MathComp `classical_sets`: `[`A`](../theories/TraceAlgebra.v#L36)<=` B `` |
| $\emptyset$ | empty set | MathComp `classical_sets`: `set0` |
| $\{x : \dots\}$ | class of all $x$ satisfying a condition | MathComp `classical_sets`: `[set x \| P x]` |
| $\{a\}, \{a,b\}, \{a,b,c\}, \dots$ | classes with listed elements | MathComp `classical_sets`: `[set a]`, `[set a; b]`, `[set a; b; c]` |
| $A \cup B$ | union | MathComp `classical_sets`: `[`A`](../theories/TraceAlgebra.v#L36)\|` B `` |
| $A \cap B$ | intersection | MathComp `classical_sets`: `[`A`](../theories/TraceAlgebra.v#L36)&` B `` |
| $A \sim B$ | difference | MathComp `classical_sets`: `[`A`](../theories/TraceAlgebra.v#L36)\` B `` |
| $\bigcup F = \bigcup_{A \in F} A$ | union of a class | MathComp `classical_sets`: `\bigcup_(A in F) A` |
| $\bigcap F = \bigcap_{A \in F} A$ | intersection of a class | MathComp `classical_sets`: `\bigcap_(A in F) A` |
| $(x,y)$ | ordered pair | Rocq pair `(x, y)` of type `X * Y` |
| $s = (s_1, s_2, s_3, \dots)$ | sequence | function `nat -> X`, indexed from 0; `seq X` or `n.-tuple X` for finite sequences |
| $\operatorname{dmn} f$ | domain | the source type of a total map; [`partial_function_domain`](../theories/PartialFunctionUP.v#L27) for partial maps |
| $\operatorname{im} f$ | image | MathComp `classical_sets`: `range f`; `` f @` A `` for the image of a set |
| $f^{-1} = \operatorname{inv} f$ | inverse relation | MathComp `classical_sets`: `` f @^-1` B `` (inverse image); [`partial_function_preimage`](../theories/PartialFunctionUP.v#L33); MathComp [`functions`](../theories/EuclideanPartitionFamilySealed.v#L33): `f^-1` for `{inv _ >-> _}` |
| $g \circ f$ | composition | `g \o f` (`ssrfun`); [`linear_comp`](../theories/TensorUP.v#L93), [`hom_comp`](../theories/Hom.v#L165) for linear maps |
| $f : X \to Y$ | $f$ maps $X$ into $Y$ | function type `X -> Y`; MathComp [`functions`](../theories/EuclideanPartitionFamilySealed.v#L33): `{fun A >-> B}` for subsets |
| $\langle x, f \rangle = f(x)$ | value of $f$ at $x$ | application `f x` |
| $\langle \cdot, f \rangle = f(\cdot) = f$ | the function itself | [`f`](../theories/ProductSpaceMaps.v#L68), or `fun x => f x` |
| $\mathbf 1_A$ | identity map of $A$ | `idfun` (`ssrfun`); [`linear_id`](../theories/TensorUP.v#L86) for linear maps |
| $f \vert A$ | restriction | MathComp [`functions`](../theories/EuclideanPartitionFamilySealed.v#L33): `` f \_ A ``; [`partial_function_source_restrict`](../theories/PartialFunctionSourceRestriction.v#L14) |
| $X \times Y$ | Cartesian product | product type `X * Y`; MathComp `classical_sets`: `[`A`](../theories/TraceAlgebra.v#L36)*` B `` for subsets |
| $f \times g$ | product map, $(f \times g)(a,c) = (f(a), g(c))$ | [`cartesian_map`](../theories/ProductMeasureBijections.v#L20) |
| $X^n$ | $n$-fold Cartesian product | `n.-tuple X` or `'I_n -> X`; $\mathbf R^n$ is [`R_n`](../theories/GrassmannAbbreviations.v#L34) |
| $Y^X$ | all functions from $X$ into $Y$ | function type `X -> Y`; `{ffun X -> Y}` for finite `X` |
| $\operatorname{card} S$ | cardinal number | MathComp `#\|A\|` for finite types; [`counting_measure`](../theories/CountingMeasure.v#L16) gives $\operatorname{card} S$ or $\infty$ |
| $\aleph_{m-1}$ | $m$-th infinite cardinal | no aleph notation; $\aleph_0$ through MathComp `cardinality`: `countable A`; cardinals are compared by injections, as in [`is_ulam_set`](../theories/UlamCardinalUP.v#L24) |
| $\operatorname{Int} T$ | interior | MathComp `topology`: `` T° `` (`interior T`) |
| $\operatorname{Clos} T$ | closure | MathComp `topology`: `closure T` |
| $\operatorname{Bdry} T$ | boundary | no MathComp notation; `` closure T `\` T° `` |
| $\simeq$ | isomorphism | no notation; mutually inverse maps with both `cancel` laws, e.g. [`tensor_Hom_isomorphism`](../theories/HomTensor.v#L126) |
| $G/H$ | class of cosets | MathComp `generic_quotient`: `{eq_quot e}`, used for [`G_o`](../theories/OrientedGrassmann.v#L96); [`module_quotient`](../theories/ModuleQuotient.v#L102) for vector spaces |
| $\ker f$ | kernel | `[set x \| f x = 0]`; [`linear_functional_kernel`](../theories/LinearFunctionalKernel.v#L19) for functionals |
| $V \oplus W$ | direct sum | MathComp `ssralg`: product `(V * W)%type` with its `lmodType` structure |
| $\bigoplus_{j \in J} V_j$ | direct sum of a family | [`grading`](../theories/GradedAlgebra.v#L24) for sums indexed by degrees |
| $\mathbf Z$ | integers | MathComp `int` |
| $\mathbf Z_\nu = \mathbf Z/(\nu \mathbf Z)$ | integers modulo $\nu$ | MathComp `zmodp`: `'Z_n` |
| $\mathbf Q$ | rational numbers | MathComp `rat` |
| $\mathbf R$ | real numbers | an abstract `R : realType` (MathComp `reals`) |
| $\mathbf C$ | complex numbers | [`ComplexScalars.C`](../theories/ComplexScalarSealed.v#L20), specified by [`is_complex_scalar_system`](../theories/ComplexScalarUP.v#L17) |
| $\mathbf i = (0,1) \in \mathbf C = \mathbf R \times \mathbf R$ | square root of $-1$ | [`ComplexScalars.ii`](../theories/ComplexScalarSealed.v#L26) |
| $\dim V$ | dimension over $\mathbf R$ | MathComp [`vector`](../theories/HilbertFunctionalSealed.v#L17): `dim V` for a `vectType`; [`finite_basis_vect`](../theories/FiniteDimension.v#L186) supplies one from a finite basis |
| $\dim_{\mathbf C} V$ | dimension over $\mathbf C$ | MathComp `dim` over the complex scalars, e.g. in [`realified_dimension`](../theories/ComplexRealBasis.v#L156) |
| $\operatorname{Hom}(V,W)$ | $\mathbf R$ linear maps of $V$ into $W$ | [`Hom`](../theories/Hom.v#L47); MathComp `{linear V -> W}` |

## Notations defined in the text (pp. 670–671)

The rows follow the printed order; coverage includes 1.1–1.10 (1.1 in part), 2.1–2.7, complete items 2.8.1–2.8.7 and 2.8.10–2.8.20, partial items 2.8.8–2.8.9, items 2.9.1–2.9.25, item 2.10.1, integer-degree coverage of 2.10.2, items 2.10.3–2.10.4, items 2.10.5 and 2.10.7–2.10.9, the supporting theorem 2.10.10, the integer-degree Hausdorff core of 2.10.11, and items 2.10.12–2.10.27 in the existing degree interfaces, and 2.10.28 for concave gauges and fractional power-gauge Cantor pairs (real-degree Hausdorff identification pending).

| Federer | Symbol | Meaning | Rocq |
| --- | --- | --- | --- |
| 1.1.1 | $\otimes$ | tensor product of spaces and of vectors | [`is_tensor_product_family`](../theories/TensorFamilyUP.v#L39), [`tensor`](../theories/TensorSealed.v#L117), [`tensor_mul`](../theories/TensorSealed.v#L123) |
| 1.2.3 | $\otimes_{\ast}$ | tensor algebra | [`is_graded_tensor_algebra`](../theories/TensorAlgebraUP.v#L73), [`tensor_algebra`](../theories/TensorAlgebraSealed.v#L34) |
| 1.2.3 | $\otimes_m$ | $m$-th tensor power | [`tensor_power`](../theories/TensorPowerComponents.v#L27) |
| 1.3.1 | $\mathfrak A$ | ideal generated by all $x \otimes x$ | [`mV`](../theories/ExteriorIdeal.v#L109) |
| 1.3.1 | $\bigwedge_{\ast}$ | exterior algebra | [`is_exterior_power_algebra`](../theories/ExteriorAlgebraUP.v#L77), [`exterior_space`](../theories/ExteriorAlgebra.v#L41); notation [`⋀* V`](../theories/ExteriorPowers.v#L528) |
| 1.3.1 | $\bigwedge_m$ | $m$-vectors | [`exterior_power`](../theories/ExteriorGrading.v#L52); notation [`⋀^ m V`](../theories/ExteriorPowers.v#L530) |
| 1.3.1 | $\wedge$ | exterior multiplication | [`wedge`](../theories/ExteriorAlgebra.v#L51); notation [`x ∧ y`](../theories/ExteriorPowers.v#L532) |
| 1.3.2 | $e_\lambda$ | $e_{\lambda(1)} \wedge \dots \wedge e_{\lambda(m)}$ | [`e_lambda`](../theories/FiniteExteriorPowers.v#L47) |
| 1.3.2 | $\Lambda(n,m)$ | increasing maps of $\{1,\dots,m\}$ into $\{1,\dots,n\}$ | [`Lambda`](../theories/ExteriorIndices.v#L178) |
| 1.3.3 | $\operatorname{Sh}(p,q)$ | shuffles | [`Sh`](../theories/Shuffles.v#L41) |
| 1.3.3 | $\operatorname{index}(\sigma)$ | sign of a permutation | [`FedererPermutation.index`](../theories/InversionCount.v#L231) |
| 1.3.4 | $\det(f)$ | determinant of an endomorphism | [`det`](../theories/ExteriorDeterminant.v#L139) |
| 1.4.1 | $\bigwedge^m$ | alternating $m$ linear maps; $m$-covectors | [`A_m`](../theories/AlternatingForms.v#L86), [`covector`](../theories/AlternatingSum.v#L173) |
| 1.4.1 | $\operatorname{Hom}^m$ | linear maps on the algebra vanishing off degree $m$ | [`Hom_m`](../theories/HomogeneousHom.v#L47) |
| 1.4.1 | $\bigwedge^{\ast}$ | direct sum of the $\bigwedge^m$ | [`A_star`](../theories/AlternatingSum.v#L32), [`A_covectors`](../theories/AlternatingSum.v#L179) |
| 1.4.1 | $\langle \xi, f \rangle$ | pairing of $m$-vectors and $m$-covectors | [`pairing`](../theories/AlternatingPairing.v#L41) |
| 1.4.2 | $\wedge$ | exterior multiplication of alternating forms | [`form_wedge`](../theories/AlternatingProduct.v#L85), [`alternating_algebra`](../theories/AlternatingProduct.v#L76) |
| 1.4.3 | $\omega_\lambda$ | $\omega_{\lambda(1)} \wedge \dots \wedge \omega_{\lambda(m)}$ | [`omega_lambda`](../theories/CovectorProducts.v#L34) |
| 1.4.5 | $\Gamma(f)$ | tensor corresponding to $f$ by the Hom-tensor isomorphism | [`Gamma`](../theories/Gamma.v#L56) |
| 1.4.5 | $\operatorname{trace}$ | trace on the equal-degree algebra and of an endomorphism | [`trace`](../theories/TraceDefinition.v#L115), [`trace_Hom`](../theories/TraceDefinition.v#L149) |
| 1.5.1 | $\mathbin{\lrcorner}$ | interior multiplication $\bigwedge_p V \times \bigwedge^q V \to \bigwedge^{q-p} V$ | [`is_right_interior`](../theories/InteriorUP.v#L31), [`right_interior`](../theories/RightInterior.v#L56); notation [`eta ⌟[hpq] phi`](../theories/RightInterior.v#L164) |
| 1.5.1 | $\mathbin{\llcorner}$ | interior multiplication $\bigwedge_q V \times \bigwedge^p V \to \bigwedge_{q-p} V$ | [`is_left_interior`](../theories/InteriorUP.v#L44), [`left_interior`](../theories/LeftInterior.v#L34); notation [`zeta ⌞[h2, hpq] a`](../theories/LeftInterior.v#L145) |
| 1.5.2 | $\mathbf D_p$ | duality isomorphism $\bigwedge_p V \to \bigwedge^{n-p} V$ | [`D_p`](../theories/DualityMaps.v#L31) |
| 1.5.2 | $\mathbf D^p$ | duality isomorphism $\bigwedge^p V \to \bigwedge_{n-p} V$ | [`D_upper`](../theories/DualityMaps.v#L58) |
| 1.6.2 | $\mathbf G(n,m)$ | $m$ dimensional subspaces of $\mathbf R^n$ | [`FedererEuclideanGrassmann.G`](../theories/GrassmannAbbreviations.v#L48), [`G`](../theories/GrassmannSubspaces.v#L49) |
| 1.6.2 | $\mathbf G_0(n,m)$ | oriented $m$ dimensional subspaces | [`FedererEuclideanGrassmann.G_0`](../theories/GrassmannAbbreviations.v#L68), [`G_o`](../theories/OrientedGrassmann.v#L96) |
| 1.6.6 | $\bigwedge^m_{\mathbf C}$ | complex alternating $m$ linear maps | [`complex_form_subspace`](../theories/ComplexFormSubspace.v#L28), [`complex_multilinear_form`](../theories/ComplexAlternatingForms.v#L26) |
| 1.6.6 | $\bigwedge^{\ast}_{\mathbf C}$ | direct sum of the $\bigwedge^m_{\mathbf C}$ | [`complex_alternating_sum`](../theories/ComplexAlternatingSum.v#L27) |
| 1.7.1 | $x \bullet y$ | inner product | [`is_inner_product`](../theories/InnerProductUP.v#L24), [`euclidean_inner_product`](../theories/EuclideanInnerProduct.v#L19) |
| 1.7.1 | $\lvert x \rvert$ | norm $(x \bullet x)^{1/2}$ | [`is_inner_norm`](../theories/InnerNormUP.v#L15), [`inner_norm`](../theories/InnerNorm.v#L15) |
| 1.7.2 | $\mathbf O(n,m)$ | orthogonal injections of $\mathbf R^m$ into $\mathbf R^n$ | [`FedererOrthogonal.O`](../theories/OrthogonalEuclidean.v#L21), [`is_orthogonal_map`](../theories/OrthogonalMaps.v#L15) |
| 1.7.4 | $f^{\ast}$ | adjoint | [`is_adjoint`](../theories/AdjointUP.v#L12), [`inner_adjoint`](../theories/Adjoint.v#L23) |
| 1.7.4 | $\mathbf O^{\ast}(n,m)$ | orthogonal projections of $\mathbf R^n$ onto $\mathbf R^m$ | [`O_star`](../theories/CoordinateProjection.v#L21) |
| 1.7.4 | $\mathbf p_\lambda$ | coordinate projection | [`coordinate_projection`](../theories/CoordinateProjection.v#L56) |
| 1.7.5 | $\xi \bullet \eta$ | inner product of $m$-vectors | [`is_inner_exterior_extension`](../theories/InnerExteriorUP.v#L17), [`exterior_inner_form`](../theories/InnerExterior.v#L64) |
| 1.7.5 | $\lvert \xi \rvert$ | Euclidean norm of an $m$-vector | [`exterior_norm`](../theories/ExteriorNorm.v#L23) |
| 1.7.5 | $\phi \bullet \psi$ | inner product of $m$-covectors | [`is_exterior_covector_inner_product`](../theories/ExteriorCovectorInnerUP.v#L14), [`exterior_covector_inner`](../theories/ExteriorCovectorInner.v#L25) |
| 1.7.5 | $\lvert \phi \rvert$ | Euclidean norm of an $m$-covector | [`exterior_covector_norm`](../theories/ExteriorCovectorInner.v#L47) |
| 1.7.6 | $\lVert f \rVert$ | operator norm | [`is_operator_norm`](../theories/OperatorNormUP.v#L17), [`linear_operator_norm`](../theories/OperatorNorm.v#L27) |
| 1.7.8 | $\ast$ | Hodge star | [`hodge_vector`](../theories/HodgeMaps.v#L29), [`hodge_covector`](../theories/HodgeMaps.v#L43) |
| 1.7.10 | $\operatorname{discr}$ | discriminant of a bilinear form | [`bilinear_discriminant`](../theories/BilinearInvariants.v#L35) |
| 1.7.10 | $\operatorname{trace}$ | trace of a bilinear form | [`bilinear_trace`](../theories/BilinearInvariants.v#L40) |
| 1.8.1 | $\lVert \phi \rVert$ | comass | [`is_comass`](../theories/ComassUP.v#L24), [`comass`](../theories/Comass.v#L26) |
| 1.8.1 | $\lVert \xi \rVert$ | mass | [`is_mass`](../theories/MassUP.v#L21), [`mass`](../theories/Mass.v#L30) |
| 1.9.1 | $\mathfrak B$ | ideal generated by all $x \otimes y - y \otimes x$ | [`commutator_ideal`](../theories/SymmetricIdeal.v#L99) |
| 1.9.1 | $\bigodot_{\ast}$ | symmetric algebra | [`is_symmetric_power_algebra`](../theories/SymmetricAlgebraUP.v#L53), [`symmetric_algebra`](../theories/SymmetricSealed.v#L25) |
| 1.9.1 | $\bigodot_m$ | $m$-th symmetric power | [`symmetric_power`](../theories/SymmetricGrading.v#L40) |
| 1.9.1 | $\odot$ | symmetric multiplication | [`symmetric_product`](../theories/SymmetricAlgebra.v#L38) |
| 1.9.2 | $e^\alpha$ | monomial $e_1^{\alpha_1} \odot \dots \odot e_n^{\alpha_n}$ | [`symmetric_monomial`](../theories/SymmetricMonomials.v#L52) |
| 1.9.2 | $\Xi(n,m)$ | $n$ termed exponent sequences with sum $m$ | [`symmetric_indices`](../theories/SymmetricMultiIndices.v#L92) |
| 1.9.3 | $t^\alpha$ | $t_1^{\alpha_1} \cdots t_n^{\alpha_n}$ | [`symmetric_scalar_monomial`](../theories/SymmetricDividedMonomials.v#L20) |
| 1.9.3 | $v^\alpha$ | $v_1^{\alpha_1} \odot \dots \odot v_n^{\alpha_n}$ | [`symmetric_monomial`](../theories/SymmetricMonomials.v#L52) |
| 1.9.3 | $\alpha!$ | $\alpha_1! \cdots \alpha_n!$ | [`symmetric_multi_factorial`](../theories/SymmetricDividedMonomials.v#L15) |
| 1.10.1 | $\bigodot^m$ | symmetric $m$ linear maps | [`S_m`](../theories/SymmetricForms.v#L30), [`symmetric_covector`](../theories/SymmetricFormSum.v#L108) |
| 1.10.1 | $\langle \xi, f \rangle$ | pairing with symmetric $m$-vectors | [`symmetric_pairing`](../theories/SymmetricPairing.v#L25) |
| 1.10.1 | $\operatorname{Hom}^m$ | linear maps on $\bigodot_{\ast} V$ vanishing off degree $m$ | [`Hom_m`](../theories/HomogeneousHom.v#L47) on `symmetric_grading`, [`homogeneous_sform`](../theories/SymmetricFormIsomorphism.v#L45) |
| 1.10.1 | $\bigodot^{\ast}$ | direct sum of the $\bigodot^m$ | [`S_star`](../theories/SymmetricFormSum.v#L22), [`S_symmetric_covectors`](../theories/SymmetricFormSum.v#L111) |
| 1.10.2 | $\odot$ | multiplication of symmetric forms | [`sform_product`](../theories/SymmetricFormProduct.v#L55), [`symmetric_forms_algebra`](../theories/SymmetricFormProduct.v#L49) |
| 1.10.2 | $\omega^\alpha$ | monomial in one-forms $\omega_i$ | [`symmetric_one_form_monomial`](../theories/SymmetricDualMonomialProducts.v#L33), [`symmetric_dual_monomial`](../theories/SymmetricDualMonomialBasis.v#L23) |
| 1.10.3 | $\mathbin{\lrcorner}$ | symmetric interior multiplication into forms | [`is_symmetric_right_interior`](../theories/SymmetricInteriorUP.v#L30), [`symmetric_right_interior`](../theories/SymmetricRightInterior.v#L51) |
| 1.10.3 | $\mathbin{\llcorner}$ | symmetric interior multiplication into vectors | [`is_symmetric_left_interior`](../theories/SymmetricInteriorUP.v#L40), [`symmetric_left_interior`](../theories/SymmetricLeftInterior.v#L32) |
| 1.10.5 | $\lvert \phi \rvert$ | Euclidean norm of a symmetric form | [`symmetric_form_norm`](../theories/SymmetricFormInner.v#L50), [`is_symmetric_form_inner_product`](../theories/SymmetricFormInnerUP.v#L28) (stated with 1.10.6) |
| 1.10.5 | $\lvert \xi \rvert$ | Euclidean norm on $\bigodot_m V$ | [`is_inner_symmetric_extension`](../theories/InnerSymmetricUP.v#L18), [`symmetric_inner_norm`](../theories/SymmetricInnerNorm.v#L24) |
| 1.10.5 | $\lVert \phi \rVert$ | supremum norm of a symmetric form | [`is_symmetric_operator_norm`](../theories/SymmetricOperatorNormUP.v#L37), [`symmetric_operator_norm`](../theories/SymmetricOperatorNorm.v#L25) |
| 1.10.5 | $\lVert \xi \rVert$ | mass on $\bigodot_m V$ | [`is_symmetric_mass`](../theories/SymmetricMassUP.v#L32), [`symmetric_mass`](../theories/SymmetricMass.v#L24) |
| 1.10.5 | $\lVert P \rVert$ | supremum of a polynomial function on the unit ball | [`is_polynomial_norm`](../theories/PolynomialNormUP.v#L31), [`polynomial_norm`](../theories/PolynomialNorm.v#L24) |
| 1.10.6 | $\mathscr S(n,m)$ | all maps of $\{1,\dots,m\}$ into $\{1,\dots,n\}$ | MathComp `{ffun 'I_m -> 'I_n}`, as in [`symmetric_form_norm_word_squares`](../theories/SymmetricFormWordSquares.v#L65) |
| 2.1.1 | $\overline{\mathbf R}$ | extended real numbers | MathComp `\bar R`; [`extended_real_line`](../theories/ExtendedRealOrderTopology.v#L18) |
| 2.1.1 | $\inf$ | infimum in $\overline{\mathbf R}$ | [`extended_real_inf`](../theories/ExtendedRealBounds.v#L21) |
| 2.1.1 | $\sup$ | supremum in $\overline{\mathbf R}$ | [`is_extended_real_supremum`](../theories/ExtendedRealBoundsUP.v#L16), [`extended_real_sup`](../theories/ExtendedRealBounds.v#L16) |
| 2.1.1 | $\uparrow$ | increasing convergence | [`extended_increases_to`](../theories/ExtendedRealOrderLimit.v#L26) |
| 2.1.1 | $\downarrow$ | decreasing convergence | [`extended_decreases_to`](../theories/ExtendedRealOrderLimit.v#L31) |
| 2.1.1 | $\operatorname{sign}$ | sign | [`extended_sign`](../theories/ExtendedRealPartial.v#L76) |
| 2.1.1 | $f^+$ | positive part | [`extended_positive_part`](../theories/ExtendedRealPartial.v#L65) |
| 2.1.1 | $f^-$ | negative part | [`extended_negative_part`](../theories/ExtendedRealPartial.v#L71) |
| 2.1.1 | $\Sigma$ | sum of an arbitrary family in $\overline{\mathbf R}$ | [`is_numerical_summation`](../theories/NumericalSumUP.v#L21), [`numerical_sum`](../theories/NumericalSum.v#L18), [`nonnegative_sum`](../theories/NonnegativeSum.v#L18) |
| 2.1.2 | $\mathbf 2^X$ | class of all subsets of $X$ | MathComp `set X`; measures `set X -> \bar R` in [`is_measure`](../theories/MeasureUP.v#L20) |
| 2.1.2 | $\phi \mathbin{\llcorner} Y$ | restriction of a measure | [`measure_restrict`](../theories/MeasureRestriction.v#L17) |
| 2.1.2 | $f_{\#}$ | image measure | [`measure_pushforward`](../theories/MeasurePushforward.v#L17) |
| 2.2.1 | $\operatorname{spt} \phi$ | support of a measure | [`is_measure_support`](../theories/MeasureSupportUP.v#L20), [`measure_support`](../theories/MeasureSupport.v#L16) |
| 2.2.6 | $\mathscr P$ | positive integers | `nat`, code $k$ for $k+1$, as in [`positive_sequence_coordinates`](../theories/SequenceSpace.v#L25) |
| 2.2.6 | $\mathscr N$ | sequence space $\mathscr P^{\mathscr P}$ | [`is_positive_sequence_representation`](../theories/SequenceSpaceUP.v#L21), [`positive_sequence_space`](../theories/SequenceSpace.v#L19), [`positive_sequence_distance`](../theories/SequenceSpace.v#L41) |
| 2.2.7 | $\operatorname{Lip}(f)$ | least Lipschitz constant | [`is_least_metric_lipschitz_constant`](../theories/LipschitzUP.v#L34), [`metric_lipschitz_constant`](../theories/LipschitzConstant.v#L17) |
| 2.3.8 | $\mathbf A(\phi, Y)$ | measurable, essentially separably valued functions | [`is_measurable_normed_function`](../theories/MeasurableNormedFunctionUP.v#L33) |
| 2.3.8 | $\lvert f \rvert_\phi$ | gauge of convergence in measure | [`measure_gauge`](../theories/MeasureGauge.v#L35) |
| 2.4.2 | $\int^{\ast} f \, d\phi$ | upper integral | [`is_measure_upper_integral`](../theories/MeasureIntegralUP.v#L55), [`measure_upper_integral`](../theories/MeasureIntegralBounds.v#L15) |
| 2.4.2 | $\int_{\ast} f \, d\phi$ | lower integral | [`is_measure_lower_integral`](../theories/MeasureIntegralUP.v#L63), [`measure_lower_integral`](../theories/MeasureIntegralBounds.v#L20) |
| 2.4.2 | $\int f \, d\phi$ | integral | [`is_measure_integral`](../theories/MeasureIntegralUP.v#L71), [`measure_integral`](../theories/MeasureIntegral.v#L16) |
| 2.4.2 | $\phi_x[f(x)]$, $\langle f, \phi \rangle$ | alternative notations for $\int f \, d\phi$ | [`measure_integral`](../theories/MeasureIntegral.v#L16) |
| 2.4.10 | $\int^{\ast}_A$ | upper integral over $A$ | [`measure_subset_upper_integral`](../theories/MeasureSubsetIntegral.v#L29) |
| 2.4.10 | $\int_{\ast A}$ | lower integral over $A$ | [`measure_subset_lower_integral`](../theories/MeasureSubsetIntegral.v#L36) |
| 2.4.10 | $\int_A$ | integral over $A$ | [`is_measure_subset_integral`](../theories/MeasureSubsetIntegral.v#L17), [`measure_subset_integral`](../theories/MeasureSubsetIntegral.v#L44) |
| 2.4.10 | $\int_a^b$ | integral over $\{x : a < x \le b\}$ | [`is_measure_interval_integral`](../theories/MeasureIntervalIntegral.v#L25), [`measure_half_open_interval`](../theories/MeasureIntervalIntegral.v#L19) |
| 2.4.12 | $\phi_{(p)}(f)$ | $\mathbf L_p$ seminorm | [`is_measure_lp_norm`](../theories/MeasureLpNormUP.v#L21), [`measure_lp_norm`](../theories/MeasureLpNorm.v#L17), [`measure_essential_norm`](../theories/MeasureEssentialNorm.v#L18) ($p = \infty$) |
| 2.4.12 | $\mathbf L_p(\phi, Y)$ | Lebesgue space | [`is_measure_lp_function`](../theories/MeasureLpMembershipUP.v#L17), [`is_measure_linfinity_function`](../theories/MeasureLinfinityUP.v#L19) |
| 2.4.12 | $\int f \, d\phi$ | integral of a $Y$ valued function | [`is_measure_vector_integral`](../theories/MeasureVectorIntegralUP.v#L28), [`measure_vector_integral`](../theories/MeasureVectorIntegral.v#L18) |
| 2.4.12 | $Y^{\ast}$ | continuous dual of a normed space | [`is_continuous_dual`](../theories/ContinuousDualUP.v#L13), [`ContinuousDual.space`](../theories/ContinuousDualSealed.v#L12) |
| 2.5.1 | $L^+$ | nonnegative members of a lattice $L$ | [`positive_function_lattice`](../theories/FunctionLatticeUP.v#L44) |
| 2.5.5 | $\mu^+$ | positive variation of a Daniell integral | [`is_daniell_positive_variation`](../theories/DaniellVariationUP.v#L23), [`daniell_positive_variation`](../theories/DaniellVariation.v#L11) |
| 2.5.5 | $\mu^-$ | negative variation of a Daniell integral | [`is_daniell_negative_variation`](../theories/DaniellVariationUP.v#L31), [`daniell_negative_variation`](../theories/DaniellVariationFunctionals.v#L43) |
| 2.5.6 | $\mu_x[f(x)]$ | alternative notation for $\mu(f)$ | application `mu f`; no separate declaration |
| 2.5.13 | $\operatorname{spt} f$ | support of a function | [`real_function_support`](../theories/CompactSupportFunctionUP.v#L15) |
| 2.5.14 | $\mathscr K(X)$ | continuous functions with compact support | [`compactly_supported_continuous_functions`](../theories/CompactSupportFunctionUP.v#L21) |
| 2.5.14 | $\operatorname{spt} \mu$ | support of a Daniell integral on $\mathscr K(X)$ | [`compact_support_daniell_support`](../theories/CompactSupportDaniellSupport.v#L17) |
| 2.5.16 | $\mathbf V_a^b$ | variation of a curve on $[a,b]$ | [`curve_variation`](../theories/CurveVariationUP.v#L106), [`signed_curve_variation`](../theories/CurveVariationUP.v#L105) |
| 2.5.17 | $\int_a^b f \, dg$, $\int_a^b f(x) \, d_x g(x)$ | Riemann–Stieltjes integral | [`stieltjes_integral`](../theories/StieltjesIntegral.v#L227) |
| 2.5.17 | $\mathscr L^1$ | Lebesgue measure on $\mathbf R$ | [`is_lebesgue_line_measure`](../theories/LebesgueLineUP.v#L16), [`lebesgue_scalar_measure`](../theories/LebesgueScalarMeasure.v#L26) |
| 2.5.19 | $L^{\ast}$ | space of Daniell integrals on $L$ | [`daniell_integrals`](../theories/DaniellSpaceWeakTopology.v#L98), [`daniell_weak_space`](../theories/DaniellSpaceWeakTopology.v#L172) |
| 2.5.19 | $\boldsymbol\delta_x$ | evaluation at $x$ | [`point_evaluation`](../theories/DaniellSpaceWeakTopology.v#L230) |
| 2.5.19 | $u_{\#}$ | image of Daniell integrals, $\mu \mapsto \mu(\cdot \circ u)$ | [`daniell_pushforward`](../theories/DaniellSpacePushforward.v#L55) |
| 2.6.1 | $\alpha \times \beta$ | Cartesian product of measures | [`is_product_measure`](../theories/ProductMeasureUP.v#L19), [`product_measure`](../theories/ProductMeasure.v#L14) |
| 2.6.5 | $\mathscr L^n$ | Lebesgue measure on $\mathbf R^n$ | [`is_euclidean_lebesgue_family`](../theories/EuclideanLebesgueUP.v#L20), [`euclidean_lebesgue_measure`](../theories/EuclideanLebesgueDimensions.v#L21) |
| 2.7.1 | $A^x$ | orbit map $g \mapsto A(g,x)$ | [`orbit_map`](../theories/HomogeneousSpaceUP.v#L21) |
| 2.7.1 | $A_g$ | action map $x \mapsto A(g,x)$ | `A g` (the action is curried); [`homogeneous_translation_homeomorphism`](../theories/HomogeneousSpaceLaws.v#L78) |
| 2.7.1 | $G^x$ | isotropy subgroup | [`isotropy_subgroup`](../theories/HomogeneousSpaceUP.v#L27) |
| 2.7.1 | $u_g$ | $u \circ A_g$ | written `u \o A g`; no abbreviation |
| 2.7.8 | $\Delta_G$ | modular function | [`is_modular_function`](../theories/ModularFunctionUP.v#L66), [`modular_function_exists`](../theories/ModularFunction.v#L225) |
| 2.7.16 | $\mathscr A(V,W)$ | affine maps of $V$ into $W$ | [`affine_maps`](../theories/AffineMapSpaceSealed.v#L54), [`is_affine_map_space`](../theories/AffineMapSpaceUP.v#L40), [`affine_isomorphism`](../theories/AffineMaps.v#L167), [`affine_map_graph`](../theories/AffineMaps.v#L80) |
| 2.7.16 | $\tau_z$ | translation by $z$ | [`affine_translation_add`](../theories/AffineMaps.v#L207), [`affine_translation_compose`](../theories/AffineMaps.v#L229) |
| 2.7.16 | $\mathbf{GL}(n, \mathbf R)$ | general linear group | [`linear_group`](../theories/LinearGroupTopology.v#L95), [`linear_group_mul`](../theories/LinearGroupSealed.v#L92), [`linear_group_operations_lch`](../theories/LinearGroupSealed.v#L117), [`general_linear_det`](../theories/GeneralLinearPunctured.v#L92) |
| 2.7.16 | $\mathbf{SL}(n, \mathbf R)$ | special linear group | [`special_linear`](../theories/SpecialLinearTopology.v#L106), [`special_linear_lch`](../theories/SpecialLinearTopology.v#L159), [`special_linear_punctured_homogeneous`](../theories/SpecialLinearTopology.v#L412) |
| 2.7.16 | $\boldsymbol\alpha(n)$ | $\mathscr L^n$ measure of the unit ball | [`euclidean_unit_ball_volume`](../theories/EuclideanBallVolume.v#L46), [`euclidean_ball_measure`](../theories/EuclideanBallVolume.v#L65), [`euclidean_ball_recursion`](../theories/EuclideanBallVolume.v#L224) |
| 2.7.16 | $\boldsymbol\theta_{n,m}$ | invariant probability measure on $\mathbf O(n,m)$ | [`euclidean_theta_nm_exists_unique`](../theories/EuclideanOrthogonalInvariantMeasures.v#L141), [`orthogonal_injections_invariant_measure`](../theories/OrthogonalInjectionSpaces.v#L475), [`euclidean_orthogonal_injections`](../theories/EuclideanOrthogonalInvariantMeasures.v#L57) |
| 2.7.16 | $\boldsymbol\theta^{\ast}_{n,m}$ | invariant probability measure on $\mathbf O^{\ast}(n,m)$ | [`euclidean_theta_star_nm_exists_unique`](../theories/EuclideanOrthogonalInvariantMeasures.v#L159), [`orthogonal_projections_invariant_measure`](../theories/OrthogonalInjectionSpaces.v#L492), [`euclidean_orthogonal_projections`](../theories/EuclideanOrthogonalInvariantMeasures.v#L68) |
| 2.7.16 | $\boldsymbol\gamma_{n,m}$ | invariant probability measure on $\mathbf G(n,m)$ | [`euclidean_gamma_nm_exists_unique`](../theories/EuclideanOrthogonalInvariantMeasures.v#L180), [`grassmann_invariant_measure`](../theories/GrassmannHomogeneousSpace.v#L472), [`euclidean_grassmann_space`](../theories/EuclideanOrthogonalInvariantMeasures.v#L80) |
| 2.7.16 | $\boldsymbol\beta_t(n,m)$ | integral-geometric constant | [`is_projection_constant`](../theories/OrthogonalProjectionConstants.v#L286), [`projection_constant_exists`](../theories/OrthogonalProjectionConstants.v#L322), [`projection_constant_ratio`](../theories/OrthogonalWedgeIntegrals.v#L419), [`projection_constant_infinity`](../theories/ProjectionConstantNorms.v#L63) |
| 2.8.1 | $\mathbf B(a,r)$ | closed ball | [`metric_closed_ball`](../theories/MetricClosedBalls.v#L16) ([`MetricClosedBalls.v`](../theories/MetricClosedBalls.v)) |
| 2.8.1 | $\mathbf U(a,r)$ | open ball | [`metric_open_ball`](../theories/CoveringFamilyUP.v#L22) ([`CoveringFamilyUP.v`](../theories/CoveringFamilyUP.v)) |
| 2.8.4–2.8.5 | $\hat S$ | enlargement of $S$ in a covering family | [`weighted_enlargement`](../theories/WeightedEnlargements.v#L19) ([`WeightedEnlargements.v`](../theories/WeightedEnlargements.v)), [`family_weighted_enlargement`](../theories/FamilyWeightedEnlargements.v#L27) ([`FamilyWeightedEnlargements.v`](../theories/FamilyWeightedEnlargements.v), exact family domain) |
| 2.8.8 | $\operatorname{diam}$ | diameter | [`is_real_diameter_weight`](../theories/DiametricRegularityUP.v#L19), [`diameter_weight_ball_bound`](../theories/DiameterWeightLaws.v#L32), [`diameter_enlargement_ball_bound`](../theories/BallEnlargementBound.v#L20) (partial item); [`extended_metric_diameter`](../theories/MetricDiameter.v#L16), [`is_extended_metric_diameter`](../theories/MetricDiameterUP.v#L19) serve 2.10.1 |
| 2.8.16 | $(C) \limsup_x f$, $(C) \limsup_{S \to x} f(S)$ | upper limit along a covering relation | [`covering_upper_limit`](../theories/CoveringRelationLimits.v#L30), [`covering_value_range`](../theories/CoveringRelationLimits.v#L22) ([`CoveringRelationLimits.v`](../theories/CoveringRelationLimits.v)); dual [`covering_lower_limit`](../theories/CoveringRelationLimits.v#L37) and partial [`covering_relation_limit`](../theories/CoveringRelationLimits.v#L44) |
| 2.9.1 | $\psi_\phi$ | part of $\psi$ absolutely continuous with respect to $\phi$ | [`measure_continuous_part`](../theories/AbsoluteContinuousPart.v#L19), [`measure_continuous_part_formula`](../theories/AbsoluteContinuousPart.v#L33), [`measure_continuous_part_is_measure`](../theories/AbsoluteContinuousPart.v#L59); [`federer_2_9_3`](../theories/DerivationLowerComparison.v#L24) compares the continuous parts from a strict lower ratio bound; [`federer_2_9_4`](../theories/DerivationComparison.v#L80) gives both comparisons with phi; [`federer_2_9_7`](../theories/DerivationIntegral.v#L52) identifies the mass with the derivate integral |
| 2.9.1 | $\mathbf D(\psi, \phi, V, x)$ | $V$ derivate of $\psi$ with respect to $\phi$ | [`measure_derivate`](../theories/MeasureDerivates.v#L70), [`measure_derivate_graph`](../theories/MeasureDerivates.v#L78); [`federer_2_9_5`](../theories/DerivationExistence.v#L77) proves existence with a finite nonnegative value almost everywhere; [`federer_2_9_6`](../theories/DerivationMeasurable.v#L39) proves measurability; [`measure_mean_function`](../theories/MeasureMeanFunction.v#L22) and [`federer_2_9_8`](../theories/MeasureDifferentiation.v#L33) give differentiation of local integrals; [`federer_2_9_10`](../theories/DerivationInvariance.v#L22) and [`derivate_independent_vitali_relation`](../theories/DerivationUniqueness.v#L49) identify the invariant derivate; [`daniell_derivate_representation`](../theories/DaniellDerivateRepresentation.v#L63) identifies it with the L1 Daniell density |
| 2.9.11 | $P$, $Q$ | points of density one for A, and density zero for its complement | [`measure_density_one_points`](../theories/MeasureDensityPoints.v#L15), [`measure_density_complement_zero_points`](../theories/MeasureDensityPoints.v#L22), [`federer_2_9_11`](../theories/DensityMeasurableSets.v#L78) |
| 2.9.12 | $(\phi, V) \operatorname{ap} \lim_x f$, $(\phi, V) \operatorname{ap} \lim_{z \to x} f(z)$ | approximate limit | [`is_measure_approximate_limit`](../theories/MeasureApproximateLimitUP.v#L18), [`measure_approximate_limit`](../theories/ApproximateLimitUniqueness.v#L48), [`measure_approximate_limit_unique`](../theories/ApproximateLimitUniqueness.v#L19) |
| 2.9.12 | $(\phi,V)\operatorname{ap}\limsup_x f$, $(\phi,V)\operatorname{ap}\liminf_x f$ | upper/lower approximate limits with corrected partial-domain complements | [`measure_approximate_upper_limit`](../theories/MeasureApproximateOrderLimits.v#L62), [`measure_approximate_lower_limit`](../theories/MeasureApproximateOrderLimits.v#L70) |
| 2.9.12 | $(\phi,V)$ density of A at x | partial restricted-measure derivate | [`measure_set_density`](../theories/MeasureSetDensity.v#L21), [`density_characteristic_measurability`](../theories/MeasureSetDensity.v#L38) |
| 2.9.13 | phi measurable iff (phi,V) approximately continuous almost everywhere | separable metric target, conull partial domain | [`federer_2_9_13`](../theories/MeasurableApproximateContinuity.v#L59); converse [`almost_approximate_continuity_measurable`](../theories/ApproximateContinuityMeasurable.v#L22) holds for every topological target |
| 2.9.14 | {x : alpha B(x,r) > beta B(x,r) for some r in J} | open ball-measure comparison locus, J open and positive; both t-scaled corollaries | [`ball_measure_comparison_points`](../theories/OpenBallMeasureComparison.v#L25), [`federer_2_9_14`](../theories/OpenBallMeasureComparison.v#L81); [`ball_measure_upper_comparison_open`](../theories/BallMeasureComparisonCorollaries.v#L22), [`ball_measure_lower_comparison_open`](../theories/BallMeasureComparisonCorollaries.v#L38) |
| 2.9.15 | W, P; psi_phi = psi restricted to X minus (W union P) | infinite centered radius-density points and points with a null ball | [`measure_infinite_centered_density_points`](../theories/CenteredRatioInfinity.v#L129), [`measure_null_ball_points`](../theories/NullBallLocus.v#L22), [`federer_2_9_15`](../theories/CenteredMeasureDecomposition.v#L29) |
| 2.9.15 | limsup as r tends to zero of phi B(x,5r)/phi B(x,r) | exact partial-quotient growth alternative | [`fivefold_ball_ratio_upper_limit`](../theories/FivefoldBallGrowth.v#L32), [`is_centered_density_geometry`](../theories/CenteredDensityGeometry.v#L26) |
| 2.9.16 | V, Y, psi=H^1 restricted to Y | all closed balls containing the point, and the Euclidean line-measure counterexample | [`noncentered_closed_ball_relation`](../theories/NoncenteredBallRelations.v#L18), [`euclidean_affine_coordinate_line`](../theories/EuclideanAffineLineGeometry.v#L34), [`euclidean_affine_line_measure`](../theories/EuclideanAffineLineMeasure.v#L32), [`federer_2_9_16`](../theories/EuclideanLineDerivationCounterexample.v#L143) |
| 2.9.17 | limsup as r tends to zero of psi B(x,r)/phi B(x,r) | zero-or-infinite alternative on a numerator-null measurable target | [`centered_ball_ratio_upper_limit`](../theories/RadialBallRatios.v#L32), [`has_zero_or_infinite_upper_ball_ratio`](../theories/UpperBallRatioDichotomy.v#L26), [`federer_2_9_17`](../theories/UpperBallRatioDichotomy.v#L117) |
| 2.9.18 | c_j, S_j, psi; lower/upper radial ratios | oscillating weighted-hit measure and projected off-line measure | [`is_sparse_ball_cover_sequence`](../theories/SparseBallCoverSequenceUP.v#L23), [`weighted_hit_measure`](../theories/WeightedHitMeasure.v#L25), [`centered_ball_ratio_lower_limit`](../theories/RadialBallLowerLimit.v#L24), [`off_line_projection_measure`](../theories/OffLineProjectionMeasure.v#L20), [`federer_2_9_18_1`](../theories/ScalarBallRatioSharpness.v#L109), [`federer_2_9_18_2`](../theories/EuclideanBallGrowthSharpness.v#L65) |
| 2.9.19 | $g'(x)$ | actual finite partial derivative and absolute-derivative integrand | [`real_curve_derivative`](../theories/RealCurveDerivativeUP.v#L77), [`real_curve_derivative_integrand`](../theories/RealCurveDerivativeIntegrands.v#L20), [`real_curve_absolute_derivative_integrand`](../theories/RealCurveDerivativeIntegrands.v#L28), [`federer_2_9_19`](../theories/RealBVDifferentiation.v#L27) |
| 2.9.20 | absolute continuity of g on [a,b] | finite ordered families with total length at most delta and total absolute increment at most epsilon; all four equivalent conditions | [`is_ordered_real_interval_family`](../theories/OrderedIntervalFamilyUP.v#L17), [`is_absolutely_continuous_real_curve`](../theories/RealAbsoluteContinuityUP.v#L21), [`federer_2_9_20`](../theories/RealAbsoluteContinuity.v#L27) |
| 2.9.21 | integral f dg = integral f g′ dL¹; monotone substitution | actual partial derivative products, both finite change-of-variable formulas, including flat images | [`weighted_real_curve_derivative_integrand`](../theories/WeightedRealDerivativeIntegrand.v#L19), [`absolutely_continuous_stieltjes_integral`](../theories/AbsolutelyContinuousStieltjesIntegral.v#L30), [`absolutely_continuous_monotone_substitution`](../theories/AbsolutelyContinuousChangeOfVariable.v#L29), [`federer_2_9_21`](../theories/AbsolutelyContinuousChangeOfVariable.v#L75) |
| 2.9.22 | $g'(x)$ in a normed space; $v(x)$; $s'=N(g')$ | actual norm derivative, simultaneous scalar dual identities, norm integral and complete four-way absolute-continuity extension | [`federer_2_9_22`](../theories/ReflexiveCurveDifferentiation.v#L39), [`normed_curve_derivative`](../theories/NormedCurveDerivativeUP.v#L76), [`has_normed_curve_derivative`](../theories/NormedCurveDerivativeUP.v#L68), [`normed_absolute_continuity_equivalences`](../theories/NormedAbsoluteContinuity.v#L29) |
| 2.9.23 | $g(x)=\chi_{(0,x)}$; $L^1$ seminorm; weak limit | Lipschitz constant one and no weak difference-quotient limit for x>0 | [`lebesgue_characteristic_curve`](../theories/LebesgueIntervalCharacteristics.v#L82), [`summable_real_seminorm`](../theories/SummableRealSeminorm.v#L20), [`punctured_seminorm_weak_limit`](../theories/SeminormWeakLimitUP.v#L28), [`federer_2_9_23`](../theories/LebesgueCharacteristicCurveCounterexample.v#L87) |
| 2.9.24 | integral f g′ dL¹ + integral g df | local BV/absolute-continuity integration by parts, including a=b | [`federer_2_9_24`](../theories/AbsolutelyContinuousIntegrationByParts.v#L29), [`uniform_right_step_approximation`](../theories/RightStepApproximation.v#L21), [`is_tagged_step_function`](../theories/TaggedStepFunctionUP.v#L17), [`tagged_step_primitive_integral`](../theories/TaggedStepPrimitiveIntegral.v#L25) |
| 2.9.25 | g(t)=integral_S integral_[a,t] u; g′(t)=integral_S u(x,t) | parameter differentiation and absolute continuity | [`federer_2_9_25`](../theories/ParameterIntegralDifferentiation.v#L68), [`parameter_integral_prefix_primitive`](../theories/ParameterIntegralPrimitive.v#L46), [`integral_mean_limit_primitive_derivative_at`](../theories/IntegralMeanPrimitiveDerivative.v#L23) |
| 2.10.1 | phi_delta and psi | approximating infimum and final Caratheodory measure | [`is_metric_scale_envelope`](../theories/MetricScaleEnvelopeUP.v#L19), [`metric_scale_envelope`](../theories/MetricScaleEnvelope.v#L16), [`is_caratheodory_limit`](../theories/CaratheodoryLimitUP.v#L20), [`caratheodory_measure`](../theories/CaratheodoryMeasure.v#L21), [`positive_cutoff_order_limit`](../theories/CaratheodoryScaleConvergence.v#L23) |
| 2.10.1 | open-refinement threshold infimum | alternative metric formula; corrected whole-space-cover topological version | [`is_open_refinement_bound`](../theories/OpenRefinementBoundUP.v#L22), [`metric_caratheodory_open_cover_characterization`](../theories/MetricRefinementCharacterization.v#L66), [`is_global_open_refinement_bound`](../theories/TopologicalOpenRefinementBound.v#L27), [`topological_caratheodory_measure`](../theories/TopologicalCaratheodory.v#L20) |
| 2.10.2 | $\mathscr H^m$ | $m$ dimensional Hausdorff measure | [`is_hausdorff_measure`](../theories/HausdorffMeasureUP.v#L78), [`hausdorff_measure`](../theories/HausdorffMeasure.v#L15) (all integer degrees); [`hausdorff_measure_one_length`](../theories/HausdorffLengthCompatibility.v#L16) identifies the legacy degree-one value; optional real-degree extension pending |
| 2.10.2 | $\mathscr S^m$ | $m$ dimensional spherical measure | [`is_spherical_measure`](../theories/HausdorffMeasureUP.v#L104), [`spherical_measure`](../theories/HausdorffMeasure.v#L31), [`spherical_zero_counting_measure`](../theories/SphericalCountingMeasure.v#L17), [`euclidean_spherical_open_ball_equality`](../theories/SphericalOpenBallAgreement.v#L91) (integer degrees) |
| 2.10.3 | $\mathscr T^m$ | measure from the $m$-vector gauge of sets | [`is_exterior_diameter_measure`](../theories/ExteriorMeasureUP.v#L21), [`exterior_diameter_measure`](../theories/ExteriorMeasure.v#L19); [`exterior_diameter_cost_convex_hull`](../theories/ExteriorDiameterConvexity.v#L83); open, compact and convex covering specifications |
| 2.10.4 | $\mathscr G^m$ | Gross measure | [`is_gross_measure`](../theories/ProjectionMeasureUP.v#L35), [`gross_measure`](../theories/ProjectionMeasure.v#L22), [`projected_volume_gauge`](../theories/ProjectedVolumeGauge.v#L54) |
| 2.10.4 | $\mathscr C^m$ | Carathéodory measure | [`is_caratheodory_projection_measure`](../theories/ProjectionMeasureUP.v#L46), [`caratheodory_projection_measure`](../theories/ProjectionMeasure.v#L61), closed convex-cover equality and [`caratheodory_projection_one_hausdorff_measure`](../theories/CaratheodoryProjectionLength.v#L91) |
| 2.10.5 | $\mathscr I^m_t$ | integral-geometric measure with exponent $t$ | [`is_integral_geometric_measure`](../theories/IntegralGeometricMeasureUP.v#L21), [`integral_geometric_measure`](../theories/IntegralGeometricMeasure.v#L23), [`integral_geometric_normalized_measure_monotone`](../theories/IntegralGeometricExponentMonotone.v#L76), [`integral_geometric_projection_null_iff`](../theories/IntegralGeometricNullSets.v#L62), [`integral_geometric_common_null_sets`](../theories/IntegralGeometricNullSets.v#L95) |
| 2.10.5 | $\mathscr Q^m_t$ | analogue of $\mathscr I^m_t$ from open convex sets | [`is_convex_integral_geometric_measure`](../theories/IntegralGeometricMeasureUP.v#L32), [`convex_integral_geometric_measure`](../theories/IntegralGeometricMeasure.v#L71), [`convex_integral_geometric_infinity`](../theories/IntegralGeometricInfinity.v#L76), [`convex_integral_geometric_normalized_measure_monotone`](../theories/IntegralGeometricExponentMonotone.v#L98), [`finite_convex_integral_geometric_open_closed_agreement`](../theories/IntegralGeometricFiniteClosedCovers.v#L32), [`convex_integral_geometric_open_closed_agreement`](../theories/IntegralGeometricClosedCovers.v#L96) |
| 2.10.7 | interval cost g(b)-g(a), phi_delta, psi | raw-increment interval construction, all positive cutoffs, induced measure and H1=L1 on R | [`stieltjes_interval_cost`](../theories/StieltjesCaratheodoryUP.v#L33), [`is_stieltjes_caratheodory_measure`](../theories/StieltjesCaratheodoryUP.v#L41), [`stieltjes_caratheodory_all_scales`](../theories/StieltjesCaratheodoryConsequences.v#L26), [`stieltjes_caratheodory_induced_pair`](../theories/StieltjesCaratheodoryIdentification.v#L65), [`real_hausdorff_measure_one_lebesgue`](../theories/RealHausdorffLebesgue.v#L74) |
| 2.10.8 | sup_H sum_(B in H) zeta(B), shrinking partition cost limit | all Borel partitions of A and their arbitrary shrinking sequences | [`borel_partition_cost`](../theories/BorelPartitionCoverBounds.v#L23), [`borel_partition_cost_values`](../theories/BorelPartitionCharacterization.v#L24), [`borel_partition_cost_formula`](../theories/BorelPartitionCharacterization.v#L53), [`borel_partition_cost_convergence`](../theories/BorelPartitionCostConvergence.v#L60), [`federer_2_10_8`](../theories/BorelPartitionTheorem.v#L25) |
| 2.10.9 | I_t = lim_(s->t-) I_s | left-exponent limit, including infinity, arbitrary approaching real exponents and targets | [`integral_geometric_exponent_left_limit`](../theories/IntegralGeometricExponentLimit.v#L58), [`federer_2_10_9`](../theories/IntegralGeometricExponentLimit.v#L85) |
| 2.10.9 | $N(f, y)$ | multiplicity $\operatorname{card}(f^{-1}\{y\})$ | [`mapping_multiplicity`](../theories/MappingMultiplicity.v#L23), used for 2.10.10 |
| 2.9.9 | $(\phi,V)$ Lebesgue set of $f$ | points where the mean distance to f(x) tends to zero | [`measure_lebesgue_set`](../theories/MeasureLebesgueSet.v#L17), [`federer_2_9_9`](../theories/NormedLebesguePoints.v#L22) |
| 2.10.11 | integral N(f restricted to A,y) dH^m <= (Lip f)^m H^m(A) | integer-degree Hausdorff multiplicity bound; real-degree and spherical variants pending | [`lipschitz_hausdorff_multiplicity_integer_bound`](../theories/LipschitzMultiplicityInteger.v#L29), [`federer_2_10_11_integer`](../theories/LipschitzMultiplicityInteger.v#L65) |
| 2.10.12 | diam C <= H1(C), C connected | connected-set length lower bound on arbitrary metric spaces | [`distance_from_point_nonexpanding`](../theories/ConnectedHausdorffLength.v#L25), [`connected_distance_image_contains_segment`](../theories/ConnectedHausdorffLength.v#L39), [`federer_2_10_12`](../theories/ConnectedHausdorffLength.v#L82) |
| 2.10.13 | V_a^b g = integral N(g restricted to [a,b],y) dH1(y) | continuous metric curve length, including infinite variation | [`federer_2_10_13_length`](../theories/CurveLengthMultiplicity.v#L114), [`federer_2_10_13`](../theories/ContinuousCurveLength.v#L25) |
| 2.10.13 | s and psi; H1[g(T)]=0 for L1-null T in [a,b] | induced arc-length/image-cost measure and absolute-continuity criterion | [`continuous_curve_arc_length_image_measure`](../theories/ArcLengthImageMeasure.v#L49), [`curve_maps_null_sets_to_null_length`](../theories/CurveNullImageCriterion.v#L32), [`continuous_curve_null_image_criterion`](../theories/CurveNullImageCriterion.v#L122) |
| 2.10.14 | alpha_+(x), alpha_-(x) | one-sided upper limits of distance[g(t),g(x)] | [`curve_right_jump_size`](../theories/CurveOneSidedJumpUP.v#L59), [`curve_left_jump_size`](../theories/CurveOneSidedJumpUP.v#L64), [`curve_one_sided_jump`](../theories/CurveOneSidedJumpUP.v#L53) |
| 2.10.14 | upper integral N(g restricted to [a,b],y) dH1(y) | corrected upper multiplicity integral; erratum p. 3, book p. 177 line 23 | [`curve_upper_multiplicity_integral`](../theories/CurveUpperMultiplicity.v#L26), [`federer_2_10_14`](../theories/DiscontinuousCurveLength.v#L79) |
| 2.10.14 | sum_[a,b) alpha_+ + sum_(a,b] alpha_- | numerical jump sums with inward endpoint convention | [`curve_interval_jump_budget`](../theories/CurveJumpBudget.v#L54), [`curve_jump_measure`](../theories/CurveJumpBudget.v#L24) |
| 2.10.15 | g(p) = integral N(p restricted to A,y) dL^m(y) | actual projection-multiplicity integral, including infinite fibres | [`projection_multiplicity_integral`](../theories/ProjectionMultiplicityIntegral.v#L40), [`projection_multiplicity_integral_specification`](../theories/ProjectionMultiplicityIntegral.v#L93) |
| 2.10.15 | I_t^m(A) >= norm_t(g)/beta_t(n,m), equality for t=1 | all-exponent lower bound and iterated-integral formula | [`federer_2_10_15`](../theories/IntegralGeometricMultiplicity.v#L111), [`integral_geometric_multiplicity_one_norm_equality`](../theories/IntegralGeometricMultiplicity.v#L156) |
| 2.10.15 | sum of f_S over H_j | increasing projected-volume partition sums with uniform norm bound | [`projection_partition_volume_sum`](../theories/ProjectionMultiplicityPartitions.v#L31), [`projection_partition_volume_sum_increases`](../theories/ProjectionMultiplicityPartitions.v#L82), [`projection_partition_volume_sum_norm_bound`](../theories/ProjectionMultiplicityPartitions.v#L113) |
| 2.10.16 | v(W) = number of points in A intersect W | actual affine slice count and Crofton integral | [`affine_slice_count`](../theories/AffineSliceCount.v#L21), [`federer_2_10_16_affine`](../theories/AffineParameterMultiplicity.v#L178) |
| 2.10.16 | I_1^{j+m-n}(A intersect Z), gamma_{n,j} | actual ambient slice measure and affine slicing integral | [`affine_integral_geometric_slice`](../theories/AffineGeometricSlice.v#L28), [`federer_2_10_16_affine_slicing`](../theories/IntegralGeometricAffineSlicing.v#L77) |
| 2.10.16 | I_1^m(N(p restricted to A, .)) | projection counting integral on R^k and its invariant average | [`projection_slice_multiplicity_integral`](../theories/IntegralGeometricProjectionSlice.v#L29), [`federer_2_10_16_projections`](../theories/IntegralGeometricProjectionSlicing.v#L33) |
| 2.10.16 | normal Jacobian of a stacked pair of projections | top exterior adjoint norm, identified with the wedge of simple unit normals | [`euclidean_normal_jacobian`](../theories/EuclideanNormalJacobian.v#L25), [`stacked_normal_jacobian_wedge`](../theories/StackedNormalJacobian.v#L48), [`stacked_normal_pair_integral`](../theories/StackedNormalPairIntegral.v#L50) |
| 2.10.17 | B(nu,t,delta) | points of A with the uniform small-generator estimate | [`caratheodory_density_good_set`](../theories/CaratheodoryDensityGoodSets.v#L17), [`caratheodory_density_good_set_bound`](../theories/CaratheodoryDensityGoodSets.v#L45) |
| 2.10.17 | mu(A intersect S)/zeta(S) | separate corrected density quotient: 0/0=0 and positive/0=infinity; other partial domains retained | [`caratheodory_density_divide`](../theories/CaratheodoryDensityQuotient.v#L27), [`caratheodory_density_function`](../theories/CaratheodoryDensityFunction.v#L15) |
| 2.10.17 | subcritical upper-density locus | final-measure zero set under finite approximations and intersection closure | [`caratheodory_density_subcritical_null`](../theories/CaratheodoryDensityLowerBound.v#L25), [`federer_2_10_17_3`](../theories/CaratheodoryDensityLowerBound.v#L85) |
| 2.10.18 | hat S | union of eligible generators meeting S with diameter at most twice diam S | [`diameter_enlargement`](../theories/DiameterEnlargements.v#L17), [`diameter_enlargement_bound`](../theories/DiameterEnlargements.v#L58) |
| 2.10.18 | C lim (mu restricted to A)/zeta | full original-quotient covering limit zero outside A almost everywhere | [`federer_2_10_18_2`](../theories/CaratheodoryZeroDensityLimit.v#L82), [`caratheodory_positive_cost_limits`](../theories/CaratheodoryPositiveCostLimits.v#L21) |
| 2.10.18 | C lim sup (psi restricted to A)/zeta | upper density between zero and one almost everywhere on X for finite psi(A) | [`federer_2_10_18_3`](../theories/CaratheodoryRestrictedDensity.v#L75), [`caratheodory_restricted_upper_density`](../theories/CaratheodoryRestrictedDensity.v#L24) |
| 2.10.19 | $\Theta^{\ast m}(\mu, a)$ | upper $m$ dimensional density | [`upper_metric_density`](../theories/MetricDensities.v#L28) (initial integer degrees) |
| 2.10.19 | $\Theta^m_{\ast}(\mu, a)$ | lower $m$ dimensional density | [`lower_metric_density`](../theories/MetricDensities.v#L35) (initial integer degrees) |
| 2.10.19 | $\Theta^m(\mu, a)$ | $m$ dimensional density | [`metric_density`](../theories/MetricDensities.v#L43), [`metric_density_graph`](../theories/MetricDensities.v#L74) (initial integer degrees) |
| 2.10.20 | $\lim_{r\to\infty}\varphi_\delta(A\cap B(a,r))$ | radial exhaustion of a fixed cutoff | [`unbounded_radius_order_limit`](../theories/RadialMassSupremum.v#L20), [`federer_2_10_20_radial`](../theories/RadialScaleContinuity.v#L43) |
| 2.10.20 | $\lim_j\varphi_\delta(C_j)$ | compact decreasing limit | [`federer_2_10_20_compact_open`](../theories/CompactScaleContinuity.v#L90), [`federer_2_10_20_compact_refinement`](../theories/CompactScaleContinuity.v#L109) |
| 2.10.21 | $E_s$ | functions with Lipschitz bound s | [`metric_lipschitz_functions`](../theories/LipschitzFunctionClosed.v#L40), [`metric_lipschitz_functions_closed`](../theories/LipschitzFunctionClosed.v#L47), [`lipschitz_product_compact_uniform`](../theories/LipschitzProductConvergence.v#L36) |
| 2.10.21 | $\Omega_C$ | distance profile of a nonempty compact set | [`compact_set_distance_profile`](../theories/CompactSetDistanceProfile.v#L25), [`compact_set_distance_profile_specification`](../theories/CompactSetDistanceProfile.v#L31) |
| 2.10.21 | Hausdorff distance | supremum of absolute distance-profile differences | [`is_hausdorff_distance`](../theories/HausdorffDistanceUP.v#L18), [`hausdorff_distance`](../theories/HausdorffDistance.v#L12), [`hausdorff_distance_directed_bound`](../theories/HausdorffDistanceBasic.v#L87) |
| 2.10.21 | $F_{a,r}$ | nonempty compact subsets of B(a,r) | [`compact_sets_in_ball`](../theories/CompactBallProfiles.v#L19), [`compact_hausdorff_ball_compact`](../theories/CompactHausdorffBall.v#L65), [`federer_2_10_21_compact_convex`](../theories/HausdorffFiniteConvexHulls.v#L59) |
| 2.10.22 | $\zeta:F\to[0,\infty)$ | finite nonnegative Hausdorff-continuous compact cost, positive on positive diameters | [`is_continuous_positive_compact_cost`](../theories/CompactGeneratorCostUP.v#L24) |
| 2.10.22 | $\phi_\delta(A_j)\uparrow\phi_\delta(\bigcup_j A_j)$ | fixed-cutoff continuity below for arbitrary increasing targets | [`federer_2_10_22`](../theories/CompactCostContinuityBelow.v#L78) |
| 2.10.22 | $C_{j,k},D_k$ | source and limiting compact cover positions with explicit inactive flags | [`compact_cost_near_optimal_array`](../theories/CompactCostSourceArray.v#L24), [`compact_cost_limit_array`](../theories/CompactCostLimitArray.v#L26), [`masked_compact_set`](../theories/MaskedCompactGenerators.v#L22), [`masked_compact_cost`](../theories/MaskedCompactGenerators.v#L28) |
| 2.10.23 | $\sup\{\psi(C): C\subset S,\ C\text{ compact}\}$ | compact-subset mass supremum for every Suslin S | [`compact_subset_mass_values`](../theories/CompactCostSuslinInner.v#L23), [`federer_2_10_23_supremum`](../theories/CompactCostSuslinInner.v#L31), [`federer_2_10_23`](../theories/CompactCostSuslinInner.v#L58) |
| 2.10.24 | $\lambda_\delta(f)$ | infimum of weighted countable covering costs, finite real coefficients and actual final-measure almost-everywhere domination | [`is_weighted_metric_cover`](../theories/WeightedMetricEnvelopeUP.v#L39), [`is_weighted_metric_envelope`](../theories/WeightedMetricEnvelopeUP.v#L63), [`weighted_metric_envelope`](../theories/WeightedMetricEnvelope.v#L16) |
| 2.10.24 | $\lambda^H_\delta,\lambda^S_\delta$ | original Hausdorff and spherical weighted constructions, integer degrees | [`hausdorff_weighted_sigma_finite_equality`](../theories/HausdorffWeightedSigmaFinite.v#L79), [`spherical_weighted_sigma_finite_equality`](../theories/SphericalWeightedSigmaFinite.v#L24), [`hausdorff_weighted_proper_equality`](../theories/HausdorffProperWeighted.v#L66), [`spherical_weighted_proper_equality`](../theories/SphericalProperWeighted.v#L59) |
| 2.10.24 | $t\zeta(A)\le\sum_j u_j\zeta(S_j)$ | supporting weighted Gross and integral-geometric gauge estimates, countable indexed Borel covers and finite real weights | [`projected_volume_gauge_weighted_cover`](../theories/ProjectedVolumeWeightedCovers.v#L74), [`integral_geometric_gauge_weighted_cover`](../theories/IntegralGeometricWeightedCovers.v#L31) |
| 2.10.24 | $\nu_f(A)$ | auxiliary restricted weighted limit, specified by cutoff supremum laws and sealed independently | [`is_weighted_restriction_measure`](../theories/WeightedRestrictionMeasureUP.v#L29), [`weighted_restriction_measure`](../theories/WeightedRestrictionMeasure.v#L30), [`weighted_restriction_measureE`](../theories/WeightedRestrictionMeasure.v#L48) |
| 2.10.24 | $\lambda^G,\lambda^{I_t}$ | limiting weighted Gross and normalized integral-geometric constructions equal their upper integrals, arbitrary nonnegative extended inputs | [`gross_weighted_integral_equality`](../theories/ProjectedWeightedIntegralEquality.v#L28), [`integral_geometric_weighted_integral_equality`](../theories/ProjectedWeightedIntegralEquality.v#L50) |
| 2.10.24 | $5+5^m$ | auxiliary common control for the closed Hausdorff containing enlargement | [`closed_hausdorff_enlargement_control`](../theories/ClosedHausdorffEnlargementUP.v#L25), [`closed_hausdorff_enlargement_specification`](../theories/ClosedHausdorffEnlargement.v#L23) |
| 2.10.24 | $\lim_{\delta\downarrow0}\lambda_\delta(f)$ | actual positive-cutoff limit, specified first by supremum laws | [`is_weighted_metric_limit`](../theories/WeightedMetricLimitUP.v#L20), [`weighted_metric_limit`](../theories/WeightedMetricLimit.v#L16), [`federer_2_10_24_upper_bound`](../theories/WeightedUpperIntegralBound.v#L65) |
| 2.10.24 | $g_j,h_j,B_j$ | weighted point sum, Borel restriction and increasing conull-support Borel family | [`weighted_generator_sum`](../theories/WeightedMetricEnvelopeUP.v#L22), [`weighted_generator_restriction`](../theories/WeightedGeneratorIntegral.v#L23), [`caratheodory_increasing_borel_generator_bounds`](../theories/CaratheodoryUniformBorelApproximation.v#L54) |
| 2.10.24 | $H_j,v_j$ | finite disjoint layers and residual weights; least-real-weight peeling preserves layer accounting | [`finite_enlarged_disjoint_cover`](../theories/FiniteEnlargedDisjointCover.v#L24), [`finite_weighted_disjoint_layer_bound`](../theories/FiniteDisjointWeightedLayers.v#L71) |
| 2.10.23 | $Z_i,C$ | pruned closed witnesses and compact projection limit | [`continuous_coordinate_pruning`](../theories/ContinuousPruning.v#L15), [`continuous_coordinate_pruning_specification`](../theories/ContinuousPruning.v#L23), [`compact_cost_suslin_bounded_approximation`](../theories/CompactCostSuslinApproximation.v#L27) |
| 2.10.25 | $\mathscr H^k(A\cap f^{-1}\{y\})$ | fibre-mass integrand, without an assumed measurability conclusion | [`hausdorff_fibre_mass`](../theories/HausdorffFibreCutoffs.v#L26), [`federer_2_10_25`](../theories/HausdorffFibreTheorem.v#L24) |
| 2.10.25 | $\phi^k_{1/i}(A\cap f^{-1}\{y\})$ | reciprocal-cutoff approximation, natural index n represents i=n+1 | [`hausdorff_fibre_cutoff`](../theories/HausdorffFibreCutoffs.v#L35), [`hausdorff_fibre_cutoffs_supremum`](../theories/HausdorffFibreCutoffs.v#L97) |
| 2.10.25 | $c=(\operatorname{Lip}f)^m\alpha(k)\alpha(m)/\alpha(k+m)$ | exact normalized bound, natural degrees including zero | [`hausdorff_fibre_bound_constant`](../theories/HausdorffFibreCost.v#L36), [`hausdorff_diameter_cost_product`](../theories/HausdorffFibreCost.v#L73) |
| 2.10.25 | $u_j(T)$ | intermediate grouped source costs; infinite groups removed only on proved null target generators | [`weighted_generator_image_assembly`](../theories/WeightedGeneratorImageAssembly.v#L27) |
| 2.10.26 | $V_j$ | finite open fibre covers, diameter at most 1/j and strict total budget t+1/j | [`is_finite_open_fibre_cover`](../theories/CompactFibreOpenCovers.v#L48), [`fibre_open_cover_locus`](../theories/CompactFibreOpenCovers.v#L61), [`compact_fibre_mass_closed_level_formula`](../theories/CompactFibreMassLevels.v#L55) |
| 2.10.26 | $\mathscr H^k(A\cap f^{-1}\{y\})$ | measurable under the printed proper-source and finite measurable-set hypotheses | [`federer_2_10_26`](../theories/HausdorffFibreMeasurability.v#L91), [`hausdorff_fibre_measurability_proper_source`](../theories/HausdorffFibreMeasurability.v#L30) |
| 2.10.26 | $A=X\subset Y=\mathbb R$ | nonmeasurable inclusion example, H^0 fibre equals the indicator of A | [`subset_inclusion_counting_fibre`](../theories/SubsetInclusionFibreCounterexample.v#L40), [`real_nonmeasurable_inclusion_exists`](../theories/SubsetInclusionFibreCounterexample.v#L115) |
| 2.10.27 | $\{z:(y,z)\in A\}$ | section in an abstract Cartesian metric product | [`metric_product_section`](../theories/MetricCartesianProductUP.v#L52), [`is_metric_cartesian_product`](../theories/MetricCartesianProductUP.v#L23) |
| 2.10.27 | $\alpha(k)\alpha(m)/\alpha(k+m)$ | Hausdorff section coefficient, natural degrees | [`federer_2_10_27_hausdorff`](../theories/HausdorffProductSections.v#L38), [`federer_2_10_27_product_lower_bound`](../theories/HausdorffProductLowerBound.v#L47) |
| 2.10.27 | $\alpha(k)(r^2-\lvert y-u\rvert^2)^{k/2}$ | sealed ball-section profile on the closed base ball | [`is_euclidean_ball_section_profile`](../theories/EuclideanBallSectionProfileUP.v#L23), [`euclidean_ball_section_profile_integral`](../theories/EuclideanBallSectionProfile.v#L49) |
| 2.10.27 | $\int^*\mathscr S^k(A_y)\,d\mathscr L^m(y)\leq\mathscr S^{k+m}(A)$ | sharp spherical section estimate | [`federer_2_10_27_spherical`](../theories/EuclideanSphericalSections.v#L64) |
| 2.10.28 | $h,\zeta,\psi$ | concave interval gauge, diameter cost and generated measure | [`is_concave_interval_gauge`](../theories/ConcaveIntervalGaugeUP.v#L21), [`concave_interval_cost`](../theories/CompactIntervalGauge.v#L39), [`concave_interval_measure`](../theories/ConcaveIntervalMeasure.v#L22) |
| 2.10.28 | $H$ special for $J$ | finite disjoint intervals with conserved cost and whole-member test bounds | [`is_special_interval_family`](../theories/SpecialIntervalFamilyUP.v#L24) |
| 2.10.28 | $\Phi(J,n),s,t$ | equal-cost child family, child length and spacing | [`is_equal_cost_interval_family`](../theories/EqualCostIntervalFamilyUP.v#L25), [`equal_cost_interval_family`](../theories/EqualCostIntervalFamily.v#L17), [`cantor_split_radius`](../theories/CantorSplitRadius.v#L19), [`cantor_split_spacing`](../theories/CantorSplitRadius.v#L49); nondegenerate J |
| 2.10.28 | $H_j,A(m,n),f$ | recursive levels, compact limit and cumulative function | [`is_equal_cost_interval_tree`](../theories/EqualCostIntervalTreeUP.v#L23), [`is_special_interval_tree_limit`](../theories/SpecialIntervalFamilyUP.v#L95), [`is_power_cantor_pair`](../theories/PowerCantorPairUP.v#L22), [`power_cantor_pair_properties`](../theories/PowerCantorPair.v#L54); positive coefficient c explicit |
| 2.10.28 | $\log(2)/\log(3)$ | classical middle-third exponent | [`classical_cantor_exponent`](../theories/ClassicalCantorSplit.v#L19), [`classical_cantor_split_parameters`](../theories/ClassicalCantorSplit.v#L63) |
| 2.10.29 | $n_j,\nu_j,s_j,\sigma_j,t_j,\tau_j$ | interleaved subdivision schedules, widths and spacings | [`is_interleaved_cantor_scales`](../theories/InterleavedCantorScalesUP.v#L59), [`interleaved_cantor_scales`](../theories/InterleavedCantorScales.v#L17), [`interleaved_cantor_scales_interleaving`](../theories/InterleavedCantorScalesLaws.v#L70); corrected last term sigma_j>=t_(j+1) |
| 2.10.29 support | $c(\operatorname{diam}S)^p$ | explicit-coefficient real power gauge | [`metric_real_diameter_cost`](../theories/MetricRealPowerCost.v#L57), [`is_metric_real_power_measure`](../theories/MetricRealPowerMeasureUP.v#L18), [`metric_real_power_measure`](../theories/MetricRealPowerMeasure.v#L18); Gamma normalisation pending |
| 3.1.1 | $Df$ | differential | [`norm_differential`](../theories/NormDifferential.v#L13), [`norm_differential_graph`](../theories/NormDifferential.v#L20) |
| 3.1.1 | $\operatorname{grad} f$ | gradient | [`norm_gradient`](../theories/DifferentialGradient.v#L17), [`norm_gradient_pairing`](../theories/DifferentialGradient.v#L26); finite-dimensional or complete inner-product setting |
| 3.1.1 | $D_i f$ | partial derivative | [`has_norm_partial_derivative`](../theories/NormPartialDerivative.v#L18), [`norm_differential_partial_expansion`](../theories/NormPartialDerivative.v#L46) |
| 3.1.2 | $\operatorname{ap} Df$ | approximate differential | [`approximate_differential`](../theories/ApproximateDifferential.v#L11), [`approximate_differential_graph`](../theories/ApproximateDifferential.v#L17) |
| 3.1.2 | $\operatorname{ap} D_i f$ | approximate partial derivative | [`approximate_partial_derivative`](../theories/ApproximatePartialDerivative.v#L12), [`approximate_partial_derivative_graph`](../theories/ApproximatePartialDerivative.v#L19) |
| 3.1.11 | $D^k f$ | $k$-th differential | [`norm_higher_differential`](../theories/NormHigherDifferential.v#L30) and its exact graph law |
| 3.1.11 | $f^{(k)}$ | $k$-th derivative | [`has_norm_higher_curve_derivative`](../theories/NormHigherCurveDerivativeUP.v#L31) |
| 3.1.11 | $D_\nu f$ | ordered coordinate partial derivative | [`norm_iterated_partial`](../theories/NormIteratedPartial.v#L14) (ordered coordinate sequence) and [`has_norm_iterated_directional`](../theories/NormIteratedDirectionalUP.v#L33) |
| 3.1.11 | $D^\alpha f$ | partial derivative of order $\alpha$ | [`has_norm_multi_partial`](../theories/NormHigherMultiPartialUP.v#L25); [`norm_multi_partial_class_criterion`](../theories/NormMultiPartialClassCriterion.v#L83) |
| 3.1.21 | $\operatorname{Tan}(S, a)$ | tangent cone | [`norm_tangent_cone`](../theories/TangentConeUP.v#L16); closure, scale and unit-direction laws in [`TangentConeBasic.v`](../theories/TangentConeBasic.v), [`TangentConeClosure.v`](../theories/TangentConeClosure.v), [`TangentUnitDirections.v`](../theories/TangentUnitDirections.v) |
| 3.1.21 | $\operatorname{Tan}(S)$ | tangent cones as a subset of $S \times X$ | [`norm_tangent_bundle`](../theories/TangentConeUP.v#L25); [`euclidean_tangent_bundle`](../theories/EuclideanBundleUP.v#L16); [`submanifold_tangent_bundle`](../theories/SubmanifoldTangentBundle.v#L21) |
| 3.1.21 | $\operatorname{Nor}(S, a)$ | normal cone | [`inner_normal_cone`](../theories/NormalConeUP.v#L15); [`inner_normal_cone_closed`](../theories/NormalConeBasic.v#L37); [`inner_normal_cone_convex`](../theories/NormalConeBasic.v#L25) |
| 3.1.21 | $\operatorname{Nor}(S)$ | normal cones as a subset of $S \times X$ | [`inner_normal_bundle`](../theories/NormalConeUP.v#L22); [`euclidean_normal_bundle`](../theories/EuclideanBundleUP.v#L24); [`submanifold_normal_bundle`](../theories/SubmanifoldNormalBundle.v#L21) |
| 3.1.22 | $Df$ | differential relative to a set | [`relative_norm_differential`](../theories/RelativeDifferential.v#L14), with exact graph [`relative_norm_differential_graph`](../theories/RelativeDifferential.v#L22) and tangent-cone domain [`tangent_differential_restriction_domain`](../theories/RelativeDifferentialRestriction.v#L28) |
| 3.2.1 | $J_k f$ | $k$ dimensional Jacobian | [`euclidean_jacobian`](../theories/Jacobian.v#L16), [`euclidean_linear_jacobian`](../theories/EuclideanLinearJacobian.v#L20) |
| 3.2.1 | $\operatorname{ap} J_k f$ | approximate $k$ dimensional Jacobian | [`approximate_jacobian`](../theories/Jacobian.v#L21) |
| 3.2.13 | $\mathbf S^{m-1}$ | unit sphere | [formalised; see section coverage](chapter3/3.2.md) |
| 3.2.13 | $\Gamma(s)$ | gamma function | [formalised; see section coverage](chapter3/3.2.md) |
| 3.2.16 | $\operatorname{Tan}^m(\phi, a)$ | approximate tangent cone | [formalised; see section coverage](chapter3/3.2.md) |
| 3.2.16 | $\mathbf E(a, v, \varepsilon)$ | cone of points near the direction $v$ | [formalised; see section coverage](chapter3/3.2.md) |
| 3.2.16 | $\operatorname{Nor}^m(\phi, a)$ | approximate normal cone | [formalised; see section coverage](chapter3/3.2.md) |
| 3.2.16 | $(\phi, m) \operatorname{ap} Df$ | $(\phi, m)$ approximate differential | [formalised; see section coverage](chapter3/3.2.md) |
| 3.2.20 | $\operatorname{ap} J_m f$ | approximate Jacobian on a rectifiable set | [formalised; see section coverage](chapter3/3.2.md) |
| 3.2.22 | $\operatorname{ap} J_\mu f$ | approximate $\mu$ dimensional Jacobian | [`measure_approximate_jacobian`](../theories/MeasureApproximateJacobian.v#L20); density dimension m and exterior degree mu remain separate. |
| 3.2.28 | $\mathbf{SO}(m)$ | special orthogonal group | not formalised |
| 3.2.37 | $\mathscr M^{\ast m}$ | upper Minkowski content | [formalised; see section coverage](chapter3/3.2.md) |
| 3.2.37 | $\mathscr M^m_{\ast}$ | lower Minkowski content | [formalised; see section coverage](chapter3/3.2.md) |
| 3.2.37 | $\mathscr M^m$ | Minkowski content | [formalised; see section coverage](chapter3/3.2.md) |
| 3.3.1 | $\mathbf X(a, r, V, s)$ | conical set $\{x : s^{-1} \operatorname{dist}(x-a, V) < \lvert x-a \rvert < r\}$ | not formalised |
| 3.4.5 | $\mathscr O_a$ | germs of analytic functions at $a$ | not formalised |
| 3.4.5 | $\gamma_a$ | germ at $a$ | not formalised |
| 3.4.5 | $\operatorname{ideal}$ | ideal of a set germ | not formalised |
| 3.4.5 | $\mathscr V_a$ | analytic variety germs at $a$ | not formalised |
| 3.4.5 | $\operatorname{var}$ | analytic variety of functions or of an ideal | not formalised |
| 3.4.8 | $\operatorname{depth}$ | depth of an ideal | not formalised |
| 3.4.8 | $\dim$ | dimension of an analytic variety germ | not formalised |
| 3.4.12 | $\mathscr O^{\mathbf C}_a$ | germs of complex analytic functions | not formalised |
| 3.4.12 | $\operatorname{ideal}^{\mathbf C}$ | complex ideal of a set germ | not formalised |
| 3.4.12 | $\mathscr V^{\mathbf C}_a$ | complex analytic variety germs | not formalised |
| 3.4.12 | $\mathbf U(n)$ | unitary group | not formalised |
| 3.4.12 | $\dim_{\mathbf C}$ | complex dimension | not formalised |
| 4.1.1 | $\mathscr E$ | functions of class $\infty$ | not formalised |
| 4.1.1 | $\nu^i_K$ | seminorm $\sup$ of $\lVert D^j \phi \rVert$ on $K$ for $j \le i$ | not formalised |
| 4.1.1 | $\mathscr E'$ | continuous linear functionals on $\mathscr E$ | not formalised |
| 4.1.1 | $\operatorname{spt}$ | support of a function or functional | not formalised |
| 4.1.1 | $\mathscr E'_K$ | members of $\mathscr E'$ supported in $K$ | not formalised |
| 4.1.1 | $\mathscr D_K$ | functions of class $\infty$ supported in $K$ | not formalised |
| 4.1.1 | $\mathscr D$ | test functions | not formalised |
| 4.1.1 | $\mathscr D'$ | distributions | not formalised |
| 4.1.1 | $T \mathbin{\llcorner} v$ | product of a distribution and a function | not formalised |
| 4.1.1 | $T D_j$ | $\phi \mapsto T(D_j \phi)$ | not formalised |
| 4.1.1 | $T D^\alpha$ | $\phi \mapsto T(D^\alpha \phi)$ | not formalised |
| 4.1.1 | $D_j T$ | distributional partial derivative | not formalised |
| 4.1.1 | $D^\alpha T$ | distributional partial derivative of order $\alpha$ | not formalised |
| 4.1.1 | $T_x \phi(x)$ | alternative notation for $T(\phi)$ | not formalised |
| 4.1.2 | $\Phi_\varepsilon$ | mollifier | not formalised |
| 4.1.2 | $T_\varepsilon$ | regularised distribution | not formalised |
| 4.1.2 | $\ast$ | convolution | not formalised |
| 4.1.5 | $\lVert S \rVert$ | variation measure of a distribution | not formalised |
| 4.1.6 | $\wedge$ | exterior product of forms and vectorfields | not formalised |
| 4.1.6 | $\mathbin{\lrcorner}$ | interior product of fields | not formalised |
| 4.1.6 | $\mathbin{\llcorner}$ | interior product of fields | not formalised |
| 4.1.6 | $\langle \xi, \phi \rangle$ | pointwise pairing | not formalised |
| 4.1.6 | $\lVert \phi \rVert$ | pointwise comass of a form | not formalised |
| 4.1.6 | $\lVert \xi \rVert$ | pointwise mass of a vectorfield | not formalised |
| 4.1.6 | $X_\lambda$ | product of coordinate covectors | not formalised |
| 4.1.6 | $e_\lambda$ | product of standard base vectors | not formalised |
| 4.1.6 | $(DX)_\lambda$ | product of coordinate differentials | not formalised |
| 4.1.6 | $\mathbf e_\lambda$ | constant $m$-vectorfield | not formalised |
| 4.1.6 | $\mathbf D_p \xi$ | duality applied to a vectorfield | not formalised |
| 4.1.6 | $\mathbf D^p \phi$ | duality applied to a form | not formalised |
| 4.1.6 | $\ast \xi$ | Hodge star of a vectorfield | not formalised |
| 4.1.6 | $\ast \phi$ | Hodge star of a form | not formalised |
| 4.1.6 | $d\phi$ | exterior derivative | not formalised |
| 4.1.6 | $\operatorname{div} \xi$ | divergence | not formalised |
| 4.1.6 | $f^{\#}$ | pull-back of forms | not formalised |
| 4.1.7 | $\mathscr E^m$ | forms of class $\infty$ | not formalised |
| 4.1.7 | $\mathscr E_m$ | currents with compact support | not formalised |
| 4.1.7 | $\mathscr D^m$ | forms with compact support | not formalised |
| 4.1.7 | $\mathscr D_m$ | currents | not formalised |
| 4.1.7 | $T \mathbin{\llcorner} \phi$ | interior product of a current and a form | not formalised |
| 4.1.7 | $T \wedge \xi$ | product of a current and a vectorfield | not formalised |
| 4.1.7 | $\partial T$ | boundary | not formalised |
| 4.1.7 | $\mathbf E^n$ | current $\mathscr L^n \wedge e_1 \wedge \dots \wedge e_n$ | not formalised |
| 4.1.7 | $\vec S$ | orienting $m$-vectorfield | not formalised |
| 4.1.7 | $\mathbf M$ | mass | not formalised |
| 4.1.7 | $\mathbf N$ | normal mass $\mathbf M(T) + \mathbf M(\partial T)$ | not formalised |
| 4.1.7 | $\mathbf N_m$ | normal currents | not formalised |
| 4.1.7 | $\mathbf N^{\mathrm{loc}}_m$ | locally normal currents | not formalised |
| 4.1.7 | $\mathbf N_{m,K}$ | normal currents supported in $K$ | not formalised |
| 4.1.7 | $f_{\#}$ | push-forward of currents | not formalised |
| 4.1.8 | $S \times T$ | Cartesian product of currents | not formalised |
| 4.1.8 | $[u, v]$ | oriented interval | not formalised |
| 4.1.9 | $h_t$ | $h(t, \cdot)$ | not formalised |
| 4.1.9 | $\dot h_t$ | velocity of a homotopy | not formalised |
| 4.1.11 | $S \mathbin{\times\!\!\!\!\times} T$ | join of currents | not formalised |
| 4.1.11 | $[u_0, \dots, u_m]$ | oriented simplex | not formalised |
| 4.1.12 | $\mathbf F_K$ | flat seminorm | not formalised |
| 4.1.12 | $\mathbf F_{m,K}$ | flat chains in $K$ | not formalised |
| 4.1.12 | $\mathbf F_m$ | flat chains | not formalised |
| 4.1.12 | $\mathbf F^{\mathrm{loc}}_m$ | locally flat chains | not formalised |
| 4.1.14 | $f_{\#}$ | push-forward of flat chains | not formalised |
| 4.1.19 | $\mathbf F$ | flat norm of a flat cochain | not formalised |
| 4.1.22 | $\mathscr P_{m,K}$ | integral polyhedral chains in $K$ | not formalised |
| 4.1.22 | $\mathbf P_{m,K}$ | real polyhedral chains in $K$ | not formalised |
| 4.1.22 | $\mathscr P_m$ | integral polyhedral chains | not formalised |
| 4.1.22 | $\mathbf P_m$ | real polyhedral chains | not formalised |
| 4.1.24 | $\mathscr R_{m,K}$ | rectifiable currents in $K$ | not formalised |
| 4.1.24 | $\mathscr R_m$ | rectifiable currents | not formalised |
| 4.1.24 | $\mathbf I_{m,K}$ | integral currents in $K$ | not formalised |
| 4.1.24 | $\mathbf I_m$ | integral currents | not formalised |
| 4.1.24 | $\mathscr F_{m,K}$ | integral flat chains in $K$ | not formalised |
| 4.1.24 | $\mathscr F_m$ | integral flat chains | not formalised |
| 4.1.24 | $\mathscr R^{\mathrm{loc}}_m$ | locally rectifiable currents | not formalised |
| 4.1.24 | $\mathbf I^{\mathrm{loc}}_m$ | locally integral currents | not formalised |
| 4.1.24 | $\mathscr F^{\mathrm{loc}}_m$ | locally integral flat chains | not formalised |
| 4.1.24 | $\mathscr F_K$ | integral flat seminorm | not formalised |
| 4.1.31 | $\int_B \phi$ | integral over an oriented submanifold | not formalised |
| 4.1.31 | $\int_{\partial A} \psi$ | integral over an oriented boundary | not formalised |
| 4.1.34 | $[\alpha, \beta]$ | Lie product of vectorfields | not formalised |
| 4.2.1 | $\langle T, u, r+ \rangle$ | slice of $T$ by $u$ | not formalised |
| 4.2.1 | $\langle T, u, r- \rangle$ | slice of $T$ by $u$ | not formalised |
| 4.2.2 | $f_{\# u}$ | push-forward under a $u$ admissible map | not formalised |
| 4.2.2 | $H_u(f, g)$ | $u$ deformation chain | not formalised |
| 4.2.5 | $\mathbf Z^n_j$ | lattice points with $j$ even coordinates | not formalised |
| 4.2.5 | $\mathbf W'(z)$ | cube of the standard subdivision | not formalised |
| 4.2.5 | $\mathbf W''(z)$ | dual cube | not formalised |
| 4.2.5 | $\mathbf W'_k$ | $k$ dimensional skeleton | not formalised |
| 4.2.5 | $\mathbf W''_k$ | $k$ dimensional dual skeleton | not formalised |
| 4.2.8 | $\boldsymbol\mu_\varepsilon$ | homothety $x \mapsto \varepsilon x$ | not formalised |
| 4.2.26 | $\mathscr F^\nu_K$ | flat seminorm modulo $\nu$ | not formalised |
| 4.2.26 | $\mathscr F^\nu_{m,K}$ | flat chains modulo $\nu$ in $K$ | not formalised |
| 4.2.26 | $T_1 \equiv T_2 \bmod \nu$ | congruence modulo $\nu$ | not formalised |
| 4.2.26 | $\mathscr F^\nu_m$ | flat chains modulo $\nu$ | not formalised |
| 4.2.26 | $\operatorname{spt}^\nu$ | support modulo $\nu$ | not formalised |
| 4.2.26 | $(T)^\nu_K$ | class of $T$ modulo $\nu$ in $K$ | not formalised |
| 4.2.26 | $(T)^\nu$ | class of $T$ modulo $\nu$ | not formalised |
| 4.2.26 | $\mathscr R^\nu_m$ | rectifiable currents modulo $\nu$ | not formalised |
| 4.2.26 | $\mathbf I^\nu_m$ | integral currents modulo $\nu$ | not formalised |
| 4.2.26 | $\mathscr R^\nu_{m,K}$ | rectifiable currents modulo $\nu$ in $K$ | not formalised |
| 4.2.26 | $\mathbf I^\nu_{m,K}$ | integral currents modulo $\nu$ in $K$ | not formalised |
| 4.2.26 | $\mathscr P^\nu_m$ | polyhedral chains modulo $\nu$ | not formalised |
| 4.2.26 | $\mathbf M^\nu$ | mass modulo $\nu$ | not formalised |
| 4.2.26 | $\lVert T \rVert^\nu$ | variation measure modulo $\nu$ | not formalised |
| 4.2.26 | $(T)^\nu \mathbin{\llcorner} A$ | restriction modulo $\nu$ | not formalised |
| 4.2.26 | $\mathbf N^\nu$ | normal mass modulo $\nu$ | not formalised |
| 4.2.26 | $\langle (T)^\nu, u, r+ \rangle$ | slice modulo $\nu$ | not formalised |
| 4.3.1 | $T \mathbin{\llcorner} f^{\#} \phi$ | interior product with a pulled-back form | not formalised |
| 4.3.1 | $\langle T, f, y \rangle$ | slice of $T$ by a map $f$ at $y$ | not formalised |
| 4.3.20 | $S \cap T$ | intersection of currents | not formalised |
| 4.4.1 | $\mathscr Z_m$ | cycles | not formalised |
| 4.4.1 | $\mathscr B_m$ | boundaries | not formalised |
| 4.4.1 | $\mathbf H_m$ | homology groups | not formalised |
| 4.4.1 | $\partial$ | connecting homomorphism | not formalised |
| 4.4.4 | $\mathscr F_{K,B}$ | relative integral flat seminorm | not formalised |
| 4.4.5 | $\mathbf H_m(A, B; \mathbf Z)$ | integral homology groups | not formalised |
| 4.4.6 | $\mathscr Z^\nu_m$ | cycles modulo $\nu$ | not formalised |
| 4.4.6 | $\mathscr B^\nu_m$ | boundaries modulo $\nu$ | not formalised |
| 4.4.6 | $\mathbf H_m(A, B; \mathbf Z_\nu)$ | homology groups modulo $\nu$ | not formalised |
| 4.4.6 | $\mathbf Z_m$ | real cycles | not formalised |
| 4.4.6 | $\mathbf B_m$ | real boundaries | not formalised |
| 4.4.6 | $\mathbf H_m(A, B; \mathbf R)$ | real homology groups | not formalised |
| 4.4.8 | $\tilde{\mathscr Z}_k$ | space of integral cycles in $A$ | not formalised |
| 4.5.5 | $\mathbf n(A, b)$ | exterior normal of $A$ at $b$ | not formalised |
| 4.5.10 | $\operatorname{ess} \mathbf V_\alpha^\beta$ | essential variation | not formalised |
| 5.1.1 | $\int_T \Phi$, $\langle \Phi, T \rangle$ | integral of a parametric integrand over $T$ | not formalised |
| 5.1.1 | $G^{\#} \Psi$ | pull-back of a parametric integrand | not formalised |
| 5.1.2 | $\Phi_a$ | integrand frozen at $a$ | not formalised |
| 5.1.7 | $\delta^{(i)}(T, \Phi, h)$ | $i$-th variation | not formalised |
| 5.1.9 | $\tilde \Phi$ | integrand on $Z \times \operatorname{Hom}(\mathbf R^m, \mathbf R^n)$ | not formalised |
| 5.1.9 | $\tilde \Phi_a$ | $\tilde \Phi$ frozen at $a$ | not formalised |
| 5.1.9 | $\mathbf p$ | projection onto the first $m$ coordinates | not formalised |
| 5.1.9 | $\mathbf q$ | projection onto the last $n-m$ coordinates | not formalised |
| 5.1.9 | $\Phi^{\S}$ | nonparametric integrand | not formalised |
| 5.1.9 | $\Phi^{\S}_a$ | $\Phi^{\S}$ frozen at $a$ | not formalised |
| 5.1.11 | $D_i \phi$ | partial derivative of a nonparametric integrand | not formalised |
| 5.1.11 | $D_{m+j} \phi$ | partial derivative of a nonparametric integrand | not formalised |
| 5.1.11 | $\phi_{(i,j)}$ | partial derivative with respect to an entry | not formalised |
| 5.1.11 | $\phi_{(i,j;k,l)}$ | second partial derivative with respect to entries | not formalised |
| 5.2.1 | $(f, g)_U$ | $\mathbf L_2$ inner product on $U$ | not formalised |
| 5.2.1 | $\lvert f \rvert_U$ | $\mathbf L_2$ norm on $U$ | not formalised |
| 5.2.1 | $(f, g)$ | $\mathbf L_2$ inner product on $\mathbf R^m$ | not formalised |
| 5.2.1 | $\lvert f \rvert$ | $\mathbf L_2$ norm on $\mathbf R^m$ | not formalised |
| 5.2.1 | $(f, g)_{b,r}$ | inner product on the ball $\mathbf U(b,r)$ | not formalised |
| 5.2.1 | $\lvert f \rvert_{b,r}$ | norm on the ball $\mathbf U(b,r)$ | not formalised |
| 5.2.1 | $\mathbf h_\delta(f)$ | Hölder constant with exponent $\delta$ | not formalised |
| 5.2.7 | $\ast$ | convolution with a kernel | not formalised |
| 5.2.10 | $\operatorname{Lap}$ | Laplacian | not formalised |
| 5.2.10 | $\mathbf r$ | $\mathbf r(x) = \lvert x \rvert$ | not formalised |
| 5.2.10 | $\mathbf c(m)$ | constant of the fundamental solution | not formalised |
| 5.3.1 | $\operatorname{Exc}(S, b, r)$ | excess | not formalised |
| 5.3.1 | $\operatorname{Exc}^\nu(S, b, r)$ | excess modulo $\nu$ | not formalised |
| 5.4.1 | $\delta^{(i)}(T, h)$ | $i$-th variation of area | not formalised |
| 5.4.11 | $\exp(T)$ | exponential of an endomorphism | not formalised |
| 5.4.12 | $\mathscr E(B, W)$ | $W$ valued functions of class $\infty$ on $B$ | not formalised |
| 5.4.12 | $\mathfrak T$ | tangent vectorfields of $B$ | not formalised |
| 5.4.12 | $\mathfrak N$ | normal vectorfields of $B$ | not formalised |
| 5.4.12 | $\mathfrak P$ | fields of endomorphisms of tangent spaces | not formalised |
| 5.4.12 | $\nabla_\xi$ | covariant derivative | not formalised |
| 5.4.12 | $[\xi, \eta]$ | Lie bracket | not formalised |
| 5.4.12 | $\nabla_{\xi,\eta}$ | second covariant derivative | not formalised |
| 5.4.12 | $R_{\xi,\eta}$ | curvature | not formalised |
| 5.4.12 | $\operatorname{Lap}$ | Laplace–Beltrami operator | not formalised |
| 5.4.12 | $\nabla \xi$ | covariant differential | not formalised |
| 5.4.12 | $\operatorname{grad} \phi$ | gradient on $B$ | not formalised |

The rectangle relation `{(x,S): x in S in F}` of 2.8.20, p. 152,
with F the compact nondegenerate coordinate rectangles, is
[`euclidean_rectangle_relation`](../theories/EuclideanRectangleCounterexample.v#L31). [`scalar_rectangle_relation`](../theories/ScalarRectangleCounterexample.v#L30) is its
auxiliary scalar-pair presentation; [`federer_2_8_20`](../theories/EuclideanRectangleCounterexample.v#L44) proves failure of
the L² Vitali property in the Euclidean metric.

| Federer | Symbol | Meaning | Rocq |
| --- | --- | --- | --- |
| 2.10.29 | $A(m,n)\times A(m,\nu)$ | actual Euclidean Cantor product | [`euclidean_cantor_product`](../theories/EuclideanCantorProduct.v#L26), [`euclidean_interleaved_cantor_product_infinite`](../theories/EuclideanCantorProduct.v#L34), [`power_cantor_product_cantor_mass`](../theories/PowerCantorProductMeasure.v#L115); every positive target normaliser and 0<=k<m+1 |
| 2.10.29 | $A^q$, $(A\times B)^q$ | actual finite Euclidean set powers | [`euclidean_set_power`](../theories/EuclideanSetPowers.v#L16), [`euclidean_block_set_power`](../theories/EuclideanBlockSetPower.v#L15), [`power_cantor_positive_cartesian_power_bound`](../theories/PowerCantorFinitePowers.v#L29), [`interleaved_cantor_positive_power_infinite`](../theories/InterleavedCantorInfinitePowers.v#L29); [`euclidean_power_regroup_image`](../theories/EuclideanPairPowerShuffle.v#L107) proves the orthogonal regrouping |
| 2.10.30 | $T$ | Steiner symmetrisation of S in a hyperplane | [`is_steiner_symmetrisation`](../theories/SteinerSymmetrisationUP.v#L26), [`steiner_symmetrisation`](../theories/SteinerSymmetrisation.v#L18), [`steiner_normal_line_alternatives`](../theories/SteinerNormalLines.v#L58), [`federer_2_10_30`](../theories/SteinerTheorem.v#L27) |
| 2.10.30 | $\rho_u$ | orthogonal reflection x minus 2(x.u)u | [`normal_reflection`](../theories/UnitNormalGeometry.v#L38), [`normal_reflection_orthogonal`](../theories/UnitNormalGeometry.v#L135), [`steiner_reflection_image`](../theories/SteinerSymmetrisationLaws.v#L72), [`steiner_closed_ball_boundary_exclusion`](../theories/SteinerBoundary.v#L22) |
| 2.10.31 | $C$, $r$ | Hausdorff-closed Steiner-stable compact-set class and minimal centred radius | [`is_steiner_stable_family`](../theories/SteinerStableFamilyUP.v#L29), [`is_compact_enclosing_radius`](../theories/CompactEnclosingRadiusUP.v#L18), [`compact_enclosing_radius`](../theories/CompactEnclosingRadius.v#L18), [`closed_compact_family_minimum_radius`](../theories/CompactFamilyMinimumRadius.v#L25), [`federer_2_10_31`](../theories/SteinerFamilyBallTheorem.v#L56) |
| 2.10.32 | $C$, $\lambda$, $\mu$, $\zeta$ | compact convex volume/cost class and the sharp endpoint exterior-product bound | [`steiner_volume_cost_family`](../theories/SteinerVolumeCostFamilyUP.v#L21), [`steiner_volume_cost_family_closed`](../theories/SteinerVolumeCostFamilyClosed.v#L83), [`steiner_volume_cost_family_stable`](../theories/SteinerVolumeCostFamilyStable.v#L27), [`steiner_volume_cost_threshold_comparison`](../theories/SteinerVolumeCostComparison.v#L24), [`federer_2_10_32`](../theories/EuclideanExteriorVolumeTheorem.v#L57) |
| 2.10.33 | $\alpha(n)2^{-n}(\operatorname{diam}S)^n$ | sharp isodiametric upper bound, including extended diameter and natural degree zero | [`hausdorff_diameter_cost`](../theories/HausdorffDiameterCost.v#L36), [`exterior_diameter_metric_power_bound`](../theories/EuclideanIsodiametric.v#L23), [`federer_2_10_33`](../theories/EuclideanIsodiametric.v#L62) |
| 2.10.34 | $\mathscr G^m\leq\mathscr T^m$ | Gross versus exterior-diameter measure; contraction of their actual generator costs | [`projection_exterior_cost_bound`](../theories/ExteriorProjectionDiameter.v#L69), [`projected_volume_gauge_exterior_bound`](../theories/ProjectedExteriorGaugeBound.v#L19), [`federer_2_10_34`](../theories/GrossExteriorComparison.v#L52) |
| 2.10.35 | $\mathcal L^n=\mathscr S^n=\mathscr H^n=\mathscr T^n=\mathscr Q_t^n=\mathscr I_t^n=\mathscr G^n$, $\beta_t(n,n)=1$ | seven actual measures in ambient dimension; every admissible exponent including infinity | [`federer_2_10_35`](../theories/EuclideanMeasureEqualities.v#L23), [`equal_dimension_projection_beta`](../theories/FullDimensionProjectionNorm.v#L40), [`equal_dimension_integral_geometric_gauge`](../theories/FullDimensionIntegralGauge.v#L23), [`euclidean_lebesgue_density_one`](../theories/EuclideanLebesgueDensity.v#L53) |
| 2.10.36 | $|\bigwedge_i(a_i-b_i)|\leq m!\mathcal L^m(S)$ | factorial endpoint-product bound for convex S; nonempty source in auxiliary degree zero | [`federer_2_10_36`](../theories/ConvexEndpointVolumeBound.v#L145), [`convex_endpoint_volume_bound`](../theories/ConvexEndpointVolumeBound.v#L120), [`euclidean_head_exterior_product_bound`](../theories/EuclideanHeadExteriorBound.v#L42), [`steiner_chord_projection_volume_bound`](../theories/SteinerChordVolumeBound.v#L27) |
| 2.10.37 | $\mathscr T^m\leq\alpha(m)2^{-m}m!\mathscr Q_t^m$ | exterior/convex integral-geometric comparison; the actual probability exponent norm and positive beta | [`federer_2_10_37`](../theories/ExteriorConvexIntegralComparison.v#L56), [`simple_projection_extended_exponent_norm`](../theories/SimpleProjectionExponentNorm.v#L69), [`convex_exterior_cost_integral_gauge_bound`](../theories/ExteriorIntegralGaugeBound.v#L45) |
| 2.10.38 | $Q$, $c_1\geq\cdots\geq c_n$, $a_i,b_i$ | rectangular enclosing box and maximal projected chords; every initial endpoint exterior norm is the corresponding side product | [`is_euclidean_rectangular_box`](../theories/EuclideanBoxUP.v#L19), [`is_greedy_chord_frame`](../theories/GreedyChordFrameUP.v#L48), [`greedy_chord_prefix_norm`](../theories/GreedyChordExteriorProducts.v#L52), [`federer_2_10_38`](../theories/CompactEnclosingBox.v#L52) |
| 2.10.39 | $\mathscr S^m\leq n^{m/2}2^{m-1}\mathscr T^m$ | spherical/exterior comparison; sqrt(n)^m coefficient, all positive natural degrees and arbitrary targets | [`federer_2_10_39`](../theories/SphericalExteriorTheorem.v#L48), [`spherical_exterior_measure_bound`](../theories/SphericalExteriorTheorem.v#L24), [`rectangular_spherical_cutoff_bound`](../theories/RectangularSphericalCover.v#L25), [`euclidean_spherical_above_dimension_zero`](../theories/EuclideanAboveDimensionNull.v#L55) |
| 2.10.40 | $P$, $Y_t$, $c$, $b$, $A$ | compact positive-radius ball parameters, feasible-centre set, least dilation, unique centre and contact centres | [`positive_ball_parameter_family`](../theories/WeightedBallMinimumUP.v#L19), [`weighted_ball_centres`](../theories/WeightedBallMinimumUP.v#L27), [`weighted_ball_feasible_scales`](../theories/WeightedBallMinimumLaws.v#L17), [`is_weighted_ball_minimum`](../theories/WeightedBallMinimumUP.v#L59), [`weighted_ball_contact_centres`](../theories/WeightedBallMinimumUP.v#L37), [`federer_2_10_40`](../theories/WeightedBallMinimumTheorem.v#L20) |
| 2.10.41 | $[2n/(n+1)]^{1/2}$, $c$, $a_i$, $\lambda_i$ | Jung diameter factor, least radius, finite contact centres and nonnegative convex weights | [`jung_factor`](../theories/JungConstant.v#L18), [`is_minimum_enclosing_ball`](../theories/EuclideanMinimumBallUP.v#L18), [`convex_hull_finite_support`](../theories/ConvexHullFiniteSupport.v#L42), [`inner_convex_spherical_pair_identity`](../theories/JungWeightedDistances.v#L35), [`federer_2_10_41`](../theories/JungTheorem.v#L40) |
| 2.10.42 | $\mathscr S^m\leq[2n/(n+1)]^{m/2}\mathscr H^m$ | Jung comparison between actual spherical and Hausdorff measures | [`federer_2_10_42`](../theories/JungSphericalTheorem.v#L24), [`jung_factor`](../theories/JungConstant.v#L18), [`spherical_cutoff_containing_ball_bound`](../theories/SphericalCutoffContainingBall.v#L26), [`jung_spherical_cutoff_generator_bound`](../theories/JungSphericalCutoff.v#L40); natural degrees, real-degree extension pending |
| 2.10.43 | $\operatorname{Lip}(g)=\operatorname{Lip}(f)$, $\Omega$, $P$, $Y_c$ | optimal global Euclidean extension, partial nonexpanding graph class, finite prescribed balls and least common dilation | [`is_kirszbraun_extension`](../theories/KirszbraunExtensionUP.v#L19), [`euclidean_lipschitz_extension`](../theories/KirszbraunExtension.v#L16), [`kirszbraun_ball_parameters`](../theories/KirszbraunBallParameters.v#L18), [`is_metric_nonexpanding_graph`](../theories/NonexpandingGraph.v#L19), [`federer_2_10_43`](../theories/KirszbraunTheorem.v#L22) |
| 2.10.44 | $\mu$, $\nu$, $S$, $f$, $g(\xi)=\inf_{x\in S}(f(x)+\operatorname{Lip}(f)\operatorname{dist}(x,\xi))$ | coordinate supremum source norm, Euclidean target norm, three-point nonextension map and scalar infimum extension | [`plane_supremum_norm`](../theories/PlaneSupremumNorm.v#L15), [`plane_supremum_metric`](../theories/PlaneSupremumNorm.v#L40), [`kirszbraun_corner_source`](../theories/KirszbraunCorners.v#L40), [`kirszbraun_corner_map`](../theories/KirszbraunCornerMap.v#L15), [`is_mcshane_envelope`](../theories/McShaneEnvelopeUP.v#L25), [`federer_2_10_44_scalar_formula`](../theories/McShaneExtensionTheorem.v#L20) |
| 2.10.45 | $\gamma(U)$, $c$, $\xi$, $j(T)$ | Hausdorff slice measure, product multiplier, cube coefficient and positive subdivision count | [`hausdorff_product_slice_measure`](../theories/HausdorffProductSliceMeasure.v#L27), [`euclidean_product_lower_coefficient`](../theories/EuclideanProductCoefficientBounds.v#L26), [`euclidean_product_upper_coefficient`](../theories/EuclideanProductCoefficient.v#L19), [`is_uniform_mesh_count`](../theories/UniformMeshCountUP.v#L18), [`federer_2_10_45`](../theories/HausdorffEuclideanProductTheorem.v#L26) |
| 2.10.46 (partial) | p, q, S times T, sqrt(1+e^2)^m | common projection factors, adapted orthogonal coordinates and ball-product coefficient, with delta=2*r*e | [`euclidean_product_projection_factor`](../theories/EuclideanProductProjectionFactor.v#L20), [`is_orthogonal_projection_chart`](../theories/OrthogonalProjectionChartUP.v#L18), [`ball_product_projected_volume_gauge_bound`](../theories/BallProductProjectedGauge.v#L79), [`gross_finite_product_upper_bound`](../theories/GrossFiniteProductUpper.v#L27) |
| 2.10.46 (partial endpoints) | G^k(V)=0; G^k(V)<infinity | independently proved null products and finite-second-mass upper bound | [`gross_product_null_second_factor`](../theories/GrossProductNullFactor.v#L26), [`gross_product_upper_finite_second`](../theories/GrossProductUpperBound.v#L25) |
| 2.10.46 (partial product formulas) | C^(m+k), G^(m+k), L^m | arbitrary-factor upper bounds; Gross equality for arbitrary factors on the defined-product domain, including all infinite-mass cases | [`caratheodory_projection_product_upper_bound`](../theories/ProjectionProductUpperBounds.v#L22), [`gross_product_upper_bound`](../theories/ProjectionProductUpperBounds.v#L42), [`gross_product_finite_second`](../theories/GrossArbitraryProduct.v#L84), [`gross_arbitrary_first_borel_second_product`](../theories/GrossBorelSecondProduct.v#L26), [`gross_sigma_finite_second_product`](../theories/GrossSigmaFiniteProduct.v#L75), [`gross_product_identity`](../theories/GrossArbitraryInfiniteProduct.v#L106) |
| 2.10.46 (deferred) | $g(F)$, $\lvert F(e_1)\rvert$, $\theta^*\{F:F(e_1)=0\}$, $1\oplus g$ | cylinder projection integral, axis coefficient, exceptional probability and sealed block rotation | [`projection_multiplicity_integral`](../theories/ProjectionMultiplicityIntegral.v#L40), [`line_cylinder_projection_transverse_factor`](../theories/LineCylinderProjectionFactor.v#L29), [`nonzero_vector_projection_kernel_probability_null`](../theories/ProjectionKernelProbability.v#L107), [`euclidean_orthogonal_block_extension`](../theories/EuclideanOrthogonalBlockExtension.v#L22) |
| 2.10.47 | H_j, gamma_i, E_j, B | dyadic cube families, covering contents and nested compact pruning invariant | [`is_dyadic_cube_grid`](../theories/DyadicCubeGridUP.v#L23), [`dyadic_cube_level`](../theories/DyadicCubeGrid.v#L24), [`is_refining_cover_content`](../theories/RefiningCoverContent.v#L25), [`is_compact_content_pruning`](../theories/CompactContentPruning.v#L22); the final dimension induction discharges the intermediate section-nullity premise |
| 2.10.47 | E_j | nested compact sets with common dyadic contents | [`is_dyadic_compact_pruning`](../theories/DyadicPruningUP.v#L17), [`dyadic_compact_pruning_specification`](../theories/DyadicPruning.v#L21) |
| 2.10.47 | H^m(A)>0, 0<H^m(B)<infinity | compact finite-positive subset, with no null-section hypothesis | [`federer_2_10_47`](../theories/HausdorffFinitePositiveSubset.v#L54), [`federer_2_10_47_real_power`](../theories/HausdorffFinitePositiveSubset.v#L24) |
| 2.10.48 | sup{H^m(C): C compact, C subset S, H^m(C)<infinity} | supremum of finite compact masses | [`finite_compact_mass_values`](../theories/FiniteCompactMassUP.v#L16), [`federer_2_10_48`](../theories/HausdorffFiniteCompactInner.v#L70), [`federer_2_10_48_real_power_supremum`](../theories/HausdorffFiniteCompactInner.v#L17) |

## Chapter 3 additions: subsection 3.1 in progress

| Federer item | Printed notation | Formal notation |
| --- | --- | --- |
| 3.1.1, p. 209 | Df(a) | `partial_function_graph (norm_differential hNX hNY A f) a L` specifies exactly when L is the differential; no default value outside its domain. |
| 3.1.1(2), p. 210 | D(g composed with f)(a) | [`norm_differential_chain`](../theories/NormDifferentialChain.v#L43) identifies the candidate as `hom_comp M L` on the actual composite domain. |
| 3.1.1(1), p. 209 | D(f inverse)(f(a)) | [`norm_differential_inverse`](../theories/NormDifferentialInverse.v#L18) identifies the inverse differential from local inverse laws and a linear inverse bound. |
| 3.1.1, pp. 209–210 | norm of L | `norm_operator_norm hNX hNY hL`, with least-bound and closed-unit-ball supremum laws. |
| 3.1.1, p. 209 | grad f(a) | `norm_gradient hspace hf`, with the characterising equation L(v)=B(v,grad f(a)). |
| 3.1.1, p. 209 | infimum over unit directions of the length of Df(a)(v) | [`norm_minimum_modulus`](../theories/NormMinimumModulus.v#L14), [`norm_differential_sharp_limits`](../theories/NormDifferentialSharpLimits.v#L47), [`norm_minimum_inverse`](../theories/NormMinimumInverse.v#L17). |
| 3.1.1, p. 210 | class 0, class 1 | [`norm_class_zero`](../theories/NormClassOneUP.v#L14), [`norm_class_one`](../theories/NormClassOneUP.v#L51). |
| 3.1.1, p. 211 | D_i f(a) | [`has_norm_partial_derivative`](../theories/NormPartialDerivative.v#L18), [`norm_differential_partial_expansion`](../theories/NormPartialDerivative.v#L46). |
| 3.1.1, p. 210 | u_n, inverse-function iteration | [`inverse_function_iteration`](../theories/InverseFunctionIteration.v#L11), [`is_inverse_function_iteration`](../theories/InverseFunctionIterationUP.v#L12); initial value and corrected recurrence through an opaque seal. |
| 3.1.1, p. 210 | D(f inverse)(y) | [`norm_class_one_inverse_field`](../theories/NormClassOneInverse.v#L18); the inverse of Df at the inverse image of y, with continuity proved. |
| 3.1.1(4), p. 210 | Df(a)(v), sum of single-factor replacements | [`norm_differential_multilinear`](../theories/NormDifferentialMultilinear.v#L129) on an abstract finite product specified by [`is_normed_family`](../theories/NormedFamilyUP.v#L17). |
| 3.1.1, p. 211 | Z, continuous linear maps from X to Y | [`is_continuous_operator_space`](../theories/ContinuousOperatorUP.v#L15); [`ContinuousOperatorSealed.v`](../theories/ContinuousOperatorSealed.v) supplies the opaque carrier, evaluation and operator norm. |
| 3.1.1, p. 211 | C_i,j and the intersection-union formula for Df | [`norm_remainder_test`](../theories/NormDifferentialBorelGraph.v#L52), [`norm_differential_graph_countable_formula`](../theories/NormDifferentialBorelGraph.v#L79); both function arguments remain in the actual domain. |
| 3.1.1, p. 211 | dmn Df; Df inverse images of Borel sets | [`norm_differential_domain_borel`](../theories/NormDifferentialBorel.v#L94), [`norm_differential_borel_preimage`](../theories/NormDifferentialBorel.v#L115); Borel sets in the operator space are identified with their evaluation images. |
| 3.1.3(1), pp. 212–213 | S_r, T | [`euclidean_section_ball_mass_measurable`](../theories/EuclideanSectionMassMeasurable.v#L26), [`euclidean_small_section_mass_measurable`](../theories/EuclideanSectionMassMeasurable.v#L68); rational-radius characterization of the universal bound. |
| 3.1.3(2), p. 213 | ap lim sup, ap lim inf in z | [`euclidean_approximate_upper_limit_measurable`](../theories/EuclideanApproximateOrderMeasurable.v#L38), [`euclidean_approximate_lower_limit_measurable`](../theories/EuclideanApproximateOrderMeasurable.v#L74). |
| 3.1.3(3), p. 213 | alpha, beta | linear epimorphism and opaque adapted coordinate chart specified by [`is_euclidean_epimorphism_chart`](../theories/EuclideanEpimorphismChartUP.v#L15). |
| 3.1.3(4), p. 213 | alpha(u,v,z)=(u+z,v); E | [`euclidean_slice_translation`](../theories/EuclideanSliceTranslation.v#L22), [`euclidean_slice_sum`](../theories/EuclideanSliceTranslation.v#L38), [`euclidean_approximate_limit_locus_measurable`](../theories/EuclideanApproximateLimitLocus.v#L23). |
| 3.1.4, p. 214 | A_i, ap D_i f | [`euclidean_approximate_partial_domain_measurable`](../theories/ApproximatePartialMeasurable.v#L16), [`euclidean_approximate_partial_measurable`](../theories/ApproximatePartialMeasurable.v#L33); measurability for Lebesgue measure restricted to the exact derivative domain. |
| 3.1.4, pp. 214–215 | T, Z, B(i,j,p), C(i,j,p,q) | [`coordinate_remainder_exception_set`](../theories/CoordinateRemainderSetMeasurable.v#L31), [`euclidean_slice_variation_exception`](../theories/EuclideanSliceVariationSets.v#L32), [`approximate_partial_uniform_cutoff`](../theories/ApproximatePartialUniformCutoffs.v#L35), [`euclidean_slice_uniform_cutoff`](../theories/EuclideanSliceUniformCutoffs.v#L30); auxiliary closed-radius cutoffs, with the erratum's weak variation threshold. |
| 3.1.4, pp. 214–216 | ap Df(a)(h)=sum_i h_i ap D_i f(a) | [`federer_3_1_4`](../theories/EuclideanApproximateDifferentiability.v#L140); exact sealed graph and coordinate expansion at almost every point of the common partial domain. |
| 3.1.5, p. 216 | C, B, eta, M; L=ap Df(a)=Df(a) | [`federer_3_1_5`](../theories/ApproximateToOrdinaryDifferential.v#L160) preserves the candidate linear map and actual domain B under uniform local control from C. |
| 3.1.6, pp. 216–217 | Df(a), D_i f(a), ap D_i f(a) | [`federer_3_1_6`](../theories/Rademacher.v#L25), [`ordinary_partial_is_approximate`](../theories/OrdinaryApproximatePartial.v#L24), [`euclidean_lipschitz_approximate_partial_conull`](../theories/LipschitzApproximatePartials.v#L91); ordinary differentiability and the coordinate-line bridge. |
| 3.1.7, p. 217 | ap Df(a), ap D_i f(a)=Dg(a)(e_i) | [`federer_3_1_7`](../theories/LipschitzRestrictionDifferentiability.v#L27), [`ordinary_differential_on_density_domain`](../theories/OrdinaryDifferentialOnDensityDomain.v#L25), [`ordinary_partial_on_density_domain`](../theories/OrdinaryPartialOnDensityDomain.v#L23); g is the global Lipschitz extension agreeing on A. |
| 3.1.8, pp. 217–218 | ap lim sup of the growth quotient; Q(u,r,j), B_j, B_(j,k) | [`partial_metric_growth_quotient`](../theories/ApproximateMetricGrowth.v#L21), [`metric_growth_exception`](../theories/ApproximateMetricGrowth.v#L30), [`euclidean_growth_cutoff`](../theories/EuclideanGrowthCutoffs.v#L43), [`euclidean_growth_lipschitz_decomposition`](../theories/ApproximateGrowthDecomposition.v#L26); positive integers use successor indices. |
| 3.1.9, p. 218 | lim sup of the growth quotient; C_j, C_(j,k) | [`metric_local_slope_limsup`](../theories/MetricSlopeLimsup.v#L31), [`metric_local_lipschitz_centers`](../theories/MetricLocalLipschitzCenters.v#L20), [`separable_closed_small_cover_allow_empty`](../theories/MetricClosedSmallCover.v#L18); domain containment is explicit. |
| 3.1.11, pp. 221–223 | F_a, S(p), alpha! | [`is_norm_jet_polynomial`](../theories/NormJetUP.v#L19), [`composition_indices`](../theories/CompositionMultiIndices.v#L41), [`symmetric_multi_factorial`](../theories/SymmetricDividedMonomials.v#L15); see the section account for the coefficient conventions. |
| 3.1.12, pp. 223–224 | S_x, gamma | [`lipschitz_radius_overlap`](../theories/LipschitzRadiusOverlap.v#L19) is the exact closed-ball overlap predicate; [`lipschitz_radius_enclosing_factor`](../theories/LipschitzRadiusOverlap.v#L114) is the printed containing-ball coefficient. |
| 3.1.13, pp. 224–225 | h, S, u_s, sigma, v_s, G_i, V_i | [`federer_cover_radius`](../theories/FedererCoverRadius.v) is h with lambda=1/20; [`is_federer_partition_ball_cover`](../theories/EuclideanPartitionBallCoverUP.v) specifies S; [`euclidean_partition_bump`](../theories/EuclideanPartitionBumps.v) is u_s; [`is_euclidean_partition_family`](../theories/EuclideanPartitionFamilyUP.v) specifies sigma and v_s; [`is_uniform_function_norm`](../theories/UniformFunctionNormUP.v) gives G_i and [`is_partition_derivative_bounds`](../theories/PartitionDerivativeBoundsUP.v) the constants V_i. |
| 3.1.14, pp. 225–226 | P_a, rho(C,delta), xi(s), g, M_i | [`is_whitney_jet_family`](../theories/WhitneyModulusUP.v) specifies the family P_a; [`whitney_modulus`](../theories/WhitneyModulusUP.v) is rho(C,delta) with zero adjoined; [`whitney_nearest_point_exists`](../theories/WhitneyNearestCenters.v) supplies xi(s); [`whitney_extension`](../theories/WhitneyExtensionFunction.v) is g; [`whitney_nearest_constant`](../theories/WhitneyBoundaryEstimate.v) is M_i. |
| 3.1.15, pp. 227–228 | E, eta_q, F, P_a, g | [`top_partial_selection`](../theories/TopDifferentialLusinSelection.v) supplies the Lusin set E; [`uniform_set`](../theories/TopDifferentialUniformSets.v) is {a in E : eta_q(a)<=1/(j+1)}; [`top_differential_good_set`](../theories/TopDifferentialGoodSet.v) supplies F with the derivative T=D D^k f; the (k+1)-jets P_a are the sealed jets of 3.1.11 at the lifted top differential; [`federer_3_1_15`](../theories/LusinClassApproximation.v) supplies g. |
| 3.1.16, p. 228 | C_i, h, g | Compact Lipschitz annular restrictions in [`finite_approximate_growth_annular_compacts`](../theories/ApproximateGrowthAnnularPieces.v#L24); opaque `AnnularLipschitzExtension.value`; the class-one approximation in [`federer_3_1_16`](../theories/ApproximateGrowthClassOneApproximation.v#L112). |
| 3.1.17, p. 229 | finite approximate upper growth; class-one approximation | [`finite_approximate_growth_points`](../theories/ClassOneApproximationUP.v#L19), [`has_class_one_lusin_approximation`](../theories/ClassOneApproximationUP.v#L32); equivalence in [`federer_3_1_17`](../theories/ClassOneApproximationConverse.v#L99) retains the explicit measurable-domain and positive-source qualifications. |

| 3.1.18, pp. 229–230 | rank Df; generic rank v; g,G,psi,h | [`has_linear_rank`](../theories/LinearRankUP.v#L17), [`linear_rank_at_least`](../theories/LinearRankAtLeast.v#L16), [`linear_rank_exteriorP`](../theories/LinearRankExterior.v#L30), [`norm_generic_rank`](../theories/NormRankZero.v#L17); the abstract laws in [`is_euclidean_constant_rank_chart`](../theories/ConstantRankChartUP.v#L59) and existence in [`federer_3_1_18`](../theories/ConstantRankTheorem.v#L52). [`norm_section_shear`](../theories/NormSectionShearUP.v#L14) and [`norm_section_shear_inverse`](../theories/NormSectionShearUP.v#L19) are the displayed target maps. |

| 3.1.19, p. 231 | B; mu; sigma; Z; phi,psi; retraction | [`is_euclidean_submanifold`](../theories/EuclideanSubmanifoldUP.v#L52), [`is_submanifold_straightening`](../theories/EuclideanSubmanifoldUP.v#L33), [`has_regular_level_charts`](../theories/SubmanifoldChartsUP.v#L29), [`has_open_constant_rank_parametrisations`](../theories/SubmanifoldChartsUP.v#L41), [`has_convex_coordinate_charts`](../theories/SubmanifoldChartsUP.v#L54), [`has_orthogonal_graph_charts`](../theories/SubmanifoldChartsUP.v#L67); equivalences in [`federer_3_1_19`](../theories/SubmanifoldEquivalences.v#L18), actual coordinate maps in [`norm_coordinate_homeomorphism`](../theories/NormCoordinateTopology.v#L102), retractions in [`RetractionUP.v`](../theories/RetractionUP.v). |

| 3.1.20, pp. 232–233 | P_i,Q_i; W_i,f_i; A=liminf W_i; mu,G | [`is_retraction_patch_family`](../theories/RetractionPatchingUP.v#L16), [`is_retraction_patching_sequence`](../theories/RetractionPatchingUP.v#L73), [`eventual_open_domain`](../theories/StationaryRetractionUP.v#L14), [`connected_retraction_generic_rank`](../theories/RetractionMaximalRank.v#L24), [`federer_3_1_20`](../theories/NeighbourhoodRetractionTheorem.v#L16). Intermediate maps satisfy the corrected [`is_partial_neighbourhood_retraction`](../theories/LocalRetractionUP.v#L15); only the final A contains all of B. |

| 3.1.22, pp. 235–236 | L=Dg(a) restricted to Tan(S,a); eta; D(f composed with psi) | [`is_tangent_differential_restriction`](../theories/RelativeDifferentialUP.v#L17), [`has_relative_first_order_approximation`](../theories/RelativeDifferentialUP.v#L56), [`is_parametric_differential_restriction`](../theories/ParametricDifferentialUP.v#L15); erratum-corrected base value and exact coordinate transport. |

| 3.1.23, pp. 236–237 | A=b+Tan(B,b); u; F; t,r | [`is_controlled_tangent_straightening`](../theories/SupportedStraighteningUP.v#L17), [`is_scaled_annular_cutoff`](../theories/ScaledCutoffUP.v#L15), [`federer_3_1_23`](../theories/SubmanifoldSupportedStraightening.v#L23); target membership is Tan(B,b)(F(x)-b), with both Lipschitz bounds 1/t and identity for |x-b|>=r. |

| 3.1.24, pp. 237–239 | analytic at a; c^m m!; p_m | [`norm_analytic_at`](../theories/NormAnalyticUP.v#L28), [`norm_diagonal_analytic_at`](../theories/NormAnalyticUP.v#L39), [`norm_taylor_analytic_at`](../theories/NormAnalyticUP.v#L52), [`norm_polynomial_analytic_at`](../theories/NormAnalyticUP.v#L65); equivalence in [`norm_analytic_equivalences`](../theories/NormAnalyticEquivalences.v#L17). Actual neighbourhoods and degree-zero coefficients are explicit. |

| 3.1.24, p. 240 | W, all jets zero | [`norm_zero_jet_set`](../theories/NormAnalyticZeroJetSet.v#L21), [`norm_analytic_zero_jets_open`](../theories/NormAnalyticZeroJetSet.v#L44), [`norm_analytic_zero_jets_relative_closed`](../theories/NormAnalyticZeroJetSet.v#L100). |
| 3.1.24, pp. 240–241 | D^alpha f(a), analytic series coefficient | [`euclidean_analytic_coordinate_series`](../theories/EuclideanAnalyticCoordinateSeries.v#L25), using the exact [`has_norm_multi_partial`](../theories/NormHigherMultiPartialUP.v#L25) graph. |

| 3.1.24, pp. 239–240 | beta, gamma; lambda_p; T(p) | [`is_inverse_majorant_sequence`](../theories/InverseMajorantUP.v#L33) specifies the initial value and recurrence; [`inverse_majorant_remainder`](../theories/InverseMajorantUP.v#L19) uses the equivalent degree-greater-than-one filter on S(p); opaque `InverseMajorant.sequence` has the proved exponential bound. |
| 3.1.24, p. 240 | analytic submanifold; analytic sigma, phi, psi | [`is_euclidean_analytic_submanifold`](../theories/AnalyticSubmanifoldUP.v#L30) and the four predicates in [`AnalyticSubmanifoldChartsUP.v`](../theories/AnalyticSubmanifoldChartsUP.v), equivalent by [`federer_3_1_19_analytic`](../theories/AnalyticSubmanifoldEquivalences.v#L17). |

| 3.2.1, p. 241 | J_k f; ap J_k f; exterior degree k | [`euclidean_jacobian`](../theories/Jacobian.v#L16), [`approximate_jacobian`](../theories/Jacobian.v#L21), [`euclidean_linear_jacobian`](../theories/EuclideanLinearJacobian.v#L20); degree k is unrestricted in nat and both numerical functions have exactly their differential domains. |

| 3.2.2, p. 242 | G; E; s; Z(s,i); lambda,epsilon | [`is_injective_differential_cover`](../theories/InjectiveDifferentialPieceUP.v#L58), [`is_injective_differential_piece`](../theories/InjectiveDifferentialPieceUP.v#L28), [`linear_model_locus`](../theories/LinearModelLocus.v#L20); positive i is represented by i+1, with the full closed-ball remainder condition. |

| 3.2.3, pp. 243–244 | integral of J_m f; N(f restricted to A,y); sum over f inverse of y | [`euclidean_jacobian_measure`](../theories/JacobianDensityMeasure.v#L29), [`mapping_multiplicity`](../theories/MappingMultiplicity.v#L23), [`partial_fibre_numerical_sum`](../theories/PartialFibreNumericalSum.v#L17); both area identities and exact signed-sum graph are proved. |

| 3.2.4, p. 244 | B; {x:J_m f(x)>0}; f(A) minus f(B) | [`positive_euclidean_jacobian_locus`](../theories/BorelAreaSelection.v#L22), [`federer_3_2_4`](../theories/BorelAreaSelection.v#L98); the Borel univalent selection preserves the image up to a Hausdorff-null deficit. |

| 3.2.5, pp. 244–245 | integral over A of (g composed with f) J_m f; integral of g(y) N(f restricted to A,y) | [`area_transform_source_integrand`](../theories/AreaTransformIntegrands.v#L18), [`area_transform_target_integrand`](../theories/AreaTransformIntegrands.v#L30), [`federer_3_2_5`](../theories/AreaIntegralTransformation.v#L61); finite real weights, actual partial Jacobian and the distinguished zero-infinity product. |

| 3.2.6, pp. 245–246 | absolute speed; A_1,A_2,A_3; integral from f(a) to f(b) | [`euclidean_curve_speed`](../theories/EuclideanCurveSpeedMeasure.v#L29), [`scalar_positive_derivative_set`](../theories/ScalarCurveDerivativeLoci.v#L70), [`scalar_negative_derivative_set`](../theories/ScalarCurveDerivativeLoci.v#L75), [`scalar_nonsigned_derivative_remainder`](../theories/ScalarCurveDerivativeLoci.v#L81), [`is_measure_oriented_real_interval_integral`](../theories/OrientedRealIntervalIntegral.v#L23); actual derivatives and both endpoint orientations, including equality. |

| 3.2.7, p. 246 | sin; f(x)=abs(x)^(3/2) sin(1/x); g(y)=abs(y)^(-1/2) | Opaque `RealTrigonometry.sine`; [`oscillatory_substitution_curve`](../theories/OscillatorySubstitutionCurve.v#L20); [`is_reciprocal_root_weight`](../theories/ReciprocalRootWeightUP.v#L17); exact real powers expressed by square roots, with g(0)=0 completing the omitted value. |

| 3.2.8, p. 247 | C={x:v(u(x))=x}; Dv(u(x)) composed with Du(x)=identity | [`federer_3_2_8`](../theories/LipschitzLeftInverseDifferentials.v#L62) uses the opaque [`norm_differential`](../theories/NormDifferential.v#L13) graphs and the actual identity linear map; both differential-existence assertions are explicit. |

| 3.2.9, p. 247 | U_lambda=(f,p_lambda); A_lambda; p in O*(m,m-n); G | [`coordinate_stack_map`](../theories/CoordinateStackLocus.v#L26), [`injective_differential_locus`](../theories/InjectiveDifferentialPieceUP.v#L18), [`is_coordinate_inverse_piece`](../theories/CoordinateInverseCoverUP.v#L34), [`is_coordinate_inverse_cover`](../theories/CoordinateInverseCoverUP.v#L51); Cartesian targets use the canonical isometric block coordinates. |

| 3.2.10, p. 248 | v_y(z)=v(y,z); J_n f; J_(m-n) v_y; H^(m-n)(B intersect f inverse y) | [`euclidean_slice_differential`](../theories/EuclideanSliceDifferentials.v#L70), [`extended_euclidean_target_jacobian`](../theories/EuclideanTargetJacobianMeasurable.v#L59), [`is_euclidean_slice_jacobian_representative`](../theories/EuclideanSliceJacobianRepresentative.v#L62), [`coordinate_slice_area_integral_almost`](../theories/CoordinateSliceAreaAlmost.v#L23), [`federer_3_2_10`](../theories/CoordinateCoarea.v#L24); exact fibre sets use [`mapping_fibre`](../theories/MappingMultiplicity.v#L16). |

| 3.2.11, pp. 248–249 | J_n f; H^(m-n)(A intersect f inverse y); g(x,z)=f(x)+epsilon z; Q=A times B(0,1) | [`extended_euclidean_target_jacobian`](../theories/EuclideanTargetJacobianMeasurable.v#L59), [`euclidean_coarea_measure`](../theories/CoareaJacobianMeasure.v#L29), [`mapping_fibre`](../theories/MappingMultiplicity.v#L16), [`coarea_perturbation_map`](../theories/CoareaPerturbationMap.v#L19), [`coarea_cylinder`](../theories/CoareaCylinderFibres.v#L19), [`critical_target_differential_locus`](../theories/CoareaRankLoci.v#L21), [`federer_3_2_11`](../theories/EuclideanCoareaFormula.v#L46); the slicing coefficient is `hausdorff_fibre_bound_constant (m-n) n 1`. |

| 3.2.12, pp. 249–250 | integral on f inverse {y} of g dH^(m-n); g J_n f | [`coarea_fibre_integral`](../theories/CoareaFibreIntegral.v#L20), [`coarea_fibre_integral_graph`](../theories/CoareaFibreIntegral.v#L30), [`partial_density_product`](../theories/PartialDensityProduct.v#L16), [`extended_euclidean_target_jacobian`](../theories/EuclideanTargetJacobianMeasurable.v#L59), [`federer_3_2_12`](../theories/EuclideanWeightedCoarea.v#L57); each inner value exists exactly where that actual subset integral exists. |

| 3.2.13, p. 250 | S^(m-1), H^(m-1)(S^(m-1)), r^(m-1) sphere integrals | [`euclidean_unit_sphere_set`](../theories/UnitSphereSpace.v#L18), [`unit_sphere_hausdorff_measure`](../theories/UnitSphereSpace.v#L67), [`unit_sphere_dilation_integral`](../theories/PolarUnitSphereIntegral.v#L25), [`weighted_unit_sphere_integral`](../theories/PolarUnitSphereIntegral.v#L48), [`hausdorff_unit_sphere_mass`](../theories/HausdorffUnitSphereMass.v#L27). |
| 3.2.13, pp. 250–251 | Gamma(s), B(z), product Gamma(z_j) | [`euler_gamma`](../theories/EulerGamma.v#L27), [`is_euler_gamma`](../theories/EulerGammaUP.v#L27), [`euler_beta`](../theories/EulerBeta.v#L17), [`is_euler_beta`](../theories/EulerBetaUP.v#L16), [`gamma_product_euler_beta`](../theories/EulerBetaGammaFormula.v#L28); getters require the proved positive parameter domains. |
| 3.2.13, p. 251 | alpha(m); sphere coordinate moments | [`euclidean_unit_ball_gamma_volume`](../theories/UnitBallGammaVolume.v#L47), [`hausdorff_unit_sphere_coordinate_moment`](../theories/SphereCoordinateMoment.v#L30), [`unit_sphere_coordinate_power`](../theories/UnitSphereCoordinatePower.v#L19); the full range t>-1 is retained. |
| 3.2.13, p. 251 | beta_t(n,m)^t and beta_1(n,m); Gamma((j+1)/2), Gamma((t+j+1)/2) | [`projection_beta_gamma_product`](../theories/ProjectionBetaGammaProduct.v#L77), [`projection_beta_first_gamma_formula`](../theories/ProjectionBetaFirstGamma.v#L17), [`gamma_half_sequence`](../theories/GammaHalfSequences.v#L24), [`gamma_shifted_half_sequence`](../theories/GammaHalfSequences.v#L30); offset j corresponds to printed dimension m+j+1. |

| 3.2.14, pp. 251–252 | m rectifiable; countably m rectifiable; countably (phi,m) rectifiable; (phi,m) rectifiable | [`is_m_rectifiable`](../theories/RectifiableSetUP.v#L20), [`is_countably_m_rectifiable`](../theories/RectifiableSetUP.v#L32), [`is_countably_measure_m_rectifiable`](../theories/RectifiableSetUP.v#L39), [`is_measure_m_rectifiable`](../theories/RectifiableSetUP.v#L46); zero rectifiable means finite and countably zero rectifiable is equivalent to countability. |
| 3.2.14, p. 252 | purely (phi,m) unrectifiable; countably m rectifiable Borel B with A minus B pure | [`is_purely_measure_m_unrectifiable`](../theories/RectifiableSetUP.v#L53), [`rectifiable_pure_borel_decomposition`](../theories/RectifiablePureDecomposition.v#L26); no measurability of A or extra containment of B is imposed. |

| 3.2.15, p. 252 | f inverse {y}; P={x:im Df(x)=R^n}; countably (H^(m-n),m-n) rectifiable | [`mapping_fibre`](../theories/MappingMultiplicity.v#L16), [`surjective_differential_locus`](../theories/CoordinateInverseCoverUP.v#L20), [`is_countably_measure_m_rectifiable`](../theories/RectifiableSetUP.v#L39), [`federer_3_2_15`](../theories/LipschitzFibreRectifiability.v#L24); full-rank fibre parametrization for every y and null complementary fibre for almost every y. |

| 3.2.16, pp. 252–253 | Tan_m(phi,a); E(a,v,e); Nor_m(phi,a) | [`measure_approximate_tangent_cone`](../theories/MeasureApproximateTangentUP.v#L24), [`approximate_direction_cone`](../theories/MeasureApproximateTangentUP.v#L37), [`measure_approximate_normal_cone`](../theories/MeasureApproximateNormalUP.v#L22); density uses alpha(m)r^m. |
| 3.2.16, p. 253 | (phi,m) ap Df(a); eta; S_i; delta_i; T | [`measure_approximate_differential`](../theories/MeasureApproximateDifferential.v#L19), [`measure_affine_approximation_set`](../theories/MeasureApproximateAffineUP.v#L20), [`measure_affine_annular_good_sets`](../theories/MeasureAffineAnnularApproximation.v#L25), [`is_shrinking_radius_selection`](../theories/ShrinkingRadiusSelectionUP.v#L17), [`is_norm_annular_set`](../theories/NormAnnularSetUP.v#L15), [`norm_annular_corrected_set`](../theories/NormAnnularOmissionDensity.v#L54); exact partial graph, i=n+1 and the erratum's centre qualification. |

| 3.2.17, pp. 254–255 | lambda^(-2m), lambda^(2m); Tan_m(H^m restricted psi(K),psi(a)); im Dpsi(a); D[F restricted psi(K)] composed with Dpsi(a) | [`is_metric_bilipschitz_bound`](../theories/MetricBiLipschitzUP.v#L19), [`euclidean_bilipschitz_lower_density`](../theories/EuclideanBiLipschitzLowerDensity.v#L25), [`euclidean_bilipschitz_upper_density`](../theories/EuclideanBiLipschitzUpperDensity.v#L22), [`euclidean_bilipschitz_tangent_planes`](../theories/EuclideanBiLipschitzTangentPlanes.v#L25), [`euclidean_bilipschitz_relative_composite`](../theories/EuclideanBiLipschitzRelativeComposite.v#L29); the last identity uses [`partial_function_precompose`](../theories/PartialFunctionPrecomposition.v#L14) and an exact total composite differential. |

| 3.2.18, p. 255 | K_i, psi_i; lambda^(-1) norm(v) <= norm(Dpsi_i(a)v) <= lambda norm(v); disjoint images covering W up to H^m null mass | [`is_uniform_compact_rectifiable_chart`](../theories/RectifiableCompactChartsUP.v#L21), [`is_rectifiable_chart_piece`](../theories/RectifiableCompactChartsUP.v#L60), [`is_rectifiable_compact_chart_cover`](../theories/RectifiableCompactChartsUP.v#L71), [`federer_3_2_18`](../theories/RectifiableCompactCharts.v#L23); inverse bounds apply only on each actual compact image. |

| 3.2.19, p. 256 | Theta^m(H^m restricted W,w)=1; Tan_m(H^m restricted W,w); ap Df(w); ap Df composed with Dpsi | [`federer_3_2_19`](../theories/RectifiableDensityTangent.v#L76), [`is_m_dimensional_approximate_tangent`](../theories/RectifiableTangentPlaneUP.v#L17), [`is_rectifiable_differential_chart_point`](../theories/RectifiableDifferentialChartUP.v#L22), [`rectifiable_lipschitz_partial_approximate_differential`](../theories/RectifiableDensityTangent.v#L25); equality with a Grassmann m-plane and an exact partial chain rule. |

| 3.2.20, pp. 256–257 | ap J_m f = norm of exterior^m ap Df; N(f,z); integral_W (g composed f) ap J_m f = integral g N(f,.) | [`measure_approximate_jacobian`](../theories/MeasureApproximateJacobian.v#L20), [`is_partial_exterior_norm`](../theories/PartialExteriorNormUP.v#L39), [`partial_mapping_multiplicity`](../theories/PartialMappingMultiplicity.v#L25), [`rectifiable_area_source_integrand`](../theories/RectifiableAreaIntegrands.v#L20), [`rectifiable_area_target_integrand`](../theories/RectifiableAreaIntegrands.v#L32), [`federer_3_2_20`](../theories/RectifiableAreaFormula.v#L115); g is extended-real and f keeps exactly domain W. |

| 3.2.21, p. 257 | dim im Dv(x)<mu on v inverse T; positive restricted exterior power; corrected L^mu(B) | [`federer_3_2_21`](../theories/PureUnrectifiableRank.v#L55), [`linear_rank_at_least`](../theories/LinearRankAtLeast.v#L16), [`positive_restricted_differential_locus`](../theories/PositiveRestrictedDifferentialLocus.v#L22), [`euclidean_block_null_sections`](../theories/EuclideanBlockNullSections.v#L25). |

| 3.2.22, pp. 258–260 | ap J_mu f; P_ij; A_ij; source R; target Q; integral on the actual f inverse z | [`measure_approximate_jacobian`](../theories/MeasureApproximateJacobian.v#L20), [`rectifiable_chart_pair_piece`](../theories/RectifiableChartPairPieces.v#L26), [`rectifiable_chart_pair_parameters`](../theories/RectifiableChartPairPieces.v#L17), [`rectifiable_coarea_source_integrand`](../theories/RectifiableCoareaIntegrands.v#L22), [`rectifiable_coarea_fibre_integral`](../theories/RectifiableCoareaIntegrands.v#L37), [`is_rectifiable_coarea`](../theories/RectifiableCoareaUP.v#L20); the original domain and both erratum remainders remain explicit. |

| 3.2.23, p. 260 | W times Z; H^(m+mu) restricted to W times Z; product of restricted H^m and H^mu; J_(m+mu)(D(f times g)) | [`euclidean_cartesian_set`](../theories/EuclideanCartesianMap.v#L18), `rectifiable_cartesian_measure_law`, [`euclidean_cartesian_map`](../theories/EuclideanCartesianMap.v#L25), [`euclidean_cartesian_linear_jacobian`](../theories/EuclideanCartesianLinear.v#L94); actual block identification and full measure equality. |

| 3.2.24, p. 260 | H^m(W)=H^mu(Z)=0; H^(m+mu)(W times Z)=infinity | [`is_rectifiable_cartesian_counterexample`](../theories/RectifiableCartesianCounterexampleUP.v#L18), [`federer_3_2_24`](../theories/RectifiableCartesianCounterexample.v#L28), [`natural_real_power_measure_agreement`](../theories/NaturalRealPowerMeasureAgreement.v#L18); fourth Cantor powers, m=mu=2, ambient R^4 factors. |

| 3.2.25, p. 261 | eta; S(w); T(w)=S(w) divided by its norm; associated m-dimensional subspace | [`euclidean_differential_top_word`](../theories/EuclideanDifferentialOrientation.v#L21), [`euclidean_differential_orientation`](../theories/EuclideanDifferentialOrientationContinuity.v#L68), [`is_rectifiable_measurable_orientation`](../theories/RectifiableOrientationUP.v#L21), `rectifiable_orientation_unit_simple`, `rectifiable_orientation_tangent`; literal empty word at degree zero and no outside value in the final partial field. |

| 3.2.26, pp. 261–262 | S^m(W)=H^m(W)=T^m(W)=G^m(W)=Q_t^m(W)=I_t^m(W); zeta_t; beta_t; g_S(p) | [`federer_3_2_26`](../theories/RectifiableGeometricMeasureEquality.v#L29), [`orthogonal_unit_disc_integral_geometric_gauge`](../theories/OrthogonalDiscGeometricGauge.v#L98), [`projection_area_jacobian_integral`](../theories/ProjectionAreaJacobianIntegral.v#L57), [`rectifiable_orientation_piece_norm_lower`](../theories/RectifiableOrientationPieceNorm.v#L32); actual unit-disc and multiplicity norms, corrected displacement x-w, and every exponent 1<=t<=infinity. |

| 3.2.27, pp. 262–263 | a_lambda; Xi; Xi_lambda; sqrt(sum a_lambda squared)<=H^m(W)<=sum a_lambda | [`is_rectifiable_coordinate_masses`](../theories/RectifiableCoordinateMassUP.v#L23), [`is_orthonormal_coordinate_modulus`](../theories/OrthonormalCoordinateModulus.v#L21), [`inner_unit_field_coordinate_integrals`](../theories/InnerCoordinateUnitFieldIntegrals.v#L29), [`federer_3_2_27`](../theories/RectifiableCoordinateProjectionBounds.v#L108); the upper bound requires the documented Hausdorff-measurability correction, while [`rectifiable_coordinate_projection_lower`](../theories/RectifiableCoordinateLower.v#L30) keeps arbitrary-source scope when the actual displayed integrals exist. |

| 3.2.28, pp. 263–267 | Y_m; P(g)=g* g; O(n,m); d=m(2n-m-1)/2 | [`euclidean_symmetric_gram`](../theories/EuclideanSymmetricGram.v#L25), [`euclidean_gram_differential`](../theories/EuclideanGramDifferentialAlgebra.v#L90), [`euclidean_stiefel_smooth_submanifold`](../theories/EuclideanStiefelSmooth.v#L24), [`euclidean_stiefel_tangent`](../theories/EuclideanStiefelTangent.v#L24) |
| 3.2.28(2), pp. 264–265 | Q(g)=Lambda^m g; Z(g); Go(n,m); r=m(n-m); SO(m) | [`euclidean_exterior_word_map`](../theories/EuclideanExteriorWordSmooth.v#L38), [`euclidean_exterior_horizontal_increment`](../theories/EuclideanExteriorHorizontalIncrement.v#L72), [`euclidean_exterior_partial_jacobian_one`](../theories/EuclideanExteriorPartialJacobian.v#L25), [`euclidean_special_orthogonal_half_measure`](../theories/EuclideanSpecialOrthogonalMeasure.v#L58), [`euclidean_oriented_grassmann_volume`](../theories/EuclideanManifoldVolumes.v#L31) |
| 3.2.28(3), pp. 265–266 | S(g)=g alpha; J_q S=(sqrt 2)^(-(m-1)); a_ij, b_ij, c_ij, d_ij | [`euclidean_frame_restriction`](../theories/EuclideanFrameRestriction.v#L25), [`euclidean_stiefel_adapted_direction`](../theories/EuclideanStiefelAdaptedBasis.v#L76), [`euclidean_forgetful_tangent_jacobian`](../theories/EuclideanForgetfulTangentJacobian.v#L23), [`euclidean_forgetful_fibre_measure`](../theories/EuclideanForgetfulFibreMeasure.v#L22), [`euclidean_stiefel_volume_recurrence`](../theories/EuclideanStiefelVolumeRecurrence.v#L22) |
| 3.2.28(4), pp. 266–267 | T(x)=x^2/2; DT(x)h=xh; G(n,m) | [`inner_projective_square`](../theories/SymmetricSquareGeometry.v#L19), [`inner_projective_square_actual_tangent_isometry`](../theories/SymmetricSquareTangentIsometry.v#L48), [`inner_projective_square_manifold_area`](../theories/SymmetricSquareManifoldArea.v#L27), [`euclidean_grassmann_square_set`](../theories/EuclideanGrassmannSquare.v#L23), [`euclidean_grassmann_volume`](../theories/EuclideanManifoldVolumes.v#L39) |
| 3.2.28(5), p. 267 | Gamma(1/2); product Gamma((n-j+1)/2); closed Stiefel and Grassmann volumes | [`stiefel_gamma_product`](../theories/StiefelGammaProduct.v#L34), [`stiefel_gamma_volume_scalar`](../theories/StiefelGammaVolumeScalar.v#L18), [`grassmann_gamma_volume_scalar`](../theories/GrassmannGammaVolumeScalar.v#L18), [`euclidean_stiefel_gamma_volume`](../theories/EuclideanStiefelGammaVolume.v#L20), [`euclidean_grassmann_gamma_volume`](../theories/EuclideanGrassmannGammaVolume.v#L21); actual positive Euler Gamma values, with the Grassmann numerator indexed in reverse order. |

| 3.2.29, pp. 267–268 | countable (H^m,m) rectifiability; countable class-one manifold family | [`is_countably_measure_m_rectifiable`](../theories/RectifiableSetUP.v#L39), [`is_countable_submanifold_measure_cover`](../theories/RectifiableManifoldCoverUP.v#L17), [`has_countable_submanifold_measure_cover`](../theories/RectifiableManifoldCoverUP.v#L39), [`federer_3_2_29`](../theories/RectifiableManifoldCharacterisation.v#L21) |
| 3.2.29, p. 268 | C={f=F}; P={rank Df=m}; uncovered image | [`lipschitz_class_one_small_disagreement`](../theories/LipschitzClassOneApproximation.v#L24), [`full_rank_countable_manifold_images`](../theories/FullRankManifoldImages.v#L19), [`agreement_image_cover_remainder`](../theories/ManifoldCoverImageRemainder.v#L18), [`lipschitz_small_manifold_remainder`](../theories/LipschitzSmallManifoldRemainder.v#L25); only valid error-image containment is asserted. |

| 3.2.30, p. 268 | T^k(L(A)); norm(Lambda^k L); n^(k/2) 2^(k-1) | [`exterior_diameter_measure`](../theories/ExteriorMeasure.v#L19), [`euclidean_linear_jacobian`](../theories/EuclideanLinearJacobian.v#L20), [`linear_exterior_measure_image_bound`](../theories/LinearExteriorMeasureImage.v#L53), [`linear_hausdorff_measure_exterior_bound`](../theories/LinearHausdorffMeasureImage.v#L22), [`federer_3_2_30`](../theories/LinearHausdorffMeasureImage.v#L51); the dimension power is sqrt(n)^k. |

| 3.2.31, pp. 268–269 | Z={y:H^(m-mu)(f^-1{y})>=lambda}; t, t^-1; norm(Lambda^mu t)<epsilon | [`federer_3_2_31`](../theories/RectifiablePartialFibreThreshold.v#L33), [`is_small_exterior_majorant`](../theories/SmallExteriorMajorantUP.v#L21), [`small_exterior_majorant_exists`](../theories/SmallExteriorMajorantExistence.v#L27), [`is_compact_rescaled_cover`](../theories/CompactRescaledCoverUP.v#L26); the actual original partial fibre and non-strict positive threshold are retained. |

| 3.2.32, p. 269 | Y={y:H^(m-mu)(f^-1{y})>0}; X={x:dim im ap Df(x)<=mu}; integral over f^-1(Y) | [`positive_partial_fibre_locus`](../theories/RectifiablePositiveFibreCoareaUP.v#L18), [`partial_approximate_image_dimension_locus`](../theories/RectifiablePositiveFibreCoareaUP.v#L28), [`is_partial_image_dimension_at_most`](../theories/PartialImageDimensionUP.v#L18), `rectifiable_positive_fibre_rank_law`, `rectifiable_positive_fibre_integral_law`; all approximate data retain their original source and exact partial domains. |

| 3.2.33, p. 270 | phi, psi, g; V; X minus f inverse(Y); h_i; S={dim im Df=mu} | [`is_positive_unit_interval_bump`](../theories/PositiveUnitIntervalBumpUP.v#L17), [`is_interval_bump_series`](../theories/IntervalBumpSeriesUP.v#L17), [`is_interval_bump_primitive`](../theories/IntervalBumpPrimitiveUP.v#L19), [`is_scalar_cylinder_map`](../theories/ScalarCylinderMapUP.v#L16), [`euclidean_exterior_gram`](../theories/EuclideanExteriorGramRank.v#L36), [`relative_low_image_locus`](../theories/RelativeLowImageLocus.v#L18), [`relative_rank_locus`](../theories/RelativeRankLocus.v#L18); both numbered theorems retain the original partial Jacobian and fibre loci of 3.2.32. |

| 3.2.34, p. 271 | d(x)=dist(x,S); J_1 d=1; H^(n-1)(d^-1{t}) | `MetricSetDistance.value`, [`euclidean_closed_distance_jacobian_one`](../theories/EuclideanClosedDistanceJacobian.v#L26), [`federer_3_2_34`](../theories/ClosedSetDistanceCoarea.v#L29); the scalar subset integral uses whole original levels. |

| 3.2.35, pp. 271–272 | zeta^m(S), zeta^0(S)=1; alpha(n-m)r^(n-m); g(x)^(-1)x | [`integral_geometric_gauge`](../theories/IntegralGeometricGauge.v#L26) at exponent one, [`zero_degree_integral_geometric_gauge`](../theories/ZeroDegreeIntegralGauge.v#L41), [`steiner_tube_polynomial`](../theories/SteinerTubePolynomial.v#L32), [`is_minkowski_gauge`](../theories/MinkowskiGaugeUP.v#L22), [`is_radial_gauge_map`](../theories/RadialGaugeMapUP.v#L22); the corrected radial map parametrizes the entire boundary. |

| 3.2.36, pp. 272–273 | zeta^l(P times Q); elementary symmetric edge coefficients; product (1+c_i t); Q_1 | [`bounded_convex_cartesian_intrinsic_volumes`](../theories/BoundedConvexCartesianIntrinsicVolumes.v#L50), [`is_elementary_symmetric_coefficients`](../theories/ElementarySymmetricCoefficientsUP.v#L19), [`rectangular_box_elementary_symmetric_existence`](../theories/RectangularBoxIntrinsicVolumes.v#L95), [`convex_integral_geometric_isometric_embedding`](../theories/ConvexIntegralGeometricIsometricEmbedding.v#L26); actual finite intrinsic volumes and arbitrary-source Q_1 invariance. |

| 3.2.37, pp. 273–274 | upper M^m, lower M^m, common M^m; alpha(n-m) r^(n-m); finite compact projection sum; G^m | [`upper_minkowski_content`](../theories/MinkowskiContents.v#L28), [`lower_minkowski_content`](../theories/MinkowskiContents.v#L34), [`minkowski_content`](../theories/MinkowskiContents.v#L41), [`minkowski_tube_quotient`](../theories/MinkowskiContents.v#L20), [`is_finite_compact_projected_family`](../theories/CompactProjectionFamilyUP.v#L20), [`compact_projected_family_values`](../theories/CompactProjectionFamilyUP.v#L41), [`gross_measure_compact_projection_supremum`](../theories/GrossCompactProjectionSupremum.v#L99); full positive-real-radius limits, original arbitrary sources and degree-zero atoms. |

| 3.2.38, pp. 274–275 | C, F, G, H; rho(K), xi, eta; J_m f; upper M^m(f(C)) | [`is_euclidean_coordinate_cube`](../theories/EuclideanCoordinateCubeUP.v#L15), [`is_equal_coordinate_cube_grid`](../theories/EqualCoordinateCubeGridUP.v#L21), [`is_compact_core_cube_cover`](../theories/CompactCoreCubeCoverUP.v#L18), [`good_coordinate_cube_minkowski_estimate`](../theories/GoodCubeMinkowskiEstimate.v#L25), [`lipschitz_parent_cube_normalized_tube_bound`](../theories/LipschitzParentCubeTubeBound.v#L23), [`compact_image_minkowski_radius_bound`](../theories/CompactImageMinkowskiRadiusBound.v#L29), [`federer_3_2_38`](../theories/CompactLipschitzImageMinkowski.v#L73); actual local cubes, original partial Jacobian, full real-radius limit, corrected j=0 term and positive degree-zero atom. |

| 3.2.39, pp. 275–276 | G, v, S_j, sigma_j, t_C, S_(j,r); H^m(W)=M^m(W) | [`is_finite_compact_jacobian_cover`](../theories/FiniteCompactJacobianCoverUP.v#L19), [`finite_family_hit_count`](../theories/FiniteFamilyMultiplicity.v#L14), [`is_finite_family_layers`](../theories/FiniteFamilyLayersUP.v#L14), [`finite_family_layer_characteristic_sum`](../theories/FiniteFamilyLayerCharacteristicSum.v#L29), [`finite_family_layer_tube_characteristic_bound`](../theories/FiniteFamilyLayerTubeCharacteristicBound.v#L22), [`federer_3_2_39`](../theories/ClosedRectifiableMinkowski.v#L56); actual indexed image counts, full real-radius limits and finite multipoint degree-zero convention. |

| 3.2.40, p. 276, first paragraph | E=A(m,n)×A(m,n); upper M¹(E)=infinity; lower M¹(E)=0 or positive finite; H¹(E)=0 below m=1/2 | [`federer_3_2_40_cantor_square`](../theories/CantorSquareMinkowskiCounterexample.v#L33), [`is_rapid_power_cantor_scales`](../theories/RapidPowerCantorScalesUP.v#L18), [`power_cantor_carrier_coefficient_change`](../theories/PowerCantorCarrierCoefficient.v#L25); original same-factor carrier and full positive-real-radius contents. Kneser's second paragraph remains deferred. |

## Canonical maps of 1.1.2 (p. 10)

| Printed notation | Formal declaration |
| --- | --- |
| Permutation and grouping isomorphisms of finite tensor products | [`tensor_family_permutation_isomorphism`](../theories/TensorFamilyPermutation.v#L106), [`tensor_family_grouping_isomorphism`](../theories/TensorFamilyGrouping.v#L153) |
| Products of bases and dimensions | [`tensor_family_basis`](../theories/TensorFamilyBasis.v#L34), [`tensor_family_basisP`](../theories/TensorFamilyBasis.v#L142), [`tensor_family_dimension`](../theories/TensorFamilyDimension.v#L35) |
| Tensor of a direct sum | [`tensor_direct_sum_decomposition`](../theories/TensorDirectSum.v#L35), [`tensor_direct_sum_bijection`](../theories/TensorDirectSum.v#L103) |

## Phi of 1.1.4 (p. 11)

| Printed notation | Formal declaration |
| --- | --- |
| Phi: Hom(V,K) tensor W to Hom(V,W) | [`tensor_Hom`](../theories/HomTensor.v#L48), [`tensor_Hom_injective`](../theories/HomTensorGeneral.v#L53), [`tensor_Hom_finite_factor_surjective`](../theories/HomTensorGeneral.v#L108) |

- **Φ : Hom(V,K) ⊗ W → Hom(V,W)** (1.1.4, p. 11): injective for arbitrary V,W; surjective iff at least one has a finite basis ([`tensor_Hom_surjective_iff_finite_factor`](../theories/HomTensorInfinite.v#L99)); both infinite gives an actual missing image ([`tensor_Hom_infinite_missing_image`](../theories/HomTensorInfinite.v#L55)).

- **u, v, n, tau, lambda** (2.8.8, p. 145): the two normalized ball-growth bounds give an internally derived lambda > 1 and adequacy ([`ball_power_growth_regularity_exists`](../theories/BallPowerGrowthAdequacy.v#L18), [`ball_power_growth_family_adequate`](../theories/BallPowerGrowthAdequacy.v#L46)).

- **v strictly convex; radial x** (2.8.9, p. 146): [`is_strictly_convex_norm`](../theories/StrictConvexNorm.v#L22) specifies midpoint containment; actual inner norms satisfy it, and the two radial distance equations determine x uniquely, including zero radius ([`strict_convex_radial_projection_unique`](../theories/StrictConvexRadial.v#L54)).

## Real-dimensional Hausdorff normalization (2.10.2, p. 171)

| Printed notation | Formal interface |
| --- | --- |
| alpha(p) 2^(-p), 0<=p real | [`real_hausdorff_normalisation`](../theories/RealHausdorffNormalisation.v#L39); actual Gamma coefficient, positive and compatible with every natural degree |
| H^p, S^p | [`real_hausdorff_measure`](../theories/RealHausdorffMeasure.v#L34), [`real_spherical_measure`](../theories/RealHausdorffMeasure.v#L40); independent covering laws and actual Gamma normalization |
| H^0, finite H^p(A) with p<q | Counting measure and real-degree dimension drop in [`RealHausdorffMeasureLaws.v`](../theories/RealHausdorffMeasureLaws.v) |
| H^p<=S^p<=2^p H^p | [`real_hausdorff_le_spherical`](../theories/RealHausdorffMeasureLaws.v#L70), [`real_spherical_le_double_hausdorff`](../theories/RealHausdorffMeasureLaws.v#L80) |
| psi_delta for open versus unrestricted generators | [`planar_circle_selected_cutoff_gap`](../theories/PlanarCircleCutoffCounterexample.v#L170) at the actual circle diameter two and degree one |

| 3.2.41, pp. 277–278 | A+B; volume(A+B)^(1/n) ≥ volume(A)^(1/n)+volume(B)^(1/n), n>0; S* | [`vector_set_sum`](../theories/VectorSetSum.v#L15), [`is_vector_set_sum`](../theories/VectorSetSumUP.v#L17), [`euclidean_volume_root_sum_bound`](../theories/EuclideanVolumeRootSum.v#L20), [`federer_3_2_41`](../theories/BrunnMinkowski.v#L24), actual [`measure_density_one_points`](../theories/MeasureDensityPoints.v#L15); arbitrary nonempty original sets, including zero and infinite outer volumes. |

| 3.2.42, p. 278 | Outer distance strip and inner r-core; n·alpha(n)^(1/n)·volume^((n−1)/n) | [`federer_3_2_42`](../theories/BoundaryLayerVolume.v#L26), [`federer_3_2_42_distance_strips`](../theories/BoundaryLayerDistanceForm.v#L24); finite closure volume, all r>0 and n≥2, with nonempty-source/core line variants. |

| 3.2.43, p. 278 | Lower M^(n−1)(closure(S) minus interior(S)); isoperimetric volume power | [`federer_3_2_43`](../theories/IsoperimetricInequality.v#L50), [`positive_closure_volume_isoperimetric`](../theories/IsoperimetricInequality.v#L23); n≥2 includes zero volume; positive closure volume also allows n=1. |

| 3.2.44, p. 278 | H^(n−1)(closure(S) minus interior(S)); genuinely rectifiable boundary | [`federer_3_2_44`](../theories/RectifiableBoundaryIsoperimetric.v#L36), [`positive_closure_rectifiable_boundary_isoperimetric`](../theories/RectifiableBoundaryIsoperimetric.v#L60); actual closed-boundary content equality from 3.2.39. |
