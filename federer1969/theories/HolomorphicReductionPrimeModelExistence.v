(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), pp. 327, 330–332:
    construct the original local model from
    the printed prime-ideal and E_m
    hypotheses. All algebraic and holomorphic
    witnesses are selected behind the project's
    existing independent opaque interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import StandardHermitian HermitianRealImaginary HermitianUP UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric LinearBasis OrthonormalFamilies GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness OrthogonalGroupTopology NormDifferentialUP NormFiniteLinearBound
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing HolomorphicCoordinateGermsSealed
  FieldPrefixCoordinatesSealed HolomorphicPrefixGermMap HolomorphicPrefixGermMapLaws
  HolomorphicRotatedGermIdeal HolomorphicReductionActual HolomorphicReductionOriginalEquations
  SetGermSealed HolomorphicZeroGermSealed HolomorphicIdealVarietyGermSealed
  CommutativeIdealUP CommutativePolynomialUP CommutativePolynomialSealed
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationSealed
  PointedHolomorphicFunctionalGermExistence OriginalHolomorphicPolynomialCylinderWitnesses OrdinalCoordinateTail
  HolomorphicPrimeLocalModelUP HolomorphicPrimeLocalModelAssembly.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OriginalPrimeModel.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation Herm:=(@standard_hermitian_product R n).
Local Notation hHerm:=(@standard_hermitian_productP R n).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Hypothesis hON:orthonormal_family Herm e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Variable I:set G.
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Variable g:@unitary_group R X Herm hHerm (n+n) eR heR.
Variable m:'I_n.
Hypothesis hMN:((m:nat)<=n)%N.
Local Notation Y:=(coordinate_space (ComplexScalars.C R) m).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o).
Local Notation NY:=(@holomorphic_coordinate_norm R m).
Local Notation hNY:=(complex_norm_real (@holomorphic_coordinate_norm_laws R m)).
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R Y NY hNY 0)].
Local Notation PY:=(@holomorphic_representative_type R Y NY hNY 0).
Local Notation PX:=(@holomorphic_representative_type R X NX hNX 0).
Local Notation vy:=(@holomorphic_representative_value R Y NY hNY 0).
Local Notation vx:=(@holomorphic_representative_value R X NX hNX 0).
Local Notation Ig:=(@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g).
Local Notation P:=(@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega m hMN).
Local Notation E:=(@holomorphic_prefix_germ_map R X NX hNX n e he omega m hMN).
Local Notation gamma:=(fun j:'I_n=>@HolomorphicCoordinateGerms.value R X NX (@holomorphic_coordinate_norm_laws R n) n e he omega j).

(** Source for [holomorphic_reduction_prime_local_model_exists]:
    the original local reduction theorem,
    3.4.12, p. 339, extending 3.4.8(10), pp. 327, 330–332.
    Only the original prime ideal, positive
    m and E_m membership are hypotheses.
    The monic kernel, common denominator,
    finite ideal, actual holomorphic equations and
    finite holomorphic covering are all proved. *)
Theorem holomorphic_reduction_prime_local_model_exists:
  is_prime_commutative_ideal I ->(0<m)%N ->
  @holomorphic_reduction_actual_E R X Herm hHerm n e he omega I (widen_ord (leqnSn n) m) g ->
  exists k (first:'I_(n-m)) (U:set Y) (d:PY) (b:'I_(n-m)->'I_k->PY)
    (f:'I_(n-m)->PX) (Z:set X) (K:set G),
    exists (hIg:is_finitely_generated_commutative_ideal Ig)
      (hK:is_finitely_generated_commutative_ideal K),
      @is_holomorphic_prime_local_model R n m hMN e he omega P Ig hIg k first U d b f Z K hK.
Proof.
move=>hPrime hMPositive hEm.
pose Poly:=@CommutativePolynomial.space A.
pose embed:=@CommutativePolynomial.embed A.
pose variable:=@CommutativePolynomial.variable A.
pose coefficient:=@CommutativePolynomial.coefficient A.
have hPoly:=@CommutativePolynomial.laws A.
pose J:=@CommutativePolynomialEvaluation.map A Poly G embed variable coefficient hPoly E (gamma m).
have hJ:=@CommutativePolynomialEvaluation.laws A Poly G embed variable coefficient hPoly E (gamma m).
have [W [derivative [k [delta [T [first [F [K data]]]]]]]]:=
  @holomorphic_reduction_original_equation_data R X Herm hHerm n e he omega hDual I g m hMN
    Poly embed variable coefficient hPoly J hJ hPrime hMPositive hEm.
case:data=>hFirst data.
case:data=>hPositive data.
case:data=>hDistinguished data.
case:data=>hKernel data.
case:data=>hDerivative data.
case:data=>hDerivativeOutside data.
case:data=>hDeltaOutside data.
case:data=>hBound data.
case:data=>hFirstRelation data.
case:data=>hRelations data.
case:data=>hGenerated data.
case:data=>hKGenerated data.
case:data=>hFI data.
case:data=>hPowers data.
case:data=>hLarger data.
have [hIg [hF [hK hVariety]]]:=data.
have hP:=@FieldPrefixCoordinates.projection_laws (ComplexScalars.C R) X n omega m hMN.
have hPBound:=@norm_finite_linear_bounded R XR YR NX NY hNX hNY (n+n) eR heR (complex_hom_real P).
have hXiBound:=@norm_finite_linear_bounded R XR CR NX (@complex_modulus R) hNX
  (@complex_modulus_real_norm R) (n+n) eR heR (complex_hom_real (omega m)).
have [fXi hXiValue]:=@pointed_holomorphic_functional_representative_exists R X NX (@holomorphic_coordinate_norm_laws R n) 0 (omega m) hXiBound.
have hXiValues x:vx fXi x = omega m x by rewrite hXiValue subr0.
have hXiGerm:(holomorphic_germ fXi:G) = gamma m:=
  @HolomorphicCoordinateGerms.laws R X NX (@holomorphic_coordinate_norm_laws R n) n e he omega m fXi hXiValues.
have hJActual:is_commutative_polynomial_evaluation embed variable E (holomorphic_germ fXi) J.
  by rewrite hXiGerm.
have hE:=@holomorphic_prefix_germ_map_specification R X NX hNX n e he omega m hMN.
have [U [bW [bT [w [wD [s [dX [t [d cylinder]]]]]]]]]:=
  @original_holomorphic_polynomial_connected_cylinder_witnesses R X Y NX NY hNX hNY P E hE hPBound
    (omega m) hXiBound fXi hXiValues Poly embed variable coefficient hPoly J hJActual Ig W derivative k
    hDistinguished hDerivative hKernel delta [the finType of 'I_(n-m)] T first hBound hFirstRelation.
case:cylinder=>hUOrigin cylinder.
case:cylinder=>hUOpen cylinder.
case:cylinder=>hCylinderOpen cylinder.
case:cylinder=>hConnected cylinder.
case:cylinder=>hBWHolomorphic cylinder.
case:cylinder=>hBTHolomorphic cylinder.
case:cylinder=>hDHolomorphic cylinder.
case:cylinder=>hWHolomorphic cylinder.
case:cylinder=>hWDHolomorphic cylinder.
case:cylinder=>hSHolomorphic cylinder.
case:cylinder=>hDXHolomorphic cylinder.
case:cylinder=>hTHolomorphic cylinder.
case:cylinder=>hWGerm cylinder.
case:cylinder=>hWDGerm cylinder.
case:cylinder=>hTGerm cylinder.
case:cylinder=>hDGerm cylinder.
case:cylinder=>hDXGerm cylinder.
case:cylinder=>hBWGerm cylinder.
case:cylinder=>hBTGerm cylinder.
case:cylinder=>hLeading cylinder.
case:cylinder=>hLower cylinder.
case:cylinder=>hWValue cylinder.
case:cylinder=>hTValue cylinder.
case:cylinder=>hDXValue cylinder.
case:cylinder=>hWDerivative cylinder.
have hIdentity:=cylinder.
have hFirstIndex:ordinal_coordinate_tail_index hMN first = m.
  apply:val_inj;change (((m:nat)+(first:nat))%N = (m:nat)).
  by rewrite hFirst addn0.
have hWValueFinal x:vx w x = \sum_(i<k.+1) vy (bW i) (P x)*
    (omega (ordinal_coordinate_tail_index hMN first) x)^+(i:nat).
  by rewrite hFirstIndex.
have hTValueFinal j x:vx (t j) x = \sum_(i<k) vy (bT j i) (P x)*
    (omega (ordinal_coordinate_tail_index hMN first) x)^+(i:nat).
  by rewrite hFirstIndex.
have hWDerivativeFinal a:(U (P a)) ->exists L:Hom XR CR,
    @has_norm_differential R XR CR NX (@complex_modulus R) (fun x=>U (P x)) (vx w) a L /\
    forall u,P u = 0 ->L u = vx wD a*omega (ordinal_coordinate_tail_index hMN first) u.
  rewrite hFirstIndex;exact:(@hWDerivative a).
have hGeneratedActual:is_generated_commutative_ideal
    [set alpha:G|exists j:'I_(n-m),alpha = if j==first then (holomorphic_germ w:G) else
      (holomorphic_germ dX:G)*gamma (ordinal_coordinate_tail_index hMN j)-(holomorphic_germ (t j):G)] F.
  have hTerm j:(if j==first then (holomorphic_germ w:G) else
      (holomorphic_germ dX:G)*gamma (ordinal_coordinate_tail_index hMN j)-(holomorphic_germ (t j):G)) =
      (if j==first then J W else E delta*gamma (ordinal_coordinate_tail_index hMN j)-J (T j)).
    by case:(j==first);rewrite ?hWGerm ?hDXGerm ?hTGerm.
  have hSeeds:[set alpha:G|exists j:'I_(n-m),alpha = if j==first then (holomorphic_germ w:G) else
      (holomorphic_germ dX:G)*gamma (ordinal_coordinate_tail_index hMN j)-(holomorphic_germ (t j):G)] =
      [set alpha:G|exists j:'I_(n-m),alpha = if j==first then J W else
        E delta*gamma (ordinal_coordinate_tail_index hMN j)-J (T j)].
    apply/seteqP;split=>alpha [j hj];exists j.
    - by rewrite -hTerm.
    - by rewrite hTerm.
  by rewrite hSeeds.
have hKGeneratedActual:is_generated_commutative_ideal (Ig `|` [set alpha:G|alpha = E (holomorphic_germ d)]) K.
  by rewrite hDGerm.
have hDeltaOutsideActual:~Ig (E (holomorphic_germ d)) by rewrite hDGerm.
have hVarietyActual:@HolomorphicIdealVarietyGerm.value R X NX hNX 0 Ig hIg =
    @SetGerms.join (Topological.clone (real_norm_metric_space hNX) _) 0
      (@HolomorphicIdealVarietyGerm.value R X NX hNX 0 K hK)
      (@SetGerms.meet (Topological.clone (real_norm_metric_space hNX) _) 0
        (@HolomorphicIdealVarietyGerm.value R X NX hNX 0 F hF)
        (@SetGerms.neg (Topological.clone (real_norm_metric_space hNX) _) 0
          (@HolomorphicZeroGerm.value R X NX hNX 0 (holomorphic_germ dX)))).
  by rewrite hDXGerm.
have [b [f [Z hModel]]]:=@holomorphic_prime_local_model_assembly R n m hMN e he omega hDual P hP
  Ig F K hIg hF hK k first hFirst hPositive U hUOrigin hUOpen d bW bT w wD s dX t
  hDHolomorphic hBWHolomorphic hBTHolomorphic hWHolomorphic hTHolomorphic hLeading hLower hWValueFinal hTValueFinal
  hDXValue hWDerivativeFinal hIdentity hDeltaOutsideActual hGeneratedActual hFI hKGeneratedActual hVarietyActual hLarger.
by exists k,first,U,d,b,f,Z,K,hIg,hK.
Qed.
End OriginalPrimeModel.
