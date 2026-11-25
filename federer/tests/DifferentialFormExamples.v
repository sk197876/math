(** Federer (1969), 4.1.6, pp. 351–355:
    concrete endpoint checks on the actual original
    form and operator spaces. The complete consumer
    imports every new source for recursive checking. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom TensorUP RealNormUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanScalarCoordinateMaps InnerNorm HilbertFormCompactness
  NormDifferentialUP NormDifferentialLinear NormOpenDomainLaws NormHigherDifferentialUP NormHigherDifferentialConstant
  ContinuousMultilinearSealed ContinuousMultilinearUP
  GradedComponents Exterior ExteriorPowers FiniteExteriorPowers Alternating
  OneFormIdentification PartialFunctionUP.
From Federer Require Import DifferentialFormPairingIdentification.
From Federer Require Import
  AlternatingFormNormBound AlternatingFormNormExistence AlternatingFormNormSealed AlternatingFormNormUP AlternatingFormUnitBounds AlternatingFormZeroNorm ClosedOneFormProducts
  ClosedScalarFormProduct CoordinateProductPullbackClosed CoordinatePullbackClosed DifferentialFormCoefficientEmbedding DifferentialFormCoefficientMaps DifferentialFormContractions DifferentialFormDuality
  DifferentialFormFields DifferentialFormHodgeValues DifferentialFormPointwiseNorms DifferentialFormPullbackConstruction DifferentialFormPullbackLaws DifferentialFormPullbackSealed DifferentialFormPullbackUP
  DifferentialFormScalarOperations DifferentialForms DivergenceConstruction DivergenceCoordinates DivergenceDerivative DivergenceDuality DivergenceDualityAlgebra
  DivergenceSealed DivergenceUP EuclideanCoordinateForms EuclideanFormNorm ExteriorDerivativeConstruction ExteriorDerivativeCoordinates ExteriorDerivativeFiniteSum
  ExteriorDerivativeLeibniz ExteriorDerivativeSealed ExteriorDerivativeSquared ExteriorDerivativeUP ExteriorDerivativeZeroDegree ExteriorDifferentialCoefficientNaturality ExteriorDifferentialCoefficients
  ExteriorDifferentialExistence ExteriorDifferentialLeibnizAlgebra ExteriorDifferentialLinearLaws ExteriorDifferentialNormBound ExteriorDifferentialOperator ExteriorDifferentialSealed ExteriorDifferentialSecondZero
  ExteriorDifferentialTensor ExteriorDifferentialUP ExteriorOmittedTupleValues FormCoefficientProductBound FormCoefficientSeparation FormDualityContraction MixedAlternatingProduct
  MixedAlternatingProductNorm MixedAlternatingShuffle MixedOrdinaryFormProduct MixedScalarContraction MixedScalarOneProductsSkew OneCovectorInterior OneFormOperatorNorm
  OneFormProductHead OneFormPullbackIdentification OriginalCoordinateFormFields OriginalFormCoefficientDifferentials OriginalFormCoefficientExpansion PointwiseFieldMaps PointwiseFieldSpaceExistence
  PointwiseFieldSpaceSealed PointwiseFieldSpaceUP PullbackExteriorDerivative RealDifferentialFormCalculus RealFormPullbackDifferential ScalarCovectorWordContraction ScalarOneFormProductOmission
  SymmetricOneFormClosed VectorFormPullbackDifferentiable VectorFormPullbackDifferential ZeroFormScalarProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [actual_coordinate_zero_degree_derivative]:
    d phi=D phi for the nonconstant scalar coordinate
    on the actual line, Federer 4.1.6,
    p. 352. The exterior derivative is nonzero. *)
Theorem actual_coordinate_zero_degree_derivative (R:realType) (h2:(1+1:R)!=0) (a:R_n R 1):
  has_real_form_derivative h2 setT
    (fun x:R_n R 1=>@zero_form R (R_n R 1) R^o (x ord0)) a
    (@euclidean_coordinate_form R 1 ord0).
Proof.
exact:(@exterior_derivative_zero_degree R (R_n R 1) R^o
  (inner_norm (@euclidean_inner_productP R 1)) (fun t:R^o=>`|t|)
  (inner_norm_real_norm (@euclidean_inner_productP R 1)) (@scalar_absolute_value_norm R)
  (@real_euclidean_form_norm R h2 1 0) (@real_euclidean_form_norm_laws R h2 1 0)
  setT (@euclidean_scalar_coordinate_map R 1 ord0) a (@euclidean_scalar_coordinate_map R 1 ord0)
  (@euclidean_coordinate_original_differential R 1 ord0 a)).
Qed.

(** Source for [actual_empty_form_derivative_domain]:
    the original derivative has no value outside
    its domain, Federer 4.1.6, p. 352.
    In particular its sealed graph on an empty
    domain is empty, even at dimension zero. *)
Theorem actual_empty_form_derivative_domain (R:realType) (h2:(1+1:R)!=0)
    (W:lmodType R) (NW:W->R) (hNW:is_real_norm NW) m
    (phi:R_n R 0->A_m (R_n R 0) W m) a b:
  ~partial_function_graph
    (@ExteriorDerivative.value R (R_n R 0) W (inner_norm (@euclidean_inner_productP R 0))
      (inner_norm_real_norm (@euclidean_inner_productP R 0)) m
      (@euclidean_form_norm R h2 0 W NW hNW m) (@euclidean_form_norm_real_norm R h2 0 W NW hNW m)
      set0 phi) a b.
Proof.
move=>hGraph.
have [L [hL _]]:=(@ExteriorDerivative.laws R (R_n R 0) W
  (inner_norm (@euclidean_inner_productP R 0)) (inner_norm_real_norm (@euclidean_inner_productP R 0)) m
  (@euclidean_form_norm R h2 0 W NW hNW m) (@euclidean_form_norm_real_norm R h2 0 W NW hNW m)
  set0 phi a b).1 hGraph.
exact:(norm_domain_interior_member (inner_norm_real_norm (@euclidean_inner_productP R 0))
  (norm_differential_interior hL)).
Qed.

(** Source for [actual_positive_degree_on_zero_space]:
    positive-degree forms on the actual zero-dimensional
    source vanish; the unrestricted-degree definitions
    in Federer 4.1.6, pp. 351–352,
    retain this endpoint rather than excluding it. *)
Theorem actual_positive_degree_on_zero_space (R:realType) (h2:(1+1:R)!=0)
    (W:lmodType R) (phi:A_m (R_n R 0) W 1):phi=0.
Proof.
apply:(can_inj (@form_to_homK R (R_n R 0) W 1)); apply:hom_ext=>xi.
have hZero:=@exterior_power_above_dimension R 0 (R_n R 0) (@coordinate_basis R 0)
  (@coordinate_basisP R 0) h2 1 (ltn0Sn 0) xi.
by rewrite hZero !linear0.
Qed.

(** Source for [actual_zero_degree_on_zero_space_nonzero]:
    degree-zero coefficients remain present on the
    actual zero-dimensional source,
    Federer 4.1.6, pp. 351–352. *)
Theorem actual_zero_degree_on_zero_space_nonzero (R:realType):
  @zero_form R (R_n R 0) R^o 1!=0.
Proof.
apply/eqP=>hEqual.
have hValue:=congr1 (fun phi:A_m (R_n R 0) R^o 0=>phi [tuple]) hEqual.
rewrite zero_formE form_zeroE in hValue.
change ((1:R)=0) in hValue.
by move:(oner_neq0 R); rewrite hValue eqxx.
Qed.

Section ActualZeroDimensionalOperators.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation E:=(R_n R 0).
Local Notation N:=(inner_norm (@euclidean_inner_productP R 0)).
Local Notation hN:=(inner_norm_real_norm (@euclidean_inner_productP R 0)).
Local Notation Z:=(fun k=>@ContinuousMultilinear.space R k E E N N hN hN).
Local Notation ev:=(fun k=>@ContinuousMultilinear.evaluation R k E E N N hN hN).
Local Notation ZN:=(fun k=>@ContinuousMultilinear.norm R k E E N N hN hN).
Local Notation hZ:=(fun k=>@ContinuousMultilinear.laws R k E E N N hN hN).
Variable W:lmodType R.
Variable NW:W->R.
Hypothesis hNW:is_real_norm NW.
Variable w:W.
Local Notation P:=(@euclidean_form_norm R h2 0 W NW hNW 0).
Local Notation phi:=(fun _ : E=>@zero_form R E W w).

(** Source for [actual_zero_dimensional_pullback_commutation]:
    the full original pullback commutation theorem
    on actual sealed multilinear spaces, with
    zero source and target dimension and an arbitrary
    coefficient value, Federer 4.1.6,
    pp. 354–355. No coefficient completeness or
    separability assumption is available in this check. *)
Theorem actual_zero_dimensional_pullback_commutation:
  exists (theta:E->A_m E W 0) (dphi:E->A_m E W 1) (dtheta:E->A_m E W 1),
    (forall y,has_exterior_derivative N P setT phi y (dphi y)) /\
    (forall x,has_differential_form_pullback N N setT setT (fun _ : E=>0) phi x (theta x) /\
      has_exterior_derivative N P setT theta x (dtheta x) /\
      has_differential_form_pullback N N setT setT (fun _ : E=>0) dphi x (dtheta x)).
Proof.
have hTwice x:True->exists z:Z 2%N,
    has_norm_higher_differential N ev ZN setT (fun _ : E=>0) 2%N x z.
  move=>_; exists 0.
  exact:(@norm_higher_differential_constant R E E N N hN hN Z ev ZN hZ setT
    (fun x _=>@norm_full_domain_interior R E N x) 0 (0:Z 0%N)
    (linear0 (@ev 0%N [ffun i:'I_0=>(0:E)])) 2%N x Logic.I).
have hPhi y:True->norm_differentiable_at N P setT phi y.
  move=>_; exists 0.
  exact:(@norm_differential_constant R E (A_m E W 0) N P hN
    (@euclidean_form_norm_real_norm R h2 0 W NW hNW 0) setT y (@zero_form R E W w)
    (@norm_full_domain_interior R E N y)).
have [theta [dphi [dtheta [hdphi hValues]]]]:=
  @original_pullback_exterior_derivative R h2 0 0 Z ev ZN hZ setT setT
    (fun _ : E=>0) (fun x _=>Logic.I) W NW hNW 0 phi hTwice hPhi.
exists theta,dphi,dtheta; split.
- move=>y; exact:(hdphi y Logic.I).
- move=>x; exact:(hValues x Logic.I).
Qed.
End ActualZeroDimensionalOperators.
