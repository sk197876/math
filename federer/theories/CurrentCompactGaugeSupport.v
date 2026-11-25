(** Federer (1969), 4.1.7, p. 358: all tests
    bounded by one original compact scalar
    majorant share a compact support bound.
    This supports the local-normality criteria via
    the original 4.1.5 gauge, p. 349. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology functions.
From Federer Require Import IsotropyGroupTopology NormBoundedLinearTopology Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms
  CurrentSpaces CurrentSupportGeometry SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport
  SmoothTestSpaces SmoothTestEvaluation DistributionVariationDomain CompactSupportFunctionUP
  CompactScalarOpenSupport NormDominatedFunctionSupport OpenSubspaceExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactGaugeSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Y := (A_m X R^o m).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := [the topologicalType of set_type (U:set XT)].
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation values := (smooth_test_values_hom hE).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT values).

(** Source for [current_compact_gauge_support]: every
    original compact continuous majorant supplies
    a compact K containing the supports of
    all its admissible tests, supporting Federer
    4.1.7, p. 358. No uniform derivative
    bound on those tests is assumed. *)
Theorem current_compact_gauge_support (f:UT->R):
  @compactly_supported_continuous_functions R UT f ->
  exists K:smooth_compact_set hNX U,forall phi:DT,
    (forall x:UT,NY (dvalues phi x)<=f x) ->
    @current_test_support R h2 n m U hU phi `<=` smooth_compact_carrier K.
Proof.
move=>hf.
pose S:set XT:=set_val @` (@real_function_support R UT f).
have hS:compact S.
  apply:continuous_compact hf.2;apply:continuous_subspaceT=>x;exact:set_type_val_continuous.
have hSU:S `<=` U by move=>x [y hy <-];exact:(set_valP y).
pose K:=@Build_smooth_compact_set R X NX hNX U S hSU hS.
have hOpen:@open XT U.
  rewrite openE=>x hx;exact:(@norm_domain_interior_neighbourhood R X NX hNX U x).1 (hU x hx).
have hSupport:=@compact_scalar_open_extension_support R XT (@metric_hausdorff R XT) U hOpen f hf.
exists K=>phi hPhi x hx.
apply:(hSupport x).
have hBound:(forall z,NY (@current_test_value R h2 n U hU m phi z)<=@open_extension R XT U f z).
  exact:(@distribution_domain_gauge_admissible R XT U Y NY hNY DT values
    (fun q z hz=>smooth_function_evaluation_outside hE _ hz) phi f).1 hPhi.
exact:(@norm_dominated_function_support R X Y NX NY hNX hNY U DT
  (@current_test_value R h2 n U hU m) phi (@open_extension R XT U f) hBound x hx).
Qed.
End CurrentCompactGaugeSupport.
