(** Federer (1969), 4.1.7, p. 358: local
    agreement on compact test supports suffices
    for integration representation. The proof
    retains the original scalar-test gauge of
    4.1.5, p. 349, and its exact criterion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingZero CurrentCoefficientNorms
  CurrentSpaces CurrentSupportGeometry CurrentCompactGaugeSupport CurrentScalarCutoffs CurrentScalarPlateau
  CurrentContraction CurrentIntegrationCriterion SmoothCompactSet SmoothFunctionSpaceUP SmoothTestSpaces
  SmoothTestEvaluation DistributionVariationUP DistributionVariationDomain DistributionFiniteVariationUP
  FunctionLatticeUP CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentLocalRepresentation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Y := (A_m X R^o m).
Local Notation NY := (@current_form_comass R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation hE0 := (@current_smooth_space_laws R h2 n U hU 0%N).
Local Notation C := (@current_space R h2 n U hU m).
Local Notation represented := (@is_integration_representable_current R h2 n m U hU).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation values := (smooth_test_values_hom hE).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT values).
Local Notation support := (@current_test_support R h2 n m U hU).

(** Source for [current_compact_agreement_representation]:
    a current agreeing on each compact test
    support with a represented current is
    itself representable, supporting the original
    local-normality equivalences in Federer 4.1.7,
    p. 358, by 4.1.5. *)
Theorem current_compact_agreement_representation (T:C):
  (forall K:smooth_compact_set hNX U,exists S:C,represented S /\
    forall psi:DT,support psi `<=` smooth_compact_carrier K->action T psi=action S psi) ->
  represented T.
Proof.
move=>hLocal.
apply:(@current_integration_finite_gauge_criterion R h2 n m U hU T).1=>f hf.
have[K hK]:=@current_compact_gauge_support R h2 n m U hU f hf.1.
have[S [hS hAgree]]:=hLocal K.
have[b hB]:=((@current_integration_finite_gauge_criterion R h2 n m U hU S).2 hS) f hf.
have hValues:distribution_variation_values NY dvalues (action T) f=
    distribution_variation_values NY dvalues (action S) f.
  apply:funext=>a;apply:propext;split=>-[psi [hPsi hValue]];exists psi;split=>//.
  - rewrite -(hAgree psi (hK psi hPsi));exact:hValue.
  - rewrite (hAgree psi (hK psi hPsi));exact:hValue.
exists b;rewrite /is_distribution_variation_value hValues;exact:hB.
Qed.

(** Source for [current_compact_scalar_representation]:
    representability of every compact scalar
    localization implies representability of T,
    supporting the first local-normality equivalence
    in Federer 4.1.7, p. 358. *)
Theorem current_compact_scalar_representation (T:C):
  (forall gamma:@current_test_space R h2 n U hU 0%N,
    represented (@current_contraction R h2 n 0 m U hU (smooth_test_inclusion hE0 gamma) T)) ->
  represented T.
Proof.
move=>hCutoffs;apply:current_compact_agreement_representation=>K.
have[gamma [W [hW [hKW [hWU hOne]]]]]:=@current_compact_scalar_cutoff R h2 n U hU K.
pose a:=smooth_test_inclusion hE0 gamma.
exists (@current_contraction R h2 n 0 m U hU a T);split;first exact:hCutoffs.
move=>psi hPsi;rewrite current_contraction_evaluation.
have hPlateau:forall x,smooth_compact_carrier K x->
    @current_smooth_value R h2 n U hU 0%N a x=@zero_form R X R^o 1.
  move=>x hx;exact:hOne x (hKW x hx).
by rewrite (@current_scalar_test_plateau R h2 n m U hU K a hPlateau psi hPsi).
Qed.
End CurrentLocalRepresentation.
