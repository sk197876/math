(** Federer (1969), 4.1.14, p. 372: approximate
    an arbitrary continuous form near the compact current
    support by an actual test and control the action
    error by mass times the uniform comass error.
    Reuse the preceding original L1 one-Lipschitz law. *)
From mathcomp Require Import all_boot all_order all_algebra functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct AlternatingForms CurrentSpaces CurrentDomain
  CurrentCoefficientNorms CurrentIntegrationCriterion NormalisedCurrentSealed
  CurrentMassSealed CurrentMassBasic CurrentMassRepresentation CurrentRadonSupport
  CurrentSupportGeometry SmoothCompactSet CompactCurrentContinuousLoneMember
  CurrentOriginalBallFormula CurrentLoneExtension CurrentLoneOriginalAgreement
  CurrentLoneSequenceLimit DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureLpMembershipUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentContinuousTestActionBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Variable K:smooth_compact_set hNX U.
Local Notation UT := (current_domain R n U).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation value := (@current_test_value R h2 n U hU m).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation xi := (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).
Local Notation hNormal := (@NormalisedCurrent.laws R h2 n m U hU T hT).
Local Notation I := (@current_representation_lone_integral R h2 n m U hU T
  mu xi hNormal).

(** Source for [current_continuous_test_action_error_bound]:
    the actual continuous-form action and test action differ
    by at most the original mass bound times a common
    comass error on K, supporting Federer 4.1.14,
    p. 372. Finite mass is derived from the stated
    real mass cap. The form keeps its full domain
    and no normality or density choice is assumed. *)
Theorem current_continuous_test_action_error_bound a error
    (phi:X->Y) (psi:DT):
  (@CurrentMass.value R h2 n m U hU T<=a%:E)%E->
  @current_support R h2 n U hU m T `<=` smooth_compact_carrier K->
  norm_class_zero NX NY U phi->0<=error->
  (forall x,smooth_compact_carrier K x->NY (phi x-value psi x)<=error)->
  `|I (partial_function_total (fun x:UT=>(phi (set_val x):real_norm_metric_space hNY)))-
    @current_value R h2 n U hU m T psi|<=error*a.
Proof.
move=>hMassCap hSupport hPhi hError hPoint.
have hFinite:(@CurrentMass.value R h2 n m U hU T< +oo)%E:=
  le_lt_trans hMassCap (ltry a).
have[mass [hMassNonnegative hMass]]:=@current_finite_mass_value R h2 n m U hU T hFinite.
have hMassToA:mass<=a by move:hMassCap;rewrite hMass lee_fin.
have hTotal:mu setT=mass%:E.
  by rewrite -(@current_represented_mass_total R h2 n m U hU T hT) hMass.
have hCompact:=@current_support_compact_bound R h2 n m U hU K T hSupport.
have hMemberPhi:=@compact_represented_current_continuous_lone_member R h2 n m
  U hU T hT hCompact phi hPhi.
have hMemberPsi:=@current_original_test_lone_member R h2 n m U hU
  T mu xi hNormal psi.
have hm:=distribution_representation_measure
  (normalised_distribution_representation_laws hNormal).
have hSupportAlmost:measure_almost_everywhere mu
    [set x:UT|@current_support R h2 n U hU m T (set_val x)].
  exact:(@current_radon_outside_support_null R h2 n m U hU T hT).
have hPointAlmost:measure_almost_everywhere mu
    [set x:UT|NY (phi (set_val x)-value psi (set_val x))<=error].
  apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _ hSupportAlmost)=>x hx.
  exact:hPoint (set_val x) (hSupport (set_val x) hx).
have hBound:=@current_lone_almost_uniform_action_bound R h2 n m U hU T
  mu xi hNormal mass error (fun x:UT=>phi (set_val x))
  (fun x:UT=>value psi (set_val x)) hTotal hMemberPhi hMemberPsi hPointAlmost.
rewrite current_lone_extension_original in hBound.
exact:le_trans hBound (ler_wpM2l hError hMassToA).
Qed.
End CurrentContinuousTestActionBound.
