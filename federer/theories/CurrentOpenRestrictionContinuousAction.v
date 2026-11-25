(** Federer (1969), 4.1.14, pp. 370, 372: a
    source representative under inclusion gives the same full
    continuous-form action as the original compact finite-mass
    current. The exact trace representation from 4.1.13,
    pp. 369–370, and the preceding bounded-density uniqueness
    transport both the variation and its pairing density.
    No normality or compact support of the form is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormClassHigherRestriction InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms
  CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentMultivectorDual
  MultivectorDualSealed CurrentSpaces CurrentDomain CurrentIntegrationCriterion
  NormalisedCurrentSealed CurrentOpenRestriction CurrentOpenRestrictionSupport
  CurrentOpenRestrictionVariation BoundedCurrentDensityUniqueness
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  CurrentOriginalBallFormula CurrentLoneExtension CompactCurrentContinuousLoneMember
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralAlmostEquality MeasureIntegralUniqueness
  SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentOpenRestrictionContinuousAction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation ed := (@MultivectorDual.evaluation R X m).
Variables U Z:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hZ:forall x,Z x->norm_domain_interior NX Z x.
Hypothesis hZU:forall x,Z x->U x.
Local Notation UT := (current_domain R n U).
Local Notation ZT := (current_domain R n Z).
Local Notation inc := (@current_open_domain_inclusion R n Z U hZU).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Hypothesis hSupport:@current_support R h2 n U hU m T `<=` Z.
Local Notation S := (@current_open_restriction R h2 n m Z U hZ hU hZU T).
Hypothesis hSmall:@is_integration_representable_current R h2 n m Z hZ S.
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation xi := (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).
Local Notation muZ := (@NormalisedCurrent.measure R h2 n m Z hZ S hSmall).
Local Notation xiZ := (@NormalisedCurrent.auxiliary_density R h2 n m Z hZ S hSmall).
Local Notation hNormal := (@NormalisedCurrent.laws R h2 n m U hU T hT).
Local Notation hNormalZ := (@NormalisedCurrent.laws R h2 n m Z hZ S hSmall).
Local Notation I := (@current_representation_lone_integral R h2 n m U hU T
  mu xi hNormal).
Local Notation IZ := (@current_representation_lone_integral R h2 n m Z hZ S
  muZ xiZ hNormalZ).

(** Source for [current_neighbourhood_density_almost_equal]:
    the actual normalized density after original source
    restriction agrees almost everywhere with the old density
    composed with inclusion. This supports the continuous
    action comparison in Federer 4.1.14, p. 372,
    using the exact original trace measure and bounded-density
    uniqueness of 4.1.7, pp. 357–359. *)
Theorem current_neighbourhood_density_almost_equal:
  measure_almost_everywhere muZ [set x:ZT|xi (inc x)=xiZ x].
Proof.
have hRep:=@current_neighbourhood_restriction_representation R h2 n m
  Z U hZ hU hZU T hT hSupport.
have hTrace:=@current_neighbourhood_variation_trace R h2 n m
  Z U hZ hU hZU T hT hSupport hSmall.
have hSmallBase:=normalised_distribution_representation_laws hNormalZ.
rewrite hTrace in hSmallBase.
have hUnit x:VN (xi (inc x))<=1:=
  normalised_distribution_density_unit_bound hNormal (inc x).
have hEqual:=@bounded_current_density_almost_unique R h2 n m Z hZ _
  (distribution_representation_measure hRep) (distribution_representation_radon hRep)
  (fun x:ZT=>xi (inc x)) xiZ
  (distribution_representation_weak_measurable hRep)
  (distribution_representation_weak_measurable hSmallBase) hUnit
  (normalised_distribution_density_unit_bound hNormalZ)
  (@current_value R h2 n Z hZ m S)
  (distribution_representation_action hRep) (distribution_representation_action hSmallBase).
rewrite hTrace;exact:hEqual.
Qed.

(** Source for [current_neighbourhood_continuous_action]:
    the representative on Z and the original compact
    represented current have the same action on every
    continuous form on U, supporting the last assertion
    of Federer 4.1.14, p. 372. Finite variation
    is derived from compact support; the form retains
    its full domain without a support or normality premise. *)
Theorem current_neighbourhood_continuous_action
    (hCompact:@compact (real_norm_metric_space hNX)
      (@current_support R h2 n U hU m T)) (w:X->Y):
  norm_class_zero NX NY U w->
  IZ (partial_function_total (fun x:ZT=>(w (set_val x):real_norm_metric_space hNY)))=
  I (partial_function_total (fun x:UT=>(w (set_val x):real_norm_metric_space hNY))).
Proof.
move=>hw.
have hSupportEqual:@current_support R h2 n Z hZ m S=
    @current_support R h2 n U hU m T.
  rewrite current_open_restriction_support.
  apply:funext=>x;apply:propext;split.
  - by move=>[_ hx].
  - move=>hx;split;first exact:(@hSupport x hx).
    exact:hx.
have hCompactZ:@compact (real_norm_metric_space hNX)
    (@current_support R h2 n Z hZ m S).
  by rewrite hSupportEqual.
have hwZ:norm_class_zero NX NY Z w.
  exact:(@norm_class_zero_open_restriction R X Y NX NY U Z w hZU hZ hw).
have hMember:=@compact_represented_current_continuous_lone_member R h2 n m
  U hU T hT hCompact w hw.
have hMemberZ:=@compact_represented_current_continuous_lone_member R h2 n m
  Z hZ S hSmall hCompactZ w hwZ.
have hOriginal:=@current_representation_lone_total_action R h2 n m U hU
  T mu xi hNormal (fun x:UT=>w (set_val x)) hMember.
have hTarget:=@current_representation_lone_total_action R h2 n m Z hZ
  S muZ xiZ hNormalZ (fun x:ZT=>w (set_val x)) hMemberZ.
have hTransport:=(@current_neighbourhood_variation_total_integral_iff R h2 n m
  Z U hZ hU hZU T hT hSupport hSmall
  (fun x:UT=>ed (xi x) (w (set_val x))) _).2 hOriginal.
have hDomain:(fun x:ZT=>ed (xi (inc x)) (w (set_val (inc x))))=
    (fun x:ZT=>ed (xi (inc x)) (w (set_val x))).
  apply:funext=>x;by rewrite current_open_domain_inclusion_value.
rewrite hDomain in hTransport.
have hmZ:=distribution_representation_measure
  (normalised_distribution_representation_laws hNormalZ).
have hAlmost:measure_almost_equal muZ
    (real_total_integrand (fun x:ZT=>ed (xi (inc x)) (w (set_val x))))
    (real_total_integrand (fun x:ZT=>ed (xiZ x) (w (set_val x)))).
  apply:(@measure_almost_everywhere_mono R ZT muZ hmZ _ _ _
    current_neighbourhood_density_almost_equal)=>x hx.
  exists (ed (xiZ x) (w (set_val x)))%:E;split;rewrite real_total_integrand_graph.
  - by rewrite hx.
  - by [].
exact:(EFin_inj (measure_integral_unique hTarget
  (measure_integral_almost_equal hmZ hTransport hAlmost))).
Qed.
End CurrentOpenRestrictionContinuousAction.
