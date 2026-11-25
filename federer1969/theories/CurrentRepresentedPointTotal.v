(** Federer (1969), 4.1.12, p. 368: the
    support obstruction for the endpoint series uses
    the fact that a represented point-supported zero-current
    of total zero vanishes. Reuse the original
    representation and compact smooth extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingZero CurrentSpaces
  CurrentEvaluation CurrentIntegrationCriterion CurrentConstantFields CurrentCompactSmoothValue
  CurrentRepresentedCompactSmoothAgreement SmoothFunctionSpaceLaws SmoothTestSpaces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentRepresentedPointTotal.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable T:@current_space R h2 n U hU 0%N.
Hypothesis hT:@is_integration_representable_current R h2 n 0%N U hU T.
Hypothesis hCompact:@compact (real_norm_metric_space hNX) (@current_support R h2 n U hU 0%N T).
Local Notation E := (@current_smooth_space R h2 n U hU 0%N).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU 0%N).
Local Notation L := (@current_compact_smooth_value R h2 n 0%N U hU T hCompact).
Local Notation one := (@current_constant_form R h2 n U hU 0%N (@zero_form R X R^o 1)).

(** Source for [current_represented_point_total_zero]:
    an original represented zero-current supported at a
    point and with T(1)=0 is zero, supporting
    Federer 4.1.12, p. 368. The point need
    not belong to the open domain; the empty-support
    case is included. *)
Theorem current_represented_point_total_zero x:
  @current_support R h2 n U hU 0%N T `<=` [set x]->
  @current_compact_total R h2 n U hU T hCompact=0->T=0.
Proof.
move=>hPoint hTotal.
apply:(@current_values_extensional R h2 n 0%N U hU)=>phi.
pose c:=@zero_form_value R X R^o (@current_test_value R h2 n U hU 0%N phi x).
have hAgree:L (smooth_test_inclusion hE phi)=L (c*:one).
  apply:(@current_represented_compact_smooth_values_equal R h2 n 0%N U hU T hT hCompact)=>y hy.
  have hEqual:y=x:=hPoint y hy.
  rewrite (smooth_function_scale_value hE)
    (@current_constant_form_values R h2 n U hU 0%N _ y hy.1) hEqual.
  change (@current_test_value R h2 n U hU 0%N phi x=c*:@zero_form R X R^o 1).
  rewrite -{1}(zero_form_valueK (@current_test_value R h2 n U hU 0%N phi x)).
  apply:form_ext=>t;rewrite form_scaleE !zero_formE.
  change (c=c*1);by rewrite mulr1.
rewrite current_compact_smooth_test_value (linZ (hom_linear L)) in hAgree.
change (L one=0) in hTotal.
rewrite hTotal scaler0 in hAgree.
by rewrite hAgree linear0 hom_zeroE.
Qed.
End CurrentRepresentedPointTotal.
