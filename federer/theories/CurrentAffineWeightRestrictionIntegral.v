(** Federer (1969), 4.1.13, pp. 369–370: the exact
    affine weights and their original variation integrals
    survive restriction to a support neighbourhood. Actual
    derivative locality and the proved measure transport
    retain the original rho and both infinite endpoints. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanHomOperator OperatorNormUP OperatorNormSealed CurrentDomain CurrentSpaces
  CurrentMapDifferential CurrentMapDifferentialOpenRestriction CurrentIntegrationCriterion
  CurrentOpenRestriction CurrentOpenRestrictionVariation NormalisedCurrentSealed
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentAffineWeightRestrictionIntegral.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation Op := (@euclidean_operator_norm R n nu).
Variables W U:set X.
Hypothesis hW:forall x,W x->norm_domain_interior NX W x.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hWU:forall x,W x->U x.
Variables f g:X->Y.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hg:norm_class_all_orders hNX hNY U g.
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Hypothesis hSupport:@current_support R h2 n U hU m T `<=` W.
Local Notation S := (@current_open_restriction R h2 n m W U hW hU hWU T).
Hypothesis hSmall:@is_integration_representable_current R h2 n m W hW S.
Local Notation WT := (current_domain R n W).
Local Notation UT := (current_domain R n U).
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation muW := (@NormalisedCurrent.measure R h2 n m W hW S hSmall).
Local Notation inc := (@current_open_domain_inclusion R n W U hWU).
Local Notation WeightU := (fun k (x:UT)=>NY (g (set_val x)-f (set_val x))*
  (Num.max (Op (@current_map_differential R n nu U f (set_val x)))
    (Op (@current_map_differential R n nu U g (set_val x))))^+k).
Local Notation WeightW := (fun k (x:WT)=>NY (g (set_val x)-f (set_val x))*
  (Num.max (Op (@current_map_differential R n nu W f (set_val x)))
    (Op (@current_map_differential R n nu W g (set_val x))))^+k).

(** Source for [current_affine_restricted_weight_identity]: the
    original weights |g-f|rho^k on the two open sources
    agree under their unchanged-point inclusion, by locality
    in 3.1.1, pp. 209–210, supporting Federer 4.1.13,
    pp. 369–370. Every natural exponent is retained. *)
Lemma current_affine_restricted_weight_identity k:
  WeightW k=(fun x:WT=>WeightU k (inc x)).
Proof.
apply:funext=>x.
rewrite current_open_domain_inclusion_value.
rewrite (@current_map_differential_open_restriction R n nu W U hW hWU f hf
  (set_val x) (set_valP x)).
by rewrite (@current_map_differential_open_restriction R n nu W U hW hWU g hg
  (set_val x) (set_valP x)).
Qed.

(** Source for [current_affine_restricted_weight_integral_iff]: the
    exact original rho-weighted variation integrals are unchanged
    by the source-neighbourhood replacement in Federer 4.1.13,
    pp. 369–370. No finite-integral or positivity premise is added. *)
Theorem current_affine_restricted_weight_integral_iff k a:
  is_measure_integral muW (real_total_integrand (WeightW k)) a<->
  is_measure_integral mu (real_total_integrand (WeightU k)) a.
Proof.
have h:=@current_neighbourhood_variation_total_integral_iff R h2 n m
  W U hW hU hWU T hT hSupport hSmall (WeightU k) a.
by rewrite -current_affine_restricted_weight_identity in h.
Qed.

(** Source for [current_affine_restricted_weight_lower_value]: the
    actual affine mass integral on the smaller source has the
    original-domain lower-integral value in Federer 4.1.13,
    pp. 369–370. Its given integral statement, rather
    than an extra integrability hypothesis on the original source,
    supplies the comparison. *)
Theorem current_affine_restricted_weight_lower_value k a:
  is_measure_integral muW (real_total_integrand (WeightW k)) a->
  a=measure_lower_integral mu (real_total_integrand (WeightU k)).
Proof.
move=>hIntegral.
have hOriginal:=(current_affine_restricted_weight_integral_iff k a).1 hIntegral.
exact:(measure_lower_integral_unique hOriginal.2.2
  (measure_lower_integral_specification mu (real_total_integrand (WeightU k)))).
Qed.
End CurrentAffineWeightRestrictionIntegral.
