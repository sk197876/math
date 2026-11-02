(** Finite integral means on the small bounded cells in Federer (1969),
    2.9.8, p. 156. Positive finite denominators and local absolute
    integrability give finite means of both parts; their difference is the
    signed mean. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealConventions PartialFunctionUP
  MeasureUP MeasurableFunctionUP MeasureSubsetIntegral MeasureMeanFunction
  CoveringFamilyUP LocalAbsoluteIntegrability PartialFunctionIntegralParts MeasureUpperIntegralPositivePart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_measure_mean_value]: supporting
    finite arithmetic for the integral quotient in
    Federer 2.9.8, p. 156. A finite
    subset integral and a positive finite denominator
    give exactly the ordinary real quotient. *)
Lemma finite_measure_mean_value (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (f : partial_function X (extended_real_line R)) S (a b : R) :
  is_measure_subset_integral phi S f a%:E -> phi S=b%:E -> (0<b)%R ->
  partial_function_graph (measure_mean_function phi f) S (a/b)%R%:E.
Proof.
move=> hi hb hbp; exists a%:E; split=> //.
have hbpE : 0<b%:E by rewrite lte_fin.
have hbfin : b%:E \is a fin_num by rewrite fin_numE.
rewrite /extended_divide hb (gt_eqF hbpE) hbfin orbT /=.
by rewrite inver (gt_eqF hbp) -EFinM.
Qed.

(** Source for [finite_measure_mean_part_values]: supporting exact
    difference of finite means in the signed case of Federer 2.9.8, p. 156
    The same finite denominator is used for both part integrals and their
    signed difference. *)
Lemma finite_measure_mean_part_values (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (f : partial_function X (extended_real_line R)) S :
  is_measure phi -> is_measure_measurable_function phi f -> is_locally_absolutely_integrable phi f ->
  metric_set_bounded S -> measure_measurable phi S -> 0<phi S -> phi S \is a fin_num ->
  exists p n : R,
    partial_function_graph (measure_mean_function phi (partial_extended_function_positive_part f)) S p%:E /\
    partial_function_graph (measure_mean_function phi (partial_extended_function_negative_part f)) S n%:E /\
    partial_function_graph (measure_mean_function phi f) S (p-n)%R%:E.
Proof.
move=> hm hf hlocal hSb hSm hSp hSf.
have [a [b [ha [hb hab]]]] := @locally_absolutely_integrable_part_values R X phi f hm hf hlocal S hSb hSm.
pose d := fine (phi S).
have hed : phi S=d%:E by rewrite /d fineK.
have hdp : (0<d)%R by move: hSp; rewrite hed lte_fin.
have hpa := @finite_measure_mean_value R X phi (partial_extended_function_positive_part f) S a d ha hed hdp.
have hnb := @finite_measure_mean_value R X phi (partial_extended_function_negative_part f) S b d hb hed hdp.
have hfab := @finite_measure_mean_value R X phi f S (a-b)%R d hab hed hdp.
exists (a/d)%R,(b/d)%R; split=> //; split=> //.
by rewrite mulrBl in hfab.
Qed.
