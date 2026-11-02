(** Federer (1969), 2.5.7, p. 98: use of the dual tests from 2.4.16, pp.
    89–90, after restricting L to total domains by erratum p. 2, book p. 98
    line 10. These supporting graph-invariance lemmas transfer the full test
    membership, including countably measurable support; they do not identify
    functions merely by norm value. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialFunctionGraphEquivalence
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableGraphEquivalence CountablyMeasurableUP
  MeasureLpNormAlmostEquality MeasureEssentialNormComparison MeasureExponentDomain MeasureDualTestUP TotalScalarLpUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [scalar_exponent_norm_graph_equivalent]: supporting
    norm invariance for the dual tests in Federer 2.5.7, p. 98,
    from the definitions in 2.4.12, p. 86. The exponent
    and measurability hypotheses are retained at finite p. *)
Lemma scalar_exponent_norm_graph_equivalent (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p
    (u v : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  1 <= p -> is_measure_measurable_function mu u ->
  (forall x y, partial_function_graph u x y <-> partial_function_graph v x y) ->
  measure_exponent_norm mu u p=measure_exponent_norm mu v p.
Proof.
move=> hp hu he.
have hv := @measurable_function_graph_equivalent R X _ mu u v he hu.
case: p hp=> [p| |] hp; last by [].
- apply: (@measure_lp_norm_almost_equal R X R^o (fun y : R => `|y|%R)
    (scalar_absolute_value_norm R) mu hm p u v hp hu hv).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hu)).
  move=> x [y hy]; exists y; split=> //; exact: (he x y).1 hy.
- exact: (@measure_essential_norm_graph_equivalent R X _ mu hm (fun y : R => `|y|%R) u v he).
Qed.

(** Source for [countable_scalar_support_graph_equivalent]: supporting
    preservation of the full support condition of 2.3.4, p. 76, in the tests
    used by Federer 2.5.7, p. 98 *)
Lemma countable_scalar_support_graph_equivalent (R : realType) (X : choiceType)
    (mu : set X -> \bar R)
    (u v : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (forall x y, partial_function_graph u x y <-> partial_function_graph v x y) ->
  is_countably_measure_measurable_function mu (0%R : real_norm_metric_space (scalar_absolute_value_norm R)) u ->
  is_countably_measure_measurable_function mu (0%R : real_norm_metric_space (scalar_absolute_value_norm R)) v.
Proof.
move=> he hu; constructor.
- exact: (@measurable_function_graph_equivalent R X _ mu u v he (countably_measurable_function_measurable hu)).
- rewrite /partial_function_nonzero_locus -(partial_function_equivalent_preimages he).
  exact: countably_measurable_function_locus hu.
Qed.

(** Source for [finite_unit_test_total_transfer]: the full finite
    dual-test ball from 2.4.16, p. 89, transferred to
    the total-domain space of Federer 2.5.7, p. 98.
    Norm <= 1 follows erratum p. 2, book p. 89 line 19. *)
Lemma finite_unit_test_total_transfer (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (u : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) (v : X -> R) :
  is_finite_lp_unit_test mu p u ->
  (forall x y, partial_function_graph u x y <-> partial_function_graph (total_scalar_function v) x y) ->
  total_scalar_lp mu p%:E v /\ total_scalar_lp_norm mu p%:E v <= 1.
Proof.
move=> [hu hb] he.
have hv := @measurable_function_graph_equivalent R X _ mu u (total_scalar_function v) he hu.2.1.1.
have hn := @scalar_exponent_norm_graph_equivalent R X mu hm p%:E u (total_scalar_function v) hu.1 hu.2.1.1 he.
split; last by rewrite /total_scalar_lp_norm -hn.
split; first exact: hu.1.
split; first exact: hv.
split; first by rewrite /total_scalar_lp_norm -hn; exact: hu.2.2.1.
exact: (@countable_scalar_support_graph_equivalent R X mu u (total_scalar_function v) he hu.2.2.2).
Qed.

(** Source for [infinity_unit_test_total_transfer]: the infinity
    dual-test ball from 2.4.16, p. 89, on the corrected
    total-domain space of Federer 2.5.7, p. 98.
    Countably measurable support is preserved at this endpoint as well. *)
Lemma infinity_unit_test_total_transfer (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) (v : X -> R) :
  is_linfinity_unit_test mu u ->
  (forall x y, partial_function_graph u x y <-> partial_function_graph (total_scalar_function v) x y) ->
  total_scalar_lp mu +oo v /\ total_scalar_lp_norm mu +oo v <= 1.
Proof.
move=> [hu hb] he.
have hv := @measurable_function_graph_equivalent R X _ mu u (total_scalar_function v) he hu.1.1.
have hn := @scalar_exponent_norm_graph_equivalent R X mu hm +oo u (total_scalar_function v) (leey _) hu.1.1 he.
split; last by rewrite /total_scalar_lp_norm -hn.
split; first exact: leey.
split; first exact: hv.
split; first by rewrite /total_scalar_lp_norm -hn; exact: hu.2.1.
exact: (@countable_scalar_support_graph_equivalent R X mu u (total_scalar_function v) he hu.2.2).
Qed.
