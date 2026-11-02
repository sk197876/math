(** Federer (1969), 2.2.15, p. 70: Borel maps into a metric space form a
    Baire class, by the open- preimage formula from 2.3.2(6), pp. 73–74. All
    Borel operations are derived from the local generated-family laws. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals topology.
From Federer Require Import BorelFunctionUP BaireFunctionUP PointwiseLimit
  PointwiseOpenPreimage MetricSetDistanceSealed TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_functions_pointwise_closed]: direct
    assertion that Borel functions form a Baire class in Federer
    2.2.15, p. 70. The proof uses the countable
    unions and tail intersections in 2.3.2(6), p. 74,
    with no separability premise on the metric target. *)
Theorem borel_functions_pointwise_closed (R : realType) (X : topologicalType) (Y : metricType R) :
  is_baire_class (@is_borel_function X Y).
Proof.
move=> f g hf hlim U ho.
case: (pselect ((~` U) !=set0))=> [hn|hn].
- pose d := @MetricSetDistance.value R Y (~` U) hn.
  have hd := @MetricSetDistance.laws R Y (~` U) hn.
  rewrite (@pointwise_open_preimage_formula R X Y f g U d hd ho hlim).
  apply: borel_set_countable_union (countableP setT) _=> i _.
  apply: borel_set_countable_union (countableP setT) _=> N _.
  apply: borel_set_countable_intersection (countableP _) _ _.
  + exists N; exact: leqnn.
  + move=> n hnN; exact: hf n _ (metric_open_inner_open hd i).
- have he : U = setT.
    apply/seteqP; split=> [y hy|y _]; first exact Logic.I.
    apply: contrapT=> hy; apply: hn; by exists y.
  rewrite he preimage_setT; exact: open_borel_set openT.
Qed.
