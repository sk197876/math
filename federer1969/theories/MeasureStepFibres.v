(** Federer (1969), 2.4.1, pp. 80–81: the countable families of level sets
    partition almost all of X. Source context: MeasureStepFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP MeasureUP MeasureBasic
  MeasureFiniteClosure MeasureAlmostUP MeasureNullModification MeasureCountableAdditivity
  MeasurableFunctionUP MeasurableFunctionBorel TopologicalBorel MeasureStepFunctionUP
  NonnegativeSum NonnegativeSumSupport NonnegativeSumRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_real_fibre]: supporting measurability
    of the level sets in Federer 2.4.1, pp. 80–81. *)
Lemma measurable_real_fibre (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u : partial_function X (real_line_metric R)) :
  is_measure_measurable_function mu u -> forall y : R,
    measure_measurable mu (partial_function_preimage u [set y]).
Proof.
move=> hu y; apply: (@measurable_function_borel_preimage R X (real_line_metric R) mu hm u hu).
apply: closed_borel_set; apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
Qed.

(** Source for [partial_fibre_outside_range]: level sets outside
    the image are empty, supporting the sums over all real values
    in Federer 2.4.1, pp. 80–81. *)
Lemma partial_fibre_outside_range (X Y : Type) (u : partial_function X Y) y :
  ~ partial_function_range u y -> partial_function_preimage u [set y] = set0.
Proof.
move=> hn; apply/seteqP; split; last by move=> x [].
move=> x [z [hz he]]; apply: hn; exists x; by rewrite -he.
Qed.

(** Source for [measure_countable_range_fibre_partition]: the
    common-refinement row and column sum identity in Federer 2.4.1, p. 81
    The null complement of the partial function's domain is included
    explicitly in the measure comparison. *)
Theorem measure_countable_range_fibre_partition (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u : partial_function X (real_line_metric R)) (A : set X) :
  is_measure_measurable_function mu u -> countable (partial_function_range u) ->
  measure_measurable mu A ->
  nonnegative_sum setT (fun y : R => mu (A `&` partial_function_preimage u [set y])) = mu A.
Proof.
move=> hu hc hA; pose D := partial_function_range u.
pose F (y : R) := A `&` partial_function_preimage u [set y].
have hF y : D y -> measure_measurable mu (F y).
  move=> _; exact (@measure_measurable_intersection R X mu hm A _ hA (@measurable_real_fibre R X mu hm u hu y)).
have hd y z : D y -> D z -> y != z -> forall x, F y x -> F z x -> False.
  move=> hy hz hne x [_ [a [ha ea]]] [_ [b [hb eb]]].
  have hab := partial_function_single_valued ha hb.
  apply: (negP hne); apply/eqP; by rewrite -ea -eb.
have he : (\bigcup_(y in D) F y) = A `&` partial_function_domain u.
  apply/seteqP; split=> x.
  - move=> [y _ [hx [z [hz _]]]]; split=> //; by exists z.
  - move=> [hx [y hy]]; exists y; first by exists x.
    split=> //; exists y; by split.
have hmA : mu (A `&` partial_function_domain u) = mu A.
  apply: (@measure_null_modification_value R X mu hm _ _ (~` partial_function_domain u)
    (measurable_function_domain hu)).
  move=> x hn; have hx : partial_function_domain u x by apply: contrapT=> h; exact: hn.
  split; first by move=> [ha _].
  move=> ha; by split.
have hs := @measure_countable_disjoint_additivity R X R mu hm D F hc hF hd.
rewrite he hmA in hs; rewrite hs.
have hz y : ~ D y -> F y = set0.
  move=> hy; rewrite /F (partial_fibre_outside_range hy); exact: setI0.
have hpos y : (@setT R) y -> 0 <= mu (F y) by move=> _; exact: measure_nonnegative.
have hzero : nonnegative_sum (setT `\` D) (fun y => mu (F y)) = 0.
  apply: nonnegative_sum_zero=> y [_ hy]; rewrite (hz y hy); exact: measure_empty.
by rewrite (@nonnegative_sum_split R R setT D (fun y => mu (F y)) hpos) setTI hzero adde0.
Qed.
