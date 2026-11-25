(** Federer (1969), 4.1.2, p. 347: the
    original Lebesgue-point hypothesis survives a total
    extension which preserves every originally defined value.
    The subset means retain their exact partial
    quotient graphs, including undefined denominators. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionExtensionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality MeasureDensityTransfer MeasureIntegralAlmostEquality
  MeasureMeanFunction MeasurableDistanceTo MeasureLebesgueSet CoveringLimitGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [measure_mean_almost_equal_graph]: actual subset
    means are invariant under null modification,
    supporting Federer 4.1.2, p. 347, by
    2.4.3(2), p. 81, and 2.9.8, p. 156. *)
Lemma measure_mean_almost_equal_graph (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu)
    (f g:partial_function X (extended_real_line R)):
  measure_almost_equal mu f g ->forall S z,
    partial_function_graph (measure_mean_function mu f) S z <->
    partial_function_graph (measure_mean_function mu g) S z.
Proof.
move=>he S z.
have hRestricted:=@zero_extension_almost_equal R X (extended_real_line R) mu hm 0 S f g he.
have hReverse:=measure_almost_equal_sym hRestricted.
split.
- move=>[a [hI hDivide]]; exists a; split=>//.
  exact:(measure_integral_almost_equal hm hI hRestricted).
- move=>[a [hI hDivide]]; exists a; split=>//.
  exact:(measure_integral_almost_equal hm hI hReverse).
Qed.

(** Source for [partial_distance_almost_equal]: distance to a
    fixed vector is unchanged almost everywhere under
    the original null extension, supporting Federer 4.1.2,
    p. 347, by 2.9.9, p. 157. *)
Lemma partial_distance_almost_equal (R:realType) (X:choiceType) (Y:metricType R)
    (mu:set X->\bar R) (hm:is_measure mu) (f g:partial_function X Y) (y:Y):
  measure_almost_equal mu f g ->
  measure_almost_equal mu (partial_distance_to f y) (partial_distance_to g y).
Proof.
move=>he; apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ he)=>x [z [hf hg]].
exists (mdist z y)%:E; split; exists z; by split.
Qed.

(** Source for [lebesgue_point_total_extension]: every originally
    defined Lebesgue point remains one after extension
    to a measurable total representative, supporting
    Federer 4.1.2, p. 347. Agreement at
    the particular point is retained, in addition
    to almost-everywhere agreement. *)
Theorem lebesgue_point_total_extension (R:realType) (X Y:metricType R)
    (mu:set X->\bar R) (hm:is_measure mu) (V:X->set X->Prop)
    (f:partial_function X Y) (F:X->Y):
  is_partial_function_total_extension f F ->
  measure_almost_equal mu f (partial_function_total F) ->
  forall x,measure_lebesgue_set mu V f x ->
    measure_lebesgue_set mu V (partial_function_total F) x.
Proof.
move=>hExt he x [y [hy hLimit]].
exists y; split; first exact:(@hExt x y hy).
have hDistance:=@partial_distance_almost_equal R X Y mu hm f (partial_function_total F) y he.
have hMeans:=@measure_mean_almost_equal_graph R X mu hm
  (partial_distance_to f y) (partial_distance_to (partial_function_total F) y) hDistance.
exact:(@covering_limit_graph_equivalent R X V _ _
  (fun _ S _ z=>hMeans S z) x 0).1 hLimit.
Qed.
