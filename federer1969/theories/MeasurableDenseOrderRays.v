(** Federer (1969), 2.3.2(2), p. 73: all four tests with thresholds from an
    arbitrary dense subset. A sealed countable refinement reduces the test
    to the local order-dense-family theorems. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureAlmostUP
  MeasurableFunctionUP MeasurableFunctionBorel TopologicalBorel CountableOrderIntervals
  DenseOrderRefinementUP DenseOrderRefinementSealed MeasurableOrderRays
  MeasurableOrderRayVariants ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope order_scope.
Local Open Scope classical_set_scope.

(** Source for [measurable_dense_order_rays_iff]: supporting
    general order-topology form of the four dense-threshold tests
    in Federer 2.3.2(2), p. 73. The starting countable
    family only proves existence of a countable refinement inside D;
    the theorem does not require D itself to be countable. *)
Theorem measurable_dense_order_rays_iff (R : realType) (X : choiceType)
    disp (Y : orderTopologicalType disp) (J : countType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X Y)
    (d : J -> Y) (D : set Y) (y0 : Y) :
  is_order_dense_family d -> dense D -> D y0 ->
  measure_almost_everywhere mu (partial_function_domain f) ->
  (is_measure_measurable_function mu f <->
    forall t, D t -> measure_measurable mu (partial_function_preimage f [set y | y < t])) /\
  (is_measure_measurable_function mu f <->
    forall t, D t -> measure_measurable mu (partial_function_preimage f [set y | y <= t])) /\
  (is_measure_measurable_function mu f <->
    forall t, D t -> measure_measurable mu (partial_function_preimage f [set y | t < y])) /\
  (is_measure_measurable_function mu f <->
    forall t, D t -> measure_measurable mu (partial_function_preimage f [set y | t <= y])).
Proof.
move=> hd hD hy0 hdom.
pose e := @DenseOrderRefinement.value disp Y J d D y0 hd hD hy0.
have he := @DenseOrderRefinement.laws disp Y J d D y0 hd hD hy0.
have hed := dense_order_refinement_dense he.
have hem := dense_order_refinement_member he.
split.
- split.
  + move=> hf t ht; apply: (@measurable_function_open_preimage R X Y mu f hf); exact: order_strict_lower_ray_open.
  + move=> h; exact ((proj2 (@measurable_order_dense_rays_iff R X disp Y
      [the countType of (J * J)%type] mu hm f e hed hdom)) (fun j => h (e j) (hem j))).
- split.
  + split.
    * move=> hf t ht; apply: (@measurable_function_borel_preimage R X Y mu hm f hf).
      apply: closed_borel_set; exact: order_closed_lower_ray_closed.
    * move=> h; exact ((proj2 (@measurable_order_dense_closed_lower_rays_iff R X disp Y
        [the countType of (J * J)%type] mu hm f e hed hdom)) (fun j => h (e j) (hem j))).
  + split.
    * split.
      -- move=> hf t ht; apply: (@measurable_function_open_preimage R X Y mu f hf); exact: order_strict_upper_ray_open.
      -- move=> h; exact ((proj2 (@measurable_order_dense_upper_rays_iff R X disp Y
          [the countType of (J * J)%type] mu hm f e hed hdom)) (fun j => h (e j) (hem j))).
    * split.
      -- move=> hf t ht; apply: (@measurable_function_borel_preimage R X Y mu hm f hf).
         apply: closed_borel_set; exact: order_closed_upper_ray_closed.
      -- move=> h; exact ((proj2 (@measurable_order_dense_closed_upper_rays_iff R X disp Y
          [the countType of (J * J)%type] mu hm f e hed hdom)) (fun j => h (e j) (hem j))).
Qed.

(** Source for [measurable_extended_dense_rays_iff]: direct arbitrary
    dense-subset and four-comparison assertion following Federer 2.3.2(2),
    p. 73 D is any dense subset of the extended real line, exactly as
    printed, and may include either infinity. *)
Theorem measurable_extended_dense_rays_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X (extended_real_line R))
    (D : set (extended_real_line R)) :
  dense D -> measure_almost_everywhere mu (partial_function_domain f) ->
  (is_measure_measurable_function mu f <->
    forall t, D t -> measure_measurable mu (partial_function_preimage f [set y | (y < t)%E])) /\
  (is_measure_measurable_function mu f <->
    forall t, D t -> measure_measurable mu (partial_function_preimage f [set y | (y <= t)%E])) /\
  (is_measure_measurable_function mu f <->
    forall t, D t -> measure_measurable mu (partial_function_preimage f [set y | (t < y)%E])) /\
  (is_measure_measurable_function mu f <->
    forall t, D t -> measure_measurable mu (partial_function_preimage f [set y | (t <= y)%E])).
Proof.
move=> hD hd.
have hn : (@setT (extended_real_line R)) !=set0 by exists (0 : \bar R)%E.
have [y0 [_ hy0]] := hD setT hn openT.
exact (@measurable_dense_order_rays_iff R X _
  [the orderTopologicalType _ of order_topology (\bar R)] [the countType of (rat : Type)] mu hm f
  (fun q : rat => (ratr q : R)%:E) D y0 (@extended_rationals_order_dense R) hD hy0 hd).
Qed.
