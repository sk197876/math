(** Federer (1969), 2.3.2(2), p. 73: the strict lower-ray test can be
    replaced by upper rays or either closed ray. These supporting
    order-dense-family lemmas retain the actual partial domain when taking
    complements. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionPreimages MeasureUP
  MeasureAlmostUP MeasureFiniteClosure MeasureCountableClosure MeasurableFunctionUP
  MeasurableFunctionBorel CountableOrderIntervals MeasurableOrderRays TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope order_scope.
Local Open Scope classical_set_scope.

(** Source for [measurable_partial_preimage_complement_iff]:
    supporting complement step for the ray alternatives in Federer
    2.3.2(2), p. 73. Complements of inverse images are
    taken relative to the measurable partial domain. *)
Lemma measurable_partial_preimage_complement_iff (R : realType) (X Y : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X Y) (A : set Y) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  (measure_measurable mu (partial_function_preimage f A) <->
   measure_measurable mu (partial_function_preimage f (~` A))).
Proof.
move=> hd; have hD := @conull_partial_function_domain_measurable R X Y mu hm f hd.
have hc B : measure_measurable mu (partial_function_preimage f B) ->
    measure_measurable mu (partial_function_preimage f (~` B)).
  move=> hb; rewrite partial_function_preimage_complement.
  exact: (@measure_measurable_difference R X mu hm _ _ hD hb).
split; first exact: hc.
move=> ha; have h := hc _ ha; by rewrite setCK in h.
Qed.

(** Source for [measurable_order_dense_closed_lower_rays_iff]:
    supporting closed lower-ray alternative to the criterion in
    Federer 2.3.2(2), p. 73. Density represents each
    strict lower ray as a countable union of closed lower rays. *)
Theorem measurable_order_dense_closed_lower_rays_iff (R : realType) (X : choiceType)
    disp (Y : orderTopologicalType disp) (J : countType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X Y) (d : J -> Y) :
  is_order_dense_family d -> measure_almost_everywhere mu (partial_function_domain f) ->
  (is_measure_measurable_function mu f <->
   forall j, measure_measurable mu (partial_function_preimage f [set y | y <= d j])).
Proof.
move=> hd hdom; split.
- move=> hf j; apply: (@measurable_function_borel_preimage R X Y mu hm f hf).
  apply: closed_borel_set; exact: order_closed_lower_ray_closed.
- move=> hc; apply: (proj2 (@measurable_order_dense_rays_iff R X disp Y J mu hm f d hd hdom))=> j.
  have he : [set y | y < d j] = \bigcup_(k in [set k | d k < d j]) [set y | y <= d k].
    apply/seteqP; split=> y.
    + move=> hy; have [k [hyk hkj]] := hd _ _ hy; exists k=> //; exact: ltW hyk.
    + move=> [k hkj hyk]; exact: le_lt_trans hyk hkj.
  rewrite he partial_function_preimage_union.
  apply: (@measure_measurable_countable_union R X J mu hm _ _ (countableP _))=> k hk.
  exact: hc k.
Qed.

(** Source for [measurable_order_dense_closed_upper_rays_iff]:
    supporting closed upper-ray alternative in Federer 2.3.2(2),
    p. 73, obtained by complements of strict lower rays. *)
Theorem measurable_order_dense_closed_upper_rays_iff (R : realType) (X : choiceType)
    disp (Y : orderTopologicalType disp) (J : countType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X Y) (d : J -> Y) :
  is_order_dense_family d -> measure_almost_everywhere mu (partial_function_domain f) ->
  (is_measure_measurable_function mu f <->
   forall j, measure_measurable mu (partial_function_preimage f [set y | d j <= y])).
Proof.
move=> hd hdom; split.
- move=> hf j; apply: (@measurable_function_borel_preimage R X Y mu hm f hf).
  apply: closed_borel_set; exact: order_closed_upper_ray_closed.
- move=> hc; apply: (proj2 (@measurable_order_dense_rays_iff R X disp Y J mu hm f d hd hdom))=> j.
  have he : ~` [set y | y < d j] = [set y | d j <= y].
    apply/seteqP; split=> y; rewrite /= leNgt; by move/negP.
  apply: (proj2 (@measurable_partial_preimage_complement_iff R X Y mu hm f _ hdom)).
  rewrite he; exact: hc j.
Qed.

(** Source for [measurable_order_dense_upper_rays_iff]: supporting
    strict upper-ray alternative in Federer 2.3.2(2), p. 73,
    obtained by complements of closed lower rays. *)
Theorem measurable_order_dense_upper_rays_iff (R : realType) (X : choiceType)
    disp (Y : orderTopologicalType disp) (J : countType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X Y) (d : J -> Y) :
  is_order_dense_family d -> measure_almost_everywhere mu (partial_function_domain f) ->
  (is_measure_measurable_function mu f <->
   forall j, measure_measurable mu (partial_function_preimage f [set y | d j < y])).
Proof.
move=> hd hdom; split.
- move=> hf j; apply: (@measurable_function_open_preimage R X Y mu f hf); exact: order_strict_upper_ray_open.
- move=> hc; apply: (proj2 (@measurable_order_dense_closed_lower_rays_iff R X disp Y J mu hm f d hd hdom))=> j.
  have he : ~` [set y | y <= d j] = [set y | d j < y].
    apply/seteqP; split=> y; rewrite /= ltNge; by move/negP.
  apply: (proj2 (@measurable_partial_preimage_complement_iff R X Y mu hm f _ hdom)).
  rewrite he; exact: hc j.
Qed.
