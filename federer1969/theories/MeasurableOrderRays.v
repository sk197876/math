(** Federer (1969), 2.3.2(2), p. 73: the countable dense-ray criterion,
    proved from interval bases and local measurable-set laws. This general
    order-topology lemma supports the printed extended-real special case. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureFiniteClosure MeasureCountableClosure MeasureAlmostUP
  MeasurableFunctionUP MeasurableFunctionBorel CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope order_scope.
Local Open Scope classical_set_scope.

(** Source for [partial_preimage_intersection]: supporting inverse-
    image intersection law for the ray criterion in Federer
    2.3.2(2), p. 73, including partial domains. *)
Lemma partial_preimage_intersection (X Y : Type) (f : partial_function X Y) (A B : set Y) :
  partial_function_preimage f (A `&` B) =
  partial_function_preimage f A `&` partial_function_preimage f B.
Proof.
apply/seteqP; split=> x.
- move=> [y [hy [ha hb]]]; split; by exists y.
- move=> [[y [hy ha]] [z [hz hb]]]; exists y; split=> //; split=> //.
  have he : y = z := partial_function_single_valued hy hz.
  by rewrite he.
Qed.

(** Source for [measurable_order_dense_rays_iff]: supporting
    countable order-dense-ray form of Federer 2.3.2(2), p. 73.
    The conull domain is explicit; strict lower rays generate the
    measurable inverse images of every open interval neighborhood. *)
Theorem measurable_order_dense_rays_iff (R : realType) (X : choiceType)
    disp (Y : orderTopologicalType disp) (J : countType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X Y) (d : J -> Y) :
  is_order_dense_family d -> measure_almost_everywhere mu (partial_function_domain f) ->
  (is_measure_measurable_function mu f <->
   forall j, measure_measurable mu (partial_function_preimage f [set y | y < d j])).
Proof.
move=> hd hdom; split.
- move=> hf j; apply: (@measurable_function_open_preimage R X Y mu f hf).
  exact: order_strict_lower_ray_open.
- move=> hl.
  have hD := @conull_partial_function_domain_measurable R X Y mu hm f hdom.
  have hge j : measure_measurable mu (partial_function_preimage f [set y | d j <= y]).
    have he : [set y | d j <= y] = ~` [set y | y < d j].
      apply/seteqP; split=> y; rewrite /= leNgt; by move/negP.
    rewrite he partial_function_preimage_complement.
    exact: (@measure_measurable_difference R X mu hm _ _ hD (hl j)).
  have hgt j : measure_measurable mu (partial_function_preimage f [set y | d j < y]).
    have he : [set y | d j < y] = \bigcup_(k in [set k | d j < d k]) [set y | d k <= y].
      apply/seteqP; split=> y.
      - move=> hy; have [k [hjk hky]] := hd _ _ hy; exists k=> //; exact: ltW hky.
      - move=> [k hjk hky]; exact: lt_le_trans hjk hky.
    rewrite he partial_function_preimage_union.
    apply: (@measure_measurable_countable_union R X J mu hm _ _ (countableP _))=> k hk.
    exact: hge k.
  have hb c : measure_measurable mu (partial_function_preimage f (order_family_interval d c)).
    have he : order_family_interval d c =
      (if c.1 is Some j then [set y | d j < y] else setT) `&`
      (if c.2 is Some j then [set y | y < d j] else setT) by case: c=> [[j|] [k|]].
    rewrite he partial_preimage_intersection; clear he.
    apply: (@measure_measurable_intersection R X mu hm).
    + case: c=> [[j|] [k|]] /=;
        first [exact: hgt | by rewrite partial_function_preimage_whole].
    + case: c=> [[j|] [k|]] /=;
        first [exact: hl | by rewrite partial_function_preimage_whole].
  constructor=> // V ho.
  pose D := [set c : option J * option J | order_family_interval d c `<=` V].
  have he : V = \bigcup_(c in D) order_family_interval d c.
    apply/seteqP; split=> x.
    + move=> hx; have [c [hc hcv]] := @order_family_intervals_refine disp Y J d hd V ho x hx.
      by exists c.
    + by move=> [c hc hx]; exact: hc hx.
  rewrite he partial_function_preimage_union.
  apply: (@measure_measurable_countable_union R X _ mu hm _ _ (countableP _))=> c hc.
  exact: hb c.
Qed.
