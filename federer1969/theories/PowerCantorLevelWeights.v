(** Federer (1969), 2.10.29, p. 193: equal-width square covers have constant
    total power cost. The sum of the m-th powers of level lengths is one by
    the conserved c*t^m root cost. Multiplication of these two sums gives
    the square-cover budget, retaining repeated indices. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground RealPower CompactIntervalGauge MetricDiameter MetricDiameterReal
  PowerConcaveIntervalGauge EqualCostIntervalTreeUP EqualCostIntervalTreeLaws SpecialIntervalFamilyUP
  NonnegativeSum NonnegativeSumSupport NonnegativeSumProduct NonnegativeSumExtendedScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [power_cantor_level_weight_sum]: supporting
    sum of m-th power lengths equals one
    in the square-cover computation of 2.10.29,
    p. 193. The root is the actual [0,1]. *)
Lemma power_cantor_level_weight_sum (R : realType) (c m : R) (J : compact_real_intervals R) n H :
  (0<c)%R -> (0<m)%R -> (m<1)%R ->
  val J=(`[0%R,1%R] : set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>(c*real_power t m)%R) J n H ->
  forall j, (\sum_(S <- H j) real_power
    (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S))) m= 1)%R.
Proof.
move=> hc hm hm1 hJ ht j.
have hg := power_concave_interval_gauge hc hm hm1.
have hsum := special_interval_cost_sum (@equal_cost_tree_level_special R _ hg J n H ht j).
have hc0 : c!=0%R by rewrite gt_eqF.
have hroot : concave_interval_cost (fun t=>(c*real_power t m)%R) (val J)=c.
  by rewrite hJ (concave_interval_cost_segment _ ler01) subr0 real_power_one_base mulr1.
rewrite hroot /concave_interval_cost -mulr_sumr in hsum.
apply: (mulfI hc0); by rewrite mulr1 -hsum.
Qed.

(** Source for [power_cantor_level_numerical_weight_sum]: supporting
    same finite cost identity in the abstract
    numerical-sum notation used for cover infima
    in 2.10.29, p. 193. *)
Lemma power_cantor_level_numerical_weight_sum (R : realType) (c m : R) (J : compact_real_intervals R) n H :
  (0<c)%R -> (0<m)%R -> (m<1)%R ->
  val J=(`[0%R,1%R] : set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>(c*real_power t m)%R) J n H ->
  forall j, nonnegative_sum [set S | S \in H j] (fun S=>(real_power
    (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S))) m)%:E)= 1.
Proof.
move=> hc hm hm1 hJ ht j.
rewrite nonnegative_sum_finite; last by move=> S _; rewrite lee_fin; exact: real_power_nonnegative.
by rewrite sumEFin (@power_cantor_level_weight_sum R c m J n H hc hm hm1 hJ ht j).
Qed.

(** Source for [normalised_weights_product_budget]: supporting
    product of the two level cost sums in
    2.10.29, p. 193. This abstract identity
    is a consequence of 2.1.1(6),(10),
    pp. 52–53, with arbitrary nonnegative weights. *)
Lemma normalised_weights_product_budget (R : realType) (I J : choiceType)
    (D : set I) (F : set J) (u : I -> \bar R) (v : J -> \bar R) (C : \bar R) :
  0<=C -> (forall i, D i -> 0<=u i) -> (forall j, F j -> 0<=v j) ->
  nonnegative_sum D u= 1 -> nonnegative_sum F v= 1 ->
  nonnegative_sum (D `*` F) (fun p=>C*u p.1*v p.2)=C.
Proof.
move=> hC hu hv hD hF.
have hnn p : (D `*` F) p -> 0<=C*u p.1*v p.2.
  move=> [hpD hpF]; exact: mule_ge0 (mule_ge0 hC (hu _ hpD)) (hv _ hpF).
rewrite (nonnegative_sum_product_first hnn).
have he : nonnegative_sum D (fun i=>nonnegative_sum F (fun j=>C*u i*v j))=
    nonnegative_sum D (fun i=>C*u i).
  apply: nonnegative_sum_ext=> i hi.
  have hCu : 0<=C*u i := mule_ge0 hC (hu i hi).
  by rewrite (@nonnegative_sum_extended_scale R J F v (C*u i) hCu hv) hF mule1.
by rewrite he (@nonnegative_sum_extended_scale R I D u C hC hu) hD mule1.
Qed.
