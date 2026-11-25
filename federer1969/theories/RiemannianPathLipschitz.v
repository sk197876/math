(** Federer (1969), 3.2.46, p. 282: Lipschitz maps
    for the original Riemannian path distances satisfy
    the hypotheses of the local finite-carrier arguments.
    The cap is technical; it does not replace the
    original metric or require globally finite distances. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RiemannianTensorUP RiemannianMetricCarrier RiemannianDistance RiemannianDistanceBasic
  ExtendedRealUnitCap ExtendedRealUnitCapOrder ExtendedRealUnitCapScaling
  RiemannianLocalGlobalCoordinates LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_riemannian_path_lipschitz]: the ordinary
    Lipschitz condition using the actual original curve-distance
    infima, supporting 3.2.46, p. 282. A positive finite
    bound can always be used in the usual Lipschitz class.
    Extended component distances remain explicit and no
    coordinate or capped-metric bound is among the laws. *)
Definition is_riemannian_path_lipschitz (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) :=
  exists c : R, 0<c /\ forall x y,
    (@riemannian_distance R n B h (val (f x)) (val (f y)) <=
      c%:E*@riemannian_distance R m A g (val x) (val y))%E.

(** Source for [riemannian_path_lipschitz_carrier]: the
    original-rho Lipschitz condition gives a finite-carrier
    Lipschitz bound max(1,c), supporting the localization
    in 3.2.46, p. 282. This is proved by the
    actual scalar cap laws, including infinite distances;
    no extra hypothesis is imposed on the original map. *)
Lemma riemannian_path_lipschitz_carrier (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) :
  is_riemannian_path_lipschitz f -> is_metric_lipschitz setT f.
Proof.
move=> [c [hc hBound]].
have hC : 0<Num.max 1 c by apply: lt_le_trans ltr01 _; rewrite le_max lexx.
exists (Num.max 1 c); split; first exact hC; split; first exact: ltW hC.
move=> x y _ _; rewrite !riemannian_metric_distanceE.
have hSource := @riemannian_distance_nonnegative R m A g (val x) (val y).
have hTarget := @riemannian_distance_nonnegative R n B h (val (f x)) (val (f y)).
have hProduct : (0<=c%:E*@riemannian_distance R m A g (val x) (val y))%E.
  apply: mule_ge0; last exact hSource; rewrite lee_fin; exact: ltW hc.
apply: le_trans (@extended_real_unit_cap_monotone R _ _ hTarget hProduct (hBound x y)) _.
exact: extended_real_unit_cap_positive_scale_bound hc hSource.
Qed.

(** Source for [riemannian_path_map_local_coordinates]:
    every map Lipschitz for the actual original path
    distances has local globally Euclidean Lipschitz coordinate
    representatives inside the original target chart, supporting
    3.2.46, p. 282. The original source patch and
    all actual map values there are retained. *)
Corollary riemannian_path_map_local_coordinates (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) :
  is_riemannian_path_lipschitz f -> forall a : riemannian_metric_space hg,
    exists U : set (inner_metric_space (@euclidean_inner_productP R m)),
    exists K : R, exists F : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n),
      open U /\ U (val a) /\ U `<=` A /\ 0<K /\
      is_metric_lipschitz_bound setT F K /\ (forall z, B (F z)) /\
      forall x : riemannian_metric_space hg, U (val x) -> F (val x)=val (f x).
Proof.
move=> hLip.
exact (@riemannian_local_global_coordinate_representative R m n A B g h hg hh f
  (@riemannian_path_lipschitz_carrier R m n A B g h hg hh f hLip)).
Qed.
