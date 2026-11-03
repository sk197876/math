(** Federer (1969), 3.2.42, printed p. 278:
    both actual outer and inner boundary-layer estimates in
    ambient dimensions at least two, including empty sources
    and empty cores. The dimension-one nonempty cases are
    supplied separately; their zero exponent is not silently
    evaluated on an empty core. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanBallVolume RealPower MetricOpenThickening MetricOpenThickeningClosure
  OuterBoundaryLayerVolume InnerBoundaryLayerVolume MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_2_42]: direct pair of boundary-layer
    inequalities in Federer 3.2.42, p. 278, for n=k+2.
    Both displayed volume powers have positive exponents,
    so zero volumes, empty original sets and empty inner
    cores are included. Only the actual closure volume is
    finite; S may be nonmeasurable and unbounded. The strip
    and core identities recover the printed distance notation. *)
Theorem federer_3_2_42 (R:realType) k
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+2))) (r:R):
  (@euclidean_lebesgue_measure R k.+2 (closure S) < +oo)%E ->0<r ->
  (((k.+2)%:R*real_power (euclidean_unit_ball_volume R k.+2) ((k.+2)%:R)^-1*
    real_power (fine (@euclidean_lebesgue_measure R k.+2 (closure S)))
      ((k.+1)%:R/(k.+2)%:R))%:E<=
    @euclidean_lebesgue_measure R k.+2
      (metric_open_thickening S r `\` closure S)*r^-1%:E)%E /\
  (((k.+2)%:R*real_power (euclidean_unit_ball_volume R k.+2) ((k.+2)%:R)^-1*
    real_power (fine (@euclidean_lebesgue_measure R k.+2
      (~`metric_open_thickening (~`S) r))) ((k.+1)%:R/(k.+2)%:R))%:E<=
    @euclidean_lebesgue_measure R k.+2
      (interior S `\` (~`metric_open_thickening (~`S) r))*r^-1%:E)%E.
Proof.
move=>hFinite hr.
pose E:=inner_metric_space (@euclidean_inner_productP R k.+2).
pose mu:=@euclidean_lebesgue_measure R k.+2.
have hm:=euclidean_lebesgue_is_measure R k.+2.
have hp:0<((k.+1)%:R/(k.+2)%:R:R) by rewrite divr_gt0 ?ltr0n.
have hpNe:((k.+1)%:R/(k.+2)%:R:R)!=0 by rewrite (gt_eqF hp).
have hInverse:0<=r^-1 by rewrite invr_ge0; exact:ltW hr.
have hZero (Z Y:set E):mu Z=0%E ->
    (((k.+2)%:R*real_power (euclidean_unit_ball_volume R k.+2) ((k.+2)%:R)^-1*
      real_power (fine (mu Z)) ((k.+1)%:R/(k.+2)%:R))%:E<=mu Y*r^-1%:E)%E.
  move=>hMass; rewrite hMass fine0 (real_power_zero_base hpNe) mulr0.
  apply:mule_ge0; first exact:measure_nonnegative hm Y.
  by rewrite lee_fin.
split.
- case:(pselect (S !=set0))=>[hNe|hEmpty].
  + exact:(@outer_boundary_layer_volume_nonempty R k.+1 S r hNe hFinite hr).
  + have hSet:S=set0.
      apply/seteqP; split; last by move=>x [].
      move=>x hx; apply:hEmpty; by exists x.
    apply:hZero.
    by rewrite /mu hSet closure0 (measure_empty hm).
- case:(pselect ((~`metric_open_thickening (~`S) r) !=set0))=>[hNe|hEmpty].
  + exact:(@inner_boundary_layer_volume_nonempty_core R k.+1 S r hNe hFinite hr).
  + have hSet:(~`metric_open_thickening (~`S) r)=set0.
      apply/seteqP; split; last by move=>x [].
      move=>x hx; apply:hEmpty; by exists x.
    apply:hZero.
    by rewrite /mu hSet (measure_empty hm).
Qed.
