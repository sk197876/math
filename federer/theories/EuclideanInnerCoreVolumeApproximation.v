(** Federer (1969), 3.2.43, printed p. 278:
    the actual inner-core volumes increase to the original
    interior volume. Reciprocal cores give a countable
    increasing exhaustion; monotonicity restores every
    sufficiently small positive real radius. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanInnerCoreBasic MetricInnerCoreExhaustion MetricOpenThickening
  MeasureUP MeasureBasic MeasureContinuityBelow ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_inner_core_volume_eventual_lower]:
    direct increasing-volume observation in Federer 3.2.43,
    p. 278, in its full positive-real-radius form. Every
    strict finite lower threshold on the actual interior
    mass eventually bounds every original inner core below.
    No finite-volume, measurability or boundedness of S is
    needed for this supporting approximation theorem. *)
Theorem euclidean_inner_core_volume_eventual_lower (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (q:R):
  (q%:E<@euclidean_lebesgue_measure R n (interior S))%E ->
  exists d:R,0<d /\forall r:R,0<r<d ->
    (q%:E<@euclidean_lebesgue_measure R n (~`metric_open_thickening (~`S) r))%E.
Proof.
move=>hQ.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose F:=fun j=>~`metric_open_thickening (~`S) (((j.+1)%:R:R)^-1).
have hm:=euclidean_lebesgue_is_measure R n.
have hMeas j:measure_measurable mu (F j):=
  (euclidean_inner_core_closed_measurable S (((j.+1)%:R:R)^-1)).2.
have hMono i j:(i<=j)%N ->F i `<=` F j.
  move=>hij.
  have hi:0<(i.+1%:R:R) by rewrite ltr0n.
  have hj:0<(j.+1%:R:R) by rewrite ltr0n.
  have hRadius:((j.+1)%:R:R)^-1<=((i.+1)%:R:R)^-1.
    by rewrite (@lef_pV2 R j.+1%:R i.+1%:R hj hi) ler_nat.
  exact:(@metric_inner_core_radius_antitone R E S _ _ hRadius).
have hUnion:(\bigcup_j F j)=interior S:=metric_inner_core_reciprocal_exhaustion S.
have hLimit:=(@measure_continuity_below R E mu hm F hMeas hMono).2.
rewrite hUnion in hLimit.
have [N hN]:=hLimit.1 q%:E hQ.
pose d:R:=((N.+1)%:R:R)^-1.
have hd:0<d by rewrite /d invr_gt0 ltr0n.
exists d; split; first exact hd.
move=>r /andP[hr hrd].
have hSub:F N `<=` (~`metric_open_thickening (~`S) r):=
  @metric_inner_core_radius_antitone R E S r d (ltW hrd).
exact:(lt_le_trans (hN N (leqnn N)) (@measure_mono R E mu hm _ _ hSub)).
Qed.
