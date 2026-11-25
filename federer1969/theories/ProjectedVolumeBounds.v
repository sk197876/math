(** Federer (1969), 2.10.5, p. 172, last paragraph, paraphrased: bounded S
    has bounded projected-volume function f_S. Every orthogonal projection
    maps a common source norm ball into the target ball of the same radius;
    the latter is compact and has finite Lebesgue measure. This proof needs
    neither Suslin measurability nor a selected parameter measure. It uses
    the actual local Euclidean and projection results. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanProjectionSpace EuclideanProjectionMetric ProjectedVolumeMeasurability
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanClosedDiameterCompact
  MetricClosedBalls MetricDiameterUP MetricDiameter MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projected_volume_function_mono]:
    supporting image-volume monotonicity for the
    gauge of Federer 2.10.5, p. 172. *)
Lemma projected_volume_function_mono (R : realType) (n m : nat)
    (S T : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n m) :
  S `<=` T -> projected_volume_function S p<=projected_volume_function T p.
Proof.
move=> hST; apply: (measure_mono (euclidean_lebesgue_is_measure R m)).
by move=> y [x hx <-]; exists x=> //; exact: hST x hx.
Qed.

(** Source for [projected_volume_function_bounded]:
    direct boundedness conclusion in Federer 2.10.5,
    p. 172, with an explicit source norm bound.
    Empty sets and dimension zero are included in
    this supporting generalization. *)
Theorem projected_volume_function_bounded (R : realType) (n m : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (c : R) :
  (forall x, S x -> (inner_norm (@euclidean_inner_productP R n) x<=c)%R) ->
  exists b : R, (0<=b)%R /\ forall p : orthogonal_projection_metric_space R n m,
    projected_volume_function S p<=b%:E.
Proof.
move=> hS.
pose E := inner_metric_space (@euclidean_inner_productP R n).
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose d := Order.max c 0%R.
pose K := @metric_closed_ball R Y (0:Y)%R d.
have hd : extended_metric_diameter K<=(d+d)%R%:E.
  apply: (metric_diameter_least (extended_metric_diameter_specification K)).
  - rewrite lee_fin addr_ge0 //; by rewrite /d le_max lexx orbT.
  - move=> x y hx hy; rewrite lee_fin; exact: metric_closed_ball_diameter_bound hx hy.
have hK : compact K := @euclidean_closed_finite_diameter_compact R m K (d+d)%R
  (@metric_closed_ball_closed R Y (0:Y)%R d) hd.
have hm := euclidean_lebesgue_is_measure R m.
have hfin : euclidean_lebesgue_measure m K \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm K)); exact: euclidean_compact_finite hK.
pose b := fine (euclidean_lebesgue_measure m K).
have hb : euclidean_lebesgue_measure m K=b%:E by rewrite /b fineK.
exists b; split.
- by have := measure_nonnegative hm K; rewrite hb lee_fin.
- move=> p; rewrite /projected_volume_function -hb; apply: (measure_mono hm).
  move=> y [x hx <-].
  have hcon := @euclidean_projection_nonexpanding R n m p x (0:E)%R.
  rewrite linear0 !inner_metric_distanceE !subr0 in hcon.
  change (is_true (mdist (0:Y)%R (euclidean_projection_linear p x:Y)<=d)%R).
  rewrite inner_metric_distanceE sub0r inner_normN.
  apply: le_trans (le_trans hcon (hS x hx)) _.
  by rewrite /d le_max lexx.
Qed.

(** Source for [projected_volume_function_finite]:
    supporting finiteness consequence of the bounded-
    set paragraph in Federer 2.10.5, p. 172.
    The finite scalar part can be used only after
    this proof, not for arbitrary unbounded sets. *)
Lemma projected_volume_function_finite (R : realType) (n m : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (c : R) :
  (forall x, S x -> (inner_norm (@euclidean_inner_productP R n) x<=c)%R) ->
  forall p : orthogonal_projection_metric_space R n m,
    projected_volume_function S p \is a fin_num.
Proof.
move=> hS; have [b [_ hb]] := @projected_volume_function_bounded R n m S c hS.
move=> p; rewrite (ge0_fin_numE (projected_volume_function_nonnegative S p)).
exact: le_lt_trans (hb p) (ltry b).
Qed.
