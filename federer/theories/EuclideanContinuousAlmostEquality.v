(** Federer (1969), 4.1.19, p. 377: continuous
    representatives upgrade almost equality of the weak
    derivative to pointwise equality on U. The
    supporting full-support argument uses the original positive
    measure of every nonempty Euclidean open ball,
    including dimension zero, from 2.7.16, pp. 134–135. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealNormUP NormMetric NormClassOneUP
  NormClassZeroTopology GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness CurrentDomain CoveringFamilyUP MetricClosedBalls
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  EuclideanOpenDomainMeasure OpenSubspaceMeasure MeasureUP
  MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_continuous_almost_equal]:
    continuous actual representatives with the same
    original Lebesgue almost class agree everywhere
    on U, supporting the continuous version of
    the class-one clause in Federer 4.1.19,
    p. 377. No separability, completeness,
    boundedness or nonempty-domain premise is needed. *)
Theorem euclidean_continuous_almost_equal
    (R : realType) n (Y : lmodType R) (N : Y -> R) (hN : is_real_norm N)
    (U : set (R_n R n)) (f g : R_n R n -> Y) :
  norm_class_zero (inner_norm (@euclidean_inner_productP R n)) N U f ->
  norm_class_zero (inner_norm (@euclidean_inner_productP R n)) N U g ->
  measure_almost_everywhere (@euclidean_open_domain_measure R n U)
    [set x : current_domain R n U | f (set_val x)=g (set_val x)] ->
  forall x, U x -> f x=g x.
Proof.
move=> hF hG hAlmost a ha.
have [hEqual|hDifferent] := eqVneq (f a) (g a); first exact: hEqual.
pose X := R_n R n.
pose NX := inner_norm (@euclidean_inner_productP R n).
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R n).
pose XT := real_norm_metric_space hNX.
pose UT := current_domain R n U.
pose d := N (f a-g a).
have hD : 0<d.
  rewrite /d (real_norm_positive hN.1 hN.2) subr_eq0.
  exact: hDifferent.
have hQuarter : 0<d/4 by rewrite divr_gt0 // ltr0n.
have [rF [hRF hFNear]] := @norm_class_zero_local_control R X Y NX N hNX U f a
  (d/4) hF ha hQuarter.
have [rG [hRG hGNear]] := @norm_class_zero_local_control R X Y NX N hNX U g a
  (d/4) hG ha hQuarter.
pose r := Num.min rF rG.
have hR : 0<r by rewrite /r lt_min hRF hRG.
pose B := @metric_open_ball R XT a r.
have hMember : B a.
  change (is_true (NX (a-a)<r)).
  have hZero : NX (a-a)=0.
    exact: (eq_trans (congr1 NX (subrr a))
      (@inner_norm0 R X (@euclidean_inner_product R n) (@euclidean_inner_productP R n))).
  by rewrite hZero.
have hPositive : (0<@euclidean_lebesgue_measure R n B)%E :=
  @euclidean_distribution_measure_open_positive R n B a
    (@metric_open_ball_open R XT a r) hMember.
have hNull : @euclidean_lebesgue_measure R n B=0%E.
  have hBadNull : @euclidean_lebesgue_measure R n
      ((set_val : UT -> X) @` (~` [set x : UT | f (set_val x)=g (set_val x)]))=0%E.
    exact: hAlmost.
  apply: (@measure_null_subset R X (@euclidean_lebesgue_measure R n)
    (euclidean_lebesgue_is_measure R n) B _ _ hBadNull).
  move=> y hy.
  have hNear : NX (y-a)<r.
    change (is_true (NX (a-y)<r)) in hy.
    have hSymmetry : NX (y-a)=NX (a-y) :=
      @real_seminorm_subtract R X NX hNX.1 y a.
    by rewrite hSymmetry.
  have hToF : r<=rF by rewrite /r ge_min lexx.
  have hToG : r<=rG by rewrite /r ge_min lexx orbT.
  have [hUy hFError] := @hFNear y (lt_le_trans hNear hToF).
  have [_ hGError] := @hGNear y (lt_le_trans hNear hToG).
  have hBad : f y<>g y.
    move=> hSame.
    have hIdentity : f a-g a=(f a-f y)+(g y-g a).
      by rewrite hSame addrA subrK.
    have hTriangle := real_seminorm_triangle hN.1 (f a-f y) (g y-g a).
    rewrite -hIdentity (real_seminorm_subtract hN.1 (f a) (f y)) in hTriangle.
    change (is_true (d<=N (f y-f a)+N (g y-g a))) in hTriangle.
    lra.
  pose p : UT := exist _ y (mem_set hUy).
  exists p; first exact: hBad.
  reflexivity.
have hContradiction := hPositive.
by rewrite hNull ltxx in hContradiction.
Qed.
