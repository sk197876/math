(** Federer (1969), 3.2.37, p. 274: the positive-degree
    Minkowski content functions are not measures. Countable dense
    sources have infinite tube volume, while every singleton has
    zero positive-degree content. Degree zero is kept separate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNormedTopology EuclideanLebesgueDimensions
  EuclideanBallVolume MetricOpenThickening MetricClosedBalls MinkowskiContents
  MinkowskiContentsBasic PositiveRadiusLimitCongruence MeasureUP MeasureBasic.
From mathcomp Require Import num_normedtype pseudometric_normed_Zmodule normed_module.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dense_metric_open_thickening]: closure invariance
    applied to a dense source, supporting the non-measure statement
    in Federer 3.2.37, p. 274. Every positive-radius tube is
    exactly the whole space, with no source measurability premise. *)
Lemma dense_metric_open_thickening (R:realType) (X:metricType R)
    (D:set X) (r:R): dense D ->(0<r)%R ->metric_open_thickening D r=setT.
Proof.
move=>hD hr; apply/seteqP; split=>[x _//|x _].
have hNonempty:[set y:X|(mdist x y<r)%R]!=set0.
  exists x; change (is_true (mdist x x<r)%R); by rewrite mdistxx.
have [y [hy hDy]]:=hD _ hNonempty (metric_open_ball_open x r).
exists y=>//.
change (is_true (mdist y x<r)%R).
change (is_true (mdist x y<r)%R) in hy.
by rewrite metric_sym.
Qed.

(** Source for [large_positive_power_ge_radius]: scalar support
    for the infinite ambient volume in the positive-degree
    non-measure example, Federer 3.2.37, p. 274. *)
Lemma large_positive_power_ge_radius (R:realType) n (r:R):
  (0<n)%N ->(1<=r)%R ->(r<=r^+n)%R.
Proof.
move=>hn hr1.
have hr:(0<r)%R:=lt_le_trans ltr01 hr1.
have hP k:(1<=r^+k)%R.
  elim:k=>[|k ih]; first by rewrite expr0.
  rewrite exprS.
  have hStep:=ler_wpM2l (ltW hr) ih.
  rewrite mulr1 in hStep; exact:le_trans hr1 hStep.
case:n hn=>[|k] hn; first by rewrite ltn0 in hn.
rewrite exprS -{1}(mulr1 r) ler_pM2l //; exact:hP.
Qed.

(** Source for [positive_euclidean_whole_volume_infinite]: the
    actual positive-dimensional Lebesgue volume of the whole space
    is infinite, supporting the dense-source counterexample of
    Federer 3.2.37, p. 274. Actual ball volumes give arbitrarily
    large finite lower bounds. *)
Lemma positive_euclidean_whole_volume_infinite (R:realType) n:
  (0<n)%N ->@euclidean_lebesgue_measure R n setT= +oo.
Proof.
move=>hn.
pose mu:=@euclidean_lebesgue_measure R n.
have hm:=euclidean_lebesgue_is_measure R n.
have hNonnegative:=measure_nonnegative hm setT.
case:(ltP (mu setT) +oo)=>[hFinite|hInfinity]; last first.
- by apply/eqP; rewrite eq_le hInfinity leey.
- exfalso.
  have hFin:mu setT \is a fin_num by rewrite ge0_fin_numE.
  pose v:=fine (mu setT).
  have hValue:mu setT=v%:E by rewrite /v fineK.
  pose alpha:=euclidean_unit_ball_volume R n.
  have hAlpha:(0<alpha)%R:=(euclidean_unit_ball_volumeE R n).2.
  pose r:=(Num.max 1 ((v+1)/alpha))%R.
  have hr1:(1<=r)%R by rewrite /r le_max lexx.
  have hr:(0<r)%R:=lt_le_trans ltr01 hr1.
  have hRatio:((v+1)/alpha<=r)%R by rewrite /r le_max lexx orbT.
  have hScale:(v+1<=alpha*r)%R.
    move:hRatio; rewrite ler_pdivrMr //; by rewrite mulrC.
  have hPow:=ler_wpM2l (ltW hAlpha) (large_positive_power_ge_radius hn hr1).
  pose X:=[the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
  pose B:set X:=[set x:X|(`|x-(0%R:X)|<r)%R].
  have hBall:mu B<=mu setT:=@measure_mono R X mu hm B setT (subsetT B).
  have hBallValue:mu B=(alpha*r^+n)%:E.
    exact:(@euclidean_ball_measure R n (0%R:X) r hr).
  rewrite hBallValue hValue lee_fin in hBall.
  have hBad:(v+1<=v)%R:=le_trans hScale (le_trans hPow hBall).
  have hStrict:(v<v+1)%R by rewrite ltrDl ltr01.
  have hFalse:=lt_le_trans hStrict hBad; by rewrite ltxx in hFalse.
Qed.

(** Source for [dense_minkowski_contents_infinite]: every dense
    source in a positive-dimensional Euclidean space has both
    actual Minkowski contents infinite, Federer 3.2.37, p. 274.
    The normalization is strictly positive at all retained radii. *)
Lemma dense_minkowski_contents_infinite (R:realType) n m
    (D:set (inner_metric_space (@euclidean_inner_productP R n))):
  (0<n)%N ->dense D ->
  upper_minkowski_content m D= +oo /\lower_minkowski_content m D= +oo.
Proof.
move=>hn hD.
have hTube:forall r:R,(0<r)%R ->minkowski_tube_quotient m D r= +oo.
  move=>r hr; have hPositive:=minkowski_tube_denominator_positive n m hr.
  rewrite /minkowski_tube_quotient (dense_metric_open_thickening hD hr)
    (@positive_euclidean_whole_volume_infinite R n hn) inver (gt_eqF hPositive).
  rewrite gt0_mulye // lte_fin invr_gt0; exact:hPositive.
have [hu hl]:=positive_radius_limits_congr hTube.
rewrite /upper_minkowski_content /lower_minkowski_content hu hl.
exact:positive_radius_limits_constant.
Qed.
