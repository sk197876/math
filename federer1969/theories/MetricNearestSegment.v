(** Federer (1969), 3.2.34, p. 271: the distance
    decreases linearly on a segment to a nearest point.
    The abstract distance laws suffice once that point exists. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra.
From Federer Require Import RealNormUP NormMetric MetricSetDistanceUP MetricSetDistanceBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_nearest_segment_distance]: the displayed
    identity f[x+t(s-x)]=f(x)-t|s-x| for 0<=t<=1,
    Federer 3.2.34, p. 271. The Lipschitz distance
    inequality gives the lower bound and the nearest point
    gives the matching upper bound. This supporting normed-space
    statement needs no convexity of the original set. *)
Lemma norm_nearest_segment_distance (R:realType) (X:lmodType R)
    (N:X->R) (hN:is_real_norm N) (S:set X) (d:X->R) x s t:
  @is_metric_set_distance R [the metricType R of real_norm_metric_space hN] S d ->
  S s ->d x=N (x-s) ->0<=t<=1 ->
  d (x+t*:(s-x))=d x-t*N (s-x).
Proof.
move=>hDistance hs hNearest /andP[ht0 ht1].
pose v:=s-x; pose y:=x+t*:v.
have hS:s=x+v by rewrite /v addrC subrK.
have hDiff:y-s=(t-1)*:v.
  by rewrite /y hS opprD addrACA subrr add0r scalerBl scale1r.
have hNormDistance:N (x-y)=t*N v.
  by rewrite /y opprD addrA subrr add0r
    (real_seminorm_negate hN.1) (real_seminorm_scale hN.1) (ger0_norm ht0).
have hNegative:t-1<=0 by rewrite subr_le0.
have hNormNearest:N (y-s)=(1-t)*N v.
  by rewrite hDiff (real_seminorm_scale hN.1) (ler0_norm hNegative) opprB.
have hValue:d x=N v by rewrite hNearest (real_seminorm_subtract hN.1 x s).
have hLower:=@metric_set_distance_subtract_bound R
  [the metricType R of real_norm_metric_space hN] S d hDistance x y.
change (is_true (d x-d y<=N (x-y))) in hLower.
have hUpper:=@metric_set_distance_lower R
  [the metricType R of real_norm_metric_space hN] S d hDistance y s hs.
change (is_true (d y<=N (y-s))) in hUpper.
rewrite hNormDistance hValue in hLower; rewrite hNormNearest in hUpper.
change (d y=d x-t*N v).
rewrite hValue; apply/eqP; rewrite eq_le; apply/andP; split; nra.
Qed.
