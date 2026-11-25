(** Exact prefix balls for the project test of the spherical
    parenthesis in Federer 2.10.11, p. 176. Only public metric
    laws and the existing binary cylinders are used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import BinarySequenceCylinders BinaryCylinderPrefixLaws
  BinaryPrefixDistanceUP BinaryPrefixMetric DyadicScaleBounds MetricClosedBalls
  MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_prefix_distance_strict_prefix]: a strict
    dyadic distance bound fixes the next coordinate, supporting the
    project test of Federer 2.10.11, p. 176. *)
Lemma binary_prefix_distance_strict_prefix (R:realType)
    (x y:binary_prefix_metric R) n :
  mdist x y<((2^n)%N)%:R^-1 -> binary_common_prefix n.+1 x y.
Proof.
move=> hd k;rewrite ltnS=> hkn.
case:(eqVneq (x k) (y k))=> // hne.
have hxy:x!=y.
  apply/eqP=> he;by rewrite he eqxx in hne.
have [j hj]:=binary_first_difference_exists hxy.
have hjk:(j<=k)%N.
  rewrite leqNgt;apply/negP=> hkj.
  by move:hne;rewrite (hj.2 k hkj) eqxx.
have hjn:=leq_trans hjk hkn.
have h:=@dyadic_side_antitone R j n hjn.
rewrite -(binary_prefix_distance_first (BinaryPrefixDistance.laws R) hj) in h.
have hbad:=lt_le_trans hd h;by rewrite ltxx in hbad.
Qed.

(** Source for [binary_prefix_closed_ball]: exact finite-prefix
    identity for closed dyadic balls in the project example for
    Federer 2.10.11, p. 176. All radii are positive. *)
Lemma binary_prefix_closed_ball (R:realType) (a:binary_prefix_metric R) n :
  metric_closed_ball a (((2^n)%N)%:R^-1)=
    [set x | binary_common_prefix n a x].
Proof.
apply/seteqP;split=> x hx.
- case:n hx=> [|n] hx.
  + by move=> k;rewrite ltn0.
  + have hp:=dyadic_side_positive R n.
    have hs:(((2^n.+1)%N)%:R^-1:R)<((2^n)%N)%:R^-1.
      rewrite dyadic_side_successor; lra.
    exact:binary_prefix_distance_strict_prefix (le_lt_trans hx hs).
- change (is_true (BinaryPrefixDistance.distance R a x<=((2^n)%N)%:R^-1)).
  exact (@binary_prefix_distance_prefix_bound R (@BinaryPrefixDistance.distance R)
    (BinaryPrefixDistance.laws R) n a x hx).
Qed.

(** Source for [binary_prefix_cylinder_ball]: each original binary
    cylinder is a positive-radius metric ball. This connects the
    existing probability construction to the project test of Federer
    2.10.11, p. 176. *)
Lemma binary_prefix_cylinder_ball (R:realType) (w:seq bool) :
  @binary_cylinder w=metric_closed_ball
    ((fun k=>nth false w k):binary_prefix_metric R) (((2^(size w))%N)%:R^-1).
Proof.
rewrite binary_prefix_closed_ball;apply/seteqP;split=> x hx k hk;
  exact:esym (hx k hk).
Qed.

(** Source for [binary_prefix_cylinder_diameter_bound]: a length-n
    cylinder has diameter at most 2^(-n), rather than twice that
    radius. Supporting the project test of Federer 2.10.11,
    p. 176; no general metric ball is assumed to have diameter 2r. *)
Lemma binary_prefix_cylinder_diameter_bound (R:realType) (w:seq bool) :
  (@extended_metric_diameter R (binary_prefix_metric R) (binary_cylinder w)
    <=(((2^(size w))%N)%:R^-1:R)%:E)%E.
Proof.
apply:(metric_diameter_least
  (@extended_metric_diameter_specification R (binary_prefix_metric R) (binary_cylinder w))).
- rewrite lee_fin;exact:ltW (dyadic_side_positive R (size w)).
- move=> x y hx hy;rewrite lee_fin binary_prefix_metric_distance.
  have hp:binary_common_prefix (size w) x y.
    move=> k hk;rewrite (hx k hk);exact:esym (hy k hk).
  exact (@binary_prefix_distance_prefix_bound R (@BinaryPrefixDistance.distance R)
    (BinaryPrefixDistance.laws R) (size w) x y hp).
Qed.

(** Source for [binary_prefix_ball_small_cylinder]: a ball of any
    positive radius is contained in a cylinder whose assigned mass
    is no greater than that radius. Supporting the lower measure
    bound for the project test of Federer 2.10.11, p. 176. *)
Lemma binary_prefix_ball_small_cylinder (R:realType)
    (a:binary_prefix_metric R) (r:R) : 0<r -> exists n,
  (((2^n)%N)%:R^-1:R)<=r /\
    metric_closed_ball a r `<=` binary_cylinder (binary_sequence_prefix n a).
Proof.
move=> hr.
have hex:exists n,(((2^n)%N)%:R^-1:R)<=r.
  have [n hn]:=dyadic_sides_arbitrarily_small hr.
  exists n;exact:ltW hn.
have [n hn hmin]:=ex_minnP hex.
exists n;split;first exact hn.
move=> x hx.
have hprefix:binary_common_prefix n a x.
  case:n hn hmin=> [|j] hn hmin.
  - by move=> l;rewrite ltn0.
  - have hstrict:r<(((2^j)%N)%:R^-1:R).
      rewrite ltNge;apply/negP=> hback.
      have hbad:=hmin j hback;by rewrite leqNgt ltnSn in hbad.
    exact:binary_prefix_distance_strict_prefix (le_lt_trans hx hstrict).
move=> k hk.
have hkn:(k<n)%N by move:hk;rewrite size_tuple.
have hword:=@binary_sequence_in_prefix n a k hk.
by rewrite -(hprefix k hkn) hword.
Qed.
