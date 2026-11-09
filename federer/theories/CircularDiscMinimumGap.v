(** Federer (1969), 3.3.19, p. 302: exact
    attained minimum gap of original sibling discs. The
    geometric conclusion is proved from their actual centres
    and radii, not specified as a refinement law. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric MetricClosedBalls
  CircularTrigonometrySealed CircularDiscRefinement CircularDiscCentreDistances
  CircularDiscGapBounds MetricMinimumPairDistanceUP InnerEqualBallMinimumDistance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Gap.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).

(** Source for [circular_disc_gap]: literal printed
    minimum gap 2(r/n)((n-1)sin(pi/n)-1), with
    parent radius r, 3.3.19, p. 302. Its minimum
    property is a subsequent theorem. *)
Definition circular_disc_gap (r:R) n:R:=
  2*(r/n%:R)*((n%:R-1)* S (p/n%:R)-1).

(** Source for [circular_disc_gap_scalar_identity]:
    rewriting the printed gap as the least centre distance
    minus two child radii, supporting 3.3.19, p. 302. *)
Lemma circular_disc_gap_scalar_identity (r:R) n:(0<n)%N ->
  circular_disc_gap r n= 2*((1-n%:R^-1)* r)* S (p/n%:R)-2*(r/n%:R).
Proof.
move=>hn;have hNN:(n%:R:R)!= 0 by rewrite pnatr_eq0 -lt0n.
have hCancel:(n%:R:R)*n%:R^-1= 1 by rewrite mulfV.
rewrite /circular_disc_gap.
have hExpand:(n%:R-1)* S (p/n%:R)-1=n%:R* S (p/n%:R)- S (p/n%:R)-1 by ring.
rewrite hExpand;have hScaled:=congr1 (fun z:R=>2* r* S (p/n%:R)* z) hCancel.
nra.
Qed.

(** Source for [circular_disc_gap_bounds]: the exact
    printed minimum is strictly larger than a child radius
    and at most the parent radius, 3.3.19, p. 302. *)
Lemma circular_disc_gap_bounds (r:R) n:0<r ->(4<=n)%N ->
  r/n%:R<circular_disc_gap r n /\circular_disc_gap r n<=r.
Proof.
move=>hr hn.
have hNP:(0<n%:R:>R) by rewrite ltr0n;exact:leq_trans (erefl true : (1<= 4)%N) hn.
have hNN:(n%:R:R)!= 0 by rewrite gt_eqF.
have hChild:0<r/n%:R by rewrite divr_gt0.
have hBudget:(r/n%:R)* n%:R=r by rewrite divfK.
have hLow:=@circular_disc_gap_coefficient_above_one R n hn.
have hHigh:=@circular_disc_gap_coefficient_parent_bound R n hn.
rewrite /circular_disc_gap;split;nra.
Qed.

(** Source for [circular_disc_sibling_gap_lower]: every
    actual point pair in distinct original child discs has
    distance at least the printed minimum, 3.3.19,
    p. 302. No compactness or minimizer premise is needed. *)
Lemma circular_disc_sibling_gap_lower (z:E) (r:R) n (k l:'I_n) (x y:E):
  0<r ->(4<=n)%N ->k!=l ->
  metric_closed_ball (circular_disc_child_center z r k) (r/n%:R) x ->
  metric_closed_ball (circular_disc_child_center z r l) (r/n%:R) y ->
  circular_disc_gap r n<=mdist x y.
Proof.
move=>hr hn hne hx hy.
have hnP:(0<n)%N:=leq_trans (erefl true : (1<= 4)%N) hn.
rewrite (@circular_disc_gap_scalar_identity r n hnP).
have hCentre:=@circular_disc_centre_minimum R z r n k l hr hn hne.
have hTriangle:=metric_triangle (circular_disc_child_center z r k) x
  (circular_disc_child_center z r l).
have hTriangle2:=metric_triangle x y (circular_disc_child_center z r l).
change (is_true (mdist (circular_disc_child_center z r k) x<=r/n%:R)) in hx.
have hy':mdist y (circular_disc_child_center z r l)<=r/n%:R by rewrite metric_sym;exact hy.
nra.
Qed.

(** Source for [circular_disc_sibling_gap_attained]:
    actual adjacent sibling discs attain the displayed
    minimum in 3.3.19, p. 302. Both original indices
    and both original attaining points remain existential. *)
Lemma circular_disc_sibling_gap_attained (z:E) (r:R) n:
  0<r ->(4<=n)%N ->exists k l:'I_n,k!=l /\
  exists x y:E,
    metric_closed_ball (circular_disc_child_center z r k) (r/n%:R) x /\
    metric_closed_ball (circular_disc_child_center z r l) (r/n%:R) y /\
    mdist x y=circular_disc_gap r n.
Proof.
move=>hr hn.
have hnP:(0<n)%N:=leq_trans (erefl true : (1<= 4)%N) hn.
have hNP:(0<n%:R:>R) by rewrite ltr0n.
have hChild:0<r/n%:R by rewrite divr_gt0.
have [k [l [hKL hDistance]]]:=@circular_disc_centre_minimum_attained R z r n hr hn.
have [hGap _]:=@circular_disc_gap_bounds r n hr hn.
have hRewrite:=@circular_disc_gap_scalar_identity r n hnP.
have hSep:2*(r/n%:R)<mdist (circular_disc_child_center z r k) (circular_disc_child_center z r l).
  rewrite hDistance;nra.
have [_ [x [y [hx [hy hXY]]]]]:=@inner_equal_ball_minimum_distance R
  (R_n R 2) (@euclidean_inner_product R 2)
  (@euclidean_inner_productP R 2) (circular_disc_child_center z r k)
  (circular_disc_child_center z r l) (r/n%:R) (ltW hChild) hSep.
exists k,l;split=>//;exists x,y;split=>//;split=>//.
by rewrite hXY hDistance -hRewrite.
Qed.
End Gap.
