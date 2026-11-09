(** Federer (1969), 3.3.19, p. 305: actual points
    of a child disc have every unit coordinate within
    2r/n of the corresponding original parent-circle point. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP Bilinear InnerNorm
  InnerNormInequalities InnerMetric MetricClosedBalls CircularUnitVectors CircularRegularDirections
  CircularDiscRefinement CircularDiscCentreRadius CircularDiscCaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Coordinates.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation hE:=(@euclidean_inner_productP R 2).
Local Notation B:=(@euclidean_inner_product R 2).

(** Source for [circular_disc_child_parent_circle_error]:
    each original child-disc point is within 2r/n of
    the original parent-circle point of its child angle,
    supporting the uniform cap comparison in 3.3.19,
    p. 305. All original closed-disc contacts remain. *)
Lemma circular_disc_child_parent_circle_error (z:E) (r:R) n (k:'I_n) (x:E):
  0<=r ->(0<n)%N ->
  metric_closed_ball (circular_disc_child_center z r k) (r/n%:R) x ->
  inner_norm hE ((x-z)-r*:(@circular_regular_direction R n k))<=2* r/n%:R.
Proof.
move=>hr hn hx.
pose u:= @circular_regular_direction R n k.
have hUnit:inner_norm hE u= 1:= @circular_unit_vector_norm R _.
have hRadius:0<=r/n%:R by apply:divr_ge0=>//;by rewrite ler0n.
have hDifference:circular_disc_child_center z r k-(z+r*:u)=(-(r/n%:R))*:u.
  rewrite /circular_disc_child_center -/u opprD addrACA subrr add0r -scalerBl.
  congr (_*:u);ring.
have hNear:mdist (circular_disc_child_center z r k) (z+r*:u)= r/n%:R.
  by rewrite inner_metric_distanceE hDifference inner_normZ hUnit mulr1 normrN (ger0_norm hRadius).
have hTriangle:= metric_triangle x (circular_disc_child_center z r k) (z+r*:u).
rewrite hNear (metric_sym x (circular_disc_child_center z r k)) in hTriangle.
have hVector:x-(z+r*:u)=(x-z)-r*:u by rewrite opprD addrA.
rewrite inner_metric_distanceE hVector in hTriangle.
change (is_true (mdist (circular_disc_child_center z r k) x<=r/n%:R)) in hx.
change (is_true (inner_norm hE ((x-z)-r*:u)<=2* r/n%:R));lra.
Qed.

(** Source for [circular_disc_child_cap_coordinate_error]:
    for every original unit cap direction u, the signed
    coordinate of x differs from r times the original
    cyclic direction coordinate by at most 2r/n,
    supporting 3.3.19, p. 305. *)
Theorem circular_disc_child_cap_coordinate_error (z u:E) (r:R) n (k:'I_n) (x:E):
  0<=r ->(0<n)%N ->inner_norm hE u= 1 ->
  metric_closed_ball (circular_disc_child_center z r k) (r/n%:R) x ->
  `|B (x-z) u-r* B (@circular_regular_direction R n k) u|<=2* r/n%:R.
Proof.
move=>hr hn hu hx.
have hError:= @circular_disc_child_parent_circle_error z r n k x hr hn hx.
have hCauchy:= inner_cauchy hE ((x-z)-r*:(@circular_regular_direction R n k)) u.
rewrite hu mulr1 (bilBl (inner_bilinear hE)) (bilZl (inner_bilinear hE)) in hCauchy.
change (is_true (`|B (x-z) u-r* B (@circular_regular_direction R n k) u|<=
  inner_norm hE ((x-z)-r*:(@circular_regular_direction R n k)))) in hCauchy.
exact:(le_trans hCauchy hError).
Qed.
End Coordinates.
