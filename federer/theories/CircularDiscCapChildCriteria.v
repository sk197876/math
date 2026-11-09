(** Federer (1969), 3.3.19, p. 305: original child
    intersection and whole-child containment tests for the
    actual caps, with the uniform coordinate error proved. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric MetricClosedBalls
  CircularTrigonometrySealed CircularRegularDirections CircularDiscRefinement CircularDiscCentreRadius
  CircularDiscCaps CircularDiscCapCoordinateError.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Criteria.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation hE:=(@euclidean_inner_productP R 2).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation B:=(@euclidean_inner_product R 2).

(** Source for [circular_disc_child_meeting_cap_cosine]:
    meeting the actual original cap forces the original
    cyclic direction coordinate to be at least cos(gamma)-2/n,
    supporting the uniform mass comparison in 3.3.19,
    p. 305. Actual closed boundary contacts are retained. *)
Theorem circular_disc_child_meeting_cap_cosine (z u:E) (r gamma:R) n (k:'I_n):
  0<r ->(0<n)%N ->inner_norm hE u= 1 ->
  (exists x:E,metric_closed_ball (circular_disc_child_center z r k) (r/n%:R) x /\
    circular_disc_cap z r u gamma x) ->
  C gamma-2/n%:R<=B (@circular_regular_direction R n k) u.
Proof.
move=>hr hn hu [x [hx [_ hCap]]].
have hError:= @circular_disc_child_cap_coordinate_error R z u r n k x (ltW hr) hn hu hx.
have /andP[hLower hUpper]:(-(2* r/n%:R)<=B (x-z) u-r* B (@circular_regular_direction R n k) u<=2* r/n%:R)
  by move:hError;rewrite ler_norml.
change (is_true (r* C gamma<=B (x-z) u)) in hCap.
rewrite -(ler_pM2l hr);nra.
Qed.

(** Source for [circular_disc_child_inside_cap_cosine]:
    an original direction coordinate at least cos(gamma)+2/n
    places the entire original closed child disc in the
    original cap. This is the converse finite comparison
    supporting 3.3.19, p. 305. Parent containment
    and the signed coordinate inequality are both derived. *)
Theorem circular_disc_child_inside_cap_cosine (z u:E) (r gamma:R) n (k:'I_n):
  0<r ->(0<n)%N ->inner_norm hE u= 1 ->
  C gamma+2/n%:R<=B (@circular_regular_direction R n k) u ->
  metric_closed_ball (circular_disc_child_center z r k) (r/n%:R) `<=`
    circular_disc_cap z r u gamma.
Proof.
move=>hr hn hu hCoordinate x hx;split.
- have hCentre:= @circular_disc_child_centre_radius R z r n k (ltW hr) hn.
  have hTriangle:= metric_triangle z (circular_disc_child_center z r k) x.
  rewrite hCentre in hTriangle.
  change (is_true (mdist (circular_disc_child_center z r k) x<=r/n%:R)) in hx.
  change (is_true (mdist z x<=r));lra.
- have hError:= @circular_disc_child_cap_coordinate_error R z u r n k x (ltW hr) hn hu hx.
  have /andP[hLower hUpper]:(-(2* r/n%:R)<=B (x-z) u-r* B (@circular_regular_direction R n k) u<=2* r/n%:R)
    by move:hError;rewrite ler_norml.
  have hScaled:= ler_wpM2l (ltW hr) hCoordinate.
  change (is_true (r* C gamma<=B (x-z) u));nra.
Qed.
End Criteria.
