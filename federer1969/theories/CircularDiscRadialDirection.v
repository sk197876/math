(** Federer (1969), 3.3.19, p. 305:
    the original radial direction is well-defined
    on each actual child disc, because its points
    remain strictly away from the parent centre. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  InnerUnitNormalization MetricClosedBalls CircularDiscRefinement CircularDiscCentreRadius.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Direction.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation hE:=(@euclidean_inner_productP R 2).

(** Source for [circular_disc_child_parent_radius_lower]:
    actual points of each original child disc
    stay at distance at least r-2r/n
    from the original parent centre, supporting
    eta_n in 3.3.19, p. 305. *)
Lemma circular_disc_child_parent_radius_lower (z:E) (r:R) n (k:'I_n) (x:E):
  0<r ->(4<=n)%N ->
  metric_closed_ball (circular_disc_child_center z r k) (r/n%:R) x ->
  r-2*(r/n%:R)<=inner_norm hE (x-z).
Proof.
move=>hr hn hx.
have hnP:(0<n)%N:= leq_trans (erefl true : (1<=4)%N) hn.
have hCentre:= @circular_disc_child_centre_radius R z r n k (ltW hr) hnP.
have hTriangle:= metric_triangle z x (circular_disc_child_center z r k).
rewrite hCentre (metric_sym x (circular_disc_child_center z r k)) in hTriangle.
have hDistance:inner_norm hE (x-z)= mdist z x by rewrite metric_sym inner_metric_distanceE.
rewrite hDistance;change (is_true (mdist (circular_disc_child_center z r k) x<=r/n%:R)) in hx;lra.
Qed.

(** Source for [circular_disc_child_parent_radius_positive]:
    no point of any original child disc equals
    its original parent centre, so the original
    denominator in eta_n is positive,
    3.3.19, p. 305. All actual
    subdivisions n>=4 are retained. *)
Lemma circular_disc_child_parent_radius_positive (z:E) (r:R) n (k:'I_n) (x:E):
  0<r ->(4<=n)%N ->
  metric_closed_ball (circular_disc_child_center z r k) (r/n%:R) x ->
  0<inner_norm hE (x-z).
Proof.
move=>hr hn hx.
have hLower:= @circular_disc_child_parent_radius_lower z r n k x hr hn hx.
have hn4:(4<=n%:R:>R) by rewrite ler_nat.
have hnP:(0<n%:R:>R) by lra.
have hInv:(0<(n%:R:R)^-1) by rewrite invr_gt0.
have hNN:(n%:R:R)!=0 by rewrite gt_eqF.
have hProduct:n%:R* n%:R^-1=(1:R) by rewrite mulfV.
have hScale:= ler_wpM2r (ltW hInv) hn4.
rewrite hProduct in hScale.
have hInvUpper:(n%:R:R)^-1<=1/4 by lra.
have hRadiusBound:= ler_wpM2l (ltW hr) hInvUpper.
have hPositive:r/2<=r-2*(r/n%:R) by nra.
have hHalf:0<r/2 by lra.
exact:(lt_le_trans hHalf (le_trans hPositive hLower)).
Qed.

(** Source for [circular_disc_radial_direction]: the
    original normalized vector (x-z)/|x-z|,
    before the parent is uniquely specified,
    in 3.3.19, p. 305. *)
Definition circular_disc_radial_direction (z x:E):E:= inner_unit_normalization hE (x-z).

(** Source for [circular_disc_radial_direction_unit]:
    every actual radial direction of an original
    child-disc point lies on the actual unit
    circle, as required for eta_n in
    3.3.19, p. 305. Positivity
    of the actual denominator is proved above. *)
Theorem circular_disc_radial_direction_unit (z:E) (r:R) n (k:'I_n) (x:E):
  0<r ->(4<=n)%N ->
  metric_closed_ball (circular_disc_child_center z r k) (r/n%:R) x ->
  inner_norm hE (circular_disc_radial_direction z x)= 1.
Proof.
move=>hr hn hx;apply:inner_unit_normalization_norm.
exact:(@circular_disc_child_parent_radius_positive z r n k x hr hn hx).
Qed.
End Direction.
