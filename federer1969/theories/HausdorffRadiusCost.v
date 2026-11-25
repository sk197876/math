(** Federer (1969), 2.10.27, p. 191: supporting diameter/radius
    normalization for the closed-ball section proof, using the gauge of
    2.10.2, p. 171. The identity is a consequence of the abstract unit-ball
    coefficient and finite scalar arithmetic, including radius and degree
    zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import EuclideanBallVolume HausdorffDiameterCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [hausdorff_doubled_radius_normalisation]: supporting
    cancellation of the diameter factor two in
    the ball-section calculation of 2.10.27, p. 191,
    using the gauge in 2.10.2, p. 171. *)
Lemma hausdorff_doubled_radius_normalisation (R : realType) n (r : R) :
  (hausdorff_normalisation R n*(r+r)^+n=euclidean_unit_ball_volume R n*r^+n)%R.
Proof.
have h2 : ((2 : R)^+n!=0)%R by rewrite expf_neq0 // pnatr_eq0.
by rewrite -mulr2n -mulr_natl exprMn mulrA /hausdorff_normalisation divfK.
Qed.
