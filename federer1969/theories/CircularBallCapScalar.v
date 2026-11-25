(** Federer (1969), 3.3.19, p. 306: scalar
    normalized distance estimates for the original ball
    inside a slightly enlarged circular cap. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [circular_normalized_ball_cap_threshold]:
    original point radii D,d in [1-2h,1], a ball
    radius 0<=T<=2 and the actual squared distance
    inequality give normal coordinate X>=1-T^2/2-12h.
    This supporting elementary estimate for 3.3.19,
    p. 306 is proved without a supplied cap limit. *)
Theorem circular_normalized_ball_cap_threshold (R:realType) (h d D T X:R):
  0<=h ->h<=1/4 ->1-2* h<=d ->d<=1 ->
  1-2* h<=D ->0<=T ->T<=2 ->D^+2+d^+2-T^+2<=2* d* X ->
  1-T^+2/2-12* h<=X.
Proof.
move=>hh hh4 hd hd1 hD hT hT2 hDistance.
have hLeft:0<=1-2* h by lra.
have hD0:0<=D by lra.
have hDSquare:(1-2* h)^+2<=D^+2 by rewrite ler_sqr.
have hDLower:1-4* h<=D^+2 by nra.
have hTBound:T^+2<=4 by nra.
have hdHalf:1/2<=d by lra.
have hdPositive:0<d by lra.
have hDeficit:0<=1-d by lra.
have hDeficitUpper:1-d<=2* h by lra.
have hProduct1:= ler_wpM2r (sqr_ge0 T) hDeficitUpper.
have hProduct2:= ler_wpM2l (mulr_ge0 (ler0n R 2) hh) hTBound.
have hBad:(1-d)* T^+2<=8* h by nra.
have hProduct3:= ler_wpM2r hh hdHalf.
have hSquareD:= sqr_ge0 (d-1).
have hScaled:0<=2* d*(X-1+T^+2/2+12* h) by nra.
nra.
Qed.
