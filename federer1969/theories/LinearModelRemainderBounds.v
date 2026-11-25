(** Federer (1969), 3.2.2, p. 242: subtract the controlled
    differentiability remainder from a fixed linear model to obtain
    both Lipschitz bounds on a small Borel piece. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [bilipschitz_margin_exists]: the choice of epsilon
    in the first sentence of the proof of Federer 3.2.2, p. 242.
    For lambda>1 choose a positive margin strictly between its
    reciprocal and one, and between one and lambda. *)
Lemma bilipschitz_margin_exists (R:realType) (lambda:R) :
  1<lambda -> exists e:R,0<e /\ lambda^-1+e<1 /\ 1<lambda-e.
Proof.
move=>hL.
have hpos:0<lambda:=lt_trans ltr01 hL.
have h0:lambda!=0 by rewrite gt_eqF.
have hi:0<lambda^-1 by rewrite invr_gt0.
have hh:lambda^-1*lambda= 1 by rewrite mulVf.
have hInv:lambda^-1<1 by nra.
pose e:=Num.min ((1-lambda^-1)/2) ((lambda-1)/2).
have he:0<e by rewrite /e lt_min; apply/andP; split; rewrite divr_gt0 // subr_gt0.
have he1:e<=(1-lambda^-1)/2 by rewrite /e ge_min lexx.
have he2:e<=(lambda-1)/2 by rewrite /e ge_min lexx orbT.
exists e; split; first exact he.
split; nra.
Qed.

(** Source for [linear_model_remainder_bounds]: the two displayed
    increment estimates in Federer 3.2.2, p. 242. Upper and lower
    bounds for the differential, with the epsilon margin, absorb
    a remainder bounded by epsilon times the model increment.
    Supporting lemma, valid in arbitrary real normed spaces. *)
Theorem linear_model_remainder_bounds (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNY:is_real_norm NY)
    (s:Hom X X) (D:Hom X Y) (f:X->Y) a b lambda e :
  (lambda^-1+e)*NX (s (b-a))<=NY (D (b-a)) ->
  NY (D (b-a))<=(lambda-e)*NX (s (b-a)) ->
  NY (f b-f a-D (b-a))<=e*NX (s (b-a)) ->
  lambda^-1*NX (s (b-a))<=NY (f b-f a) /\
  NY (f b-f a)<=lambda*NX (s (b-a)).
Proof.
move=>hl hu hr.
pose r:=f b-f a-D (b-a).
have heq:r+D (b-a)=f b-f a by rewrite /r subrK.
have hUpper:=real_seminorm_triangle hNY.1 r (D (b-a)).
rewrite heq in hUpper.
have heq2:(f b-f a)-r=D (b-a) by rewrite /r opprB addrCA subrr addr0.
have hLower:=real_seminorm_triangle hNY.1 (f b-f a) (-r).
change (is_true (NY ((f b-f a)-r)<=NY (f b-f a)+NY (-r))) in hLower.
rewrite heq2 (real_seminorm_negate hNY.1) in hLower.
split; nra.
Qed.
