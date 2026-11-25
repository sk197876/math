(** Federer (1969), 3.2.34, p. 271: the nearest-segment
    identity determines the differential on that direction.
    This supporting one-sided argument works in normed spaces. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_from_ray_increment]: the
    deduction Df(x)(s-x)=-|s-x| from the displayed
    segment identity in Federer 3.2.34, p. 271.
    Actual directional difference quotients converge to L(v);
    their exact values on positive small increments force
    that value to be c. Neither a two-sided segment
    identity nor additional differentiability is assumed. *)
Lemma norm_differential_from_ray_increment (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (f:X->Y) a (L:Hom X Y) v c:
  has_norm_differential NX NY A f a L ->
  (forall t:R,0<=t<=1 ->f (a+t*:v)=f a+t*:c) ->L v=c.
Proof.
move=>hD hRay.
case:(eqVneq c (L v))=>[he|hne]; first exact:esym he.
have hp:0<NY (c-L v).
  by rewrite (real_norm_positive hNY.1 hNY.2) subr_eq0.
have [d [hd hLimit]]:=norm_differential_directional_limit hNX hNY hD v hp.
pose t:R:=Num.min d 1/2.
have hm:0<Num.min d 1 by rewrite lt_min hd ltr01.
have hmd:Num.min d 1<=d by rewrite ge_min lexx.
have hm1:Num.min d 1<=1 by rewrite ge_min lexx orbT.
have ht:0<t by rewrite /t divr_gt0 // ltr0n.
have htd:t<d by rewrite /t; lra.
have ht1:t<=1 by rewrite /t; lra.
have hArg:0<`|t|<d by rewrite (ger0_norm (ltW ht)); apply/andP; split.
have hError:=hLimit t hArg.
have hSegment:0<=t<=1 by apply/andP; split; [exact:ltW ht|exact ht1].
have hQuotient:t^-1*:(f (a+t*:v)-f a)=c.
  rewrite (hRay t hSegment) addrAC subrr add0r scalerA.
  by rewrite mulVf ?scale1r // gt_eqF.
by rewrite hQuotient ltxx in hError.
Qed.
