(** Federer 2.10.2(1), p. 171, circle at a fixed cutoff. Independent
    scalar bounds for the two diameter ranges, before choosing local
    witnesses. The final covering theorem will discharge alpha>2 using
    the actual unit-disc volume theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_planar_circle_cutoff_constants]: Federer 2.10.2(1),
    p. 171; supporting simultaneous scalar conditions for a uniform
    generator cost bound strictly below half the circle's total length.
    No measure comparison is part of this independent specification. *)
Definition is_planar_circle_cutoff_constants (R:realType)
    (alpha delta radius coeff:R):Prop:=
  0<delta<1/2 /\ alpha^-1<delta /\ 1<radius /\
  radius^+2  =  2-2*delta /\ delta^-1<=coeff /\
  alpha/radius<=coeff /\ 0<coeff<alpha.

(** Source for [planar_circle_cutoff_constants_exist]: Federer 2.10.2(1),
    p. 171; supporting finite scalar witnesses for the actual circle
    cutoff argument. Only existence is exported; no chosen auxiliary
    constants or hidden measure conclusions are assumed. *)
Theorem planar_circle_cutoff_constants_exist (R:realType) (alpha:R):
  2<alpha -> exists delta radius coeff,
    is_planar_circle_cutoff_constants alpha delta radius coeff.
Proof.
move=>ha2.
have h2:(0<2:>R) by rewrite ltr0n.
have ha:0<alpha:=lt_trans h2 ha2.
have hane:alpha!=0:=lt0r_neq0 ha.
pose i:=alpha^-1.
pose half:=(1/2:R).
have hi:0<i by rewrite /i invr_gt0.
have hHalf:0<half by rewrite /half divr_gt0.
have hHalf2:half*2  =  1 by rewrite /half divfK ?pnatr_eq0.
have hiAlpha:i*alpha  =  1 by rewrite /i mulVf.
have hiTwo:i*2<1.
  have hh:i*2<i*alpha by rewrite (ltr_pM2l hi).
  by rewrite hiAlpha in hh.
have hiHalf:i<half by nra.
pose delta:=(i+half)/2.
have hDelta2:delta*2 = i+half by rewrite /delta divfK ?pnatr_eq0.
have hDelta:0<delta by rewrite /delta divr_gt0 // addr_gt0.
have hIDelta:i<delta by nra.
have hDeltaHalf:delta<half by nra.
have hRad:0<2-2*delta by nra.
pose radius:=Num.sqrt (2-2*delta).
have hRadius:0<radius by rewrite /radius sqrtr_gt0.
have hRadius2:radius^+2  =  2-2*delta:=sqr_sqrtr (ltW hRad).
have hRadius1:1<radius by nra.
have hDeltaInv:0<delta^-1 by rewrite invr_gt0.
have hDeltaNe:delta!=0:=lt0r_neq0 hDelta.
have hDeltaInvEq:delta^-1*delta  =  1 by rewrite mulVf.
have hAlphaDelta:1<alpha*delta.
  have hh:i*alpha<delta*alpha by rewrite (ltr_pM2r ha).
  by rewrite hiAlpha mulrC in hh.
have hInvAlpha:delta^-1<alpha.
  rewrite -(ltr_pM2r hDelta) hDeltaInvEq; exact:hAlphaDelta.
have hRatio:alpha/radius<alpha.
  rewrite (ltr_pdivrMr _ _ hRadius) -{1}[alpha]mulr1 (ltr_pM2l ha).
  exact:hRadius1.
pose coeff:=Order.max delta^-1 (alpha/radius).
have hCoeff:0<coeff by rewrite /coeff lt_max hDeltaInv.
have hCoeffAlpha:coeff<alpha by rewrite /coeff gt_max hInvAlpha hRatio.
have hInvCoeff:delta^-1<=coeff by rewrite /coeff le_max lexx.
have hRatioCoeff:alpha/radius<=coeff by rewrite /coeff le_max lexx orbT.
exists delta,radius,coeff; split; first by apply/andP; split=>//; exact:hDeltaHalf.
split; first exact:hIDelta.
split; first exact:hRadius1.
split; first exact:hRadius2.
split; first exact:hInvCoeff.
split; first exact:hRatioCoeff.
by apply/andP; split.
Qed.
