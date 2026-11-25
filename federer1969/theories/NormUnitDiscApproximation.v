(** Federer (1969), 3.2.26(2), p. 261: a
    normalized secant which is close to the tangent
    plane is close to its unit disc. This elementary
    rescaling estimate expands the thin-cover containment. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_near_unit_rescaling]: supporting
    unit-disc approximation for C(w,r) in 3.2.26(2),
    p. 261. If a unit-ball vector is within e
    of y, then y/(1+e) is a unit-ball vector
    within 2e of it. No dimension or inner product
    is required for this norm calculation. *)
Lemma norm_near_unit_rescaling (R:realType) (V:lmodType R) (N:V->R)
    (hN:is_real_norm N) (v y:V) (e:R):
  0<=e ->N v<=1 ->N (v-y)<=e ->
  N ((1+e)^-1*:y)<=1 /\N (v-(1+e)^-1*:y)<=2*e.
Proof.
move=>he hv hError.
have hPositive:0<1+e by lra.
have hNonzero:1+e!=0 by rewrite gt_eqF.
have hY:N y<=1+e.
  have hTriangle:=real_seminorm_triangle hN.1 (y-v) v.
  rewrite subrK (real_seminorm_subtract hN.1) in hTriangle.
  lra.
have hInverse:0<=(1+e)^-1 by rewrite invr_ge0; exact:ltW hPositive.
have hInverseLe:(1+e)^-1<=1 by rewrite invf_le1 //; lra.
have hCoefficient:0<=1-(1+e)^-1 by rewrite subr_ge0.
have hProduct:(1-(1+e)^-1)*(1+e)=e.
  rewrite mulrBl mul1r mulVf //; ring.
split.
- rewrite (real_seminorm_scale hN.1) (ger0_norm hInverse).
  have h:=ler_wpM2l hInverse hY; by rewrite mulVf in h.
- have hDifference:y-(1+e)^-1*:y=(1-(1+e)^-1)*:y.
    by rewrite scalerBl scale1r.
  have hRemainder:N (y-(1+e)^-1*:y)<=e.
    rewrite hDifference (real_seminorm_scale hN.1) (ger0_norm hCoefficient).
    have h:=ler_wpM2l hCoefficient hY; by rewrite hProduct in h.
  have hTriangle:=real_seminorm_triangle hN.1 (v-y) (y-(1+e)^-1*:y).
  rewrite subrKA in hTriangle.
  lra.
Qed.
