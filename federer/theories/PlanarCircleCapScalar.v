(** Federer 2.10.2(1), p. 171, circle at a fixed diameter cutoff.
    Supporting elementary estimate: projection of a unit-circle cap onto
    its transverse coordinate has inverse Lipschitz bound 1/delta when
    the forward coordinate is at least delta>0. No arc length formula or
    trigonometric parametrization is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [circle_cap_transverse_square_bound]: Federer 2.10.2(1),
    p. 171; supporting chord estimate in orthonormal coordinates. Both
    points are on the actual unit circle and have first coordinate at
    least delta. The final inequality is the squared inverse bound. *)
Lemma circle_cap_transverse_square_bound (R:realType) (delta u v s t:R):
  0<delta -> delta<=u -> delta<=v ->
  u^+2+s^+2 = 1 -> v^+2+t^+2 = 1 ->
  delta^+2*((u-v)^+2+(s-t)^+2)<=(s-t)^+2.
Proof.
move=>hd hu hv hUnitU hUnitV.
have hDiff:0<=(u-v)^+2+(s-t)^+2 by apply:addr_ge0; exact:sqr_ge0.
have hSum:0<=4-(u+v)^+2-(s+t)^+2.
  have h0:=sqr_ge0 (u-v); have h1:=sqr_ge0 (s-t); nra.
have hRel:(u+v)*(u-v)= -((s+t)*(s-t)) by nra.
have hSquare:=congr1 (fun x:R=>x^+2) hRel.
rewrite sqrrN !exprMn in hSquare.
have hIdentity:(u+v)^+2*((u-v)^+2+(s-t)^+2)=
    ((u+v)^+2+(s+t)^+2)*(s-t)^+2 by nra.
have hLower:0<=(u+v)^+2-4*delta^+2 by nra.
have hLeft:=mulr_ge0 hLower hDiff.
have hRight:=mulr_ge0 hSum (sqr_ge0 (s-t)).
nra.
Qed.
