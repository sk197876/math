(** Federer (1969), 3.4.10, p. 338:
    uniqueness of the original y coordinate above
    every fixed (x,z) with negative z.
    Reuse the proved nonnegative-root bound and
    monotonicity of positive powers. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import BruhatWhitneyNegativeRootBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [bruhat_whitney_negative_root_unique]: the
    actual graph near the negative axis in the
    example cited by 3.4.10, p. 338.
    The negative-root polynomial is strictly decreasing
    in its nonnegative y coordinate. *)
Theorem bruhat_whitney_negative_root_unique (R:realType) (x y w z:R):
  z<0 ->y*z*(x^+2-z*y^+2)+x^+4=0 ->
  w*z*(x^+2-z*w^+2)+x^+4=0 ->y=w.
Proof.
move=>hz hY hW.
have hy:=(@bruhat_whitney_negative_root_bounds R x y z hz hY).1.
have hw:=(@bruhat_whitney_negative_root_bounds R x w z hz hW).1.
pose c:=-z.
have hc:0<c by rewrite /c oppr_gt0.
have hc2:0<c^+2:=exprn_gt0 _ hc.
have hx2:0<=x^+2:=sqr_ge0 x.
have hEqual:c*x^+2*y+c^+2*y^+3=c*x^+2*w+c^+2*w^+3.
  have hId t:t*z*(x^+2-z*t^+2)+x^+4=
      x^+4-(c*x^+2*t+c^+2*t^+3) by rewrite /c;ring.
  rewrite (hId y) in hY.
  rewrite (hId w) in hW.
  move/eqP:hY;rewrite subr_eq0=>/eqP hY.
  move/eqP:hW;rewrite subr_eq0=>/eqP hW.
  by rewrite -hY -hW.
have hStrict u v (hu:0<=u) (hv:0<=v) (hUV:u<v):
    c*x^+2*u+c^+2*u^+3<c*x^+2*v+c^+2*v^+3.
  have hPower:u^+3<v^+3 by rewrite ltrXn2r //.
  have hFirst:c*x^+2*u<=c*x^+2*v.
    have hCoefficient:0<=c*x^+2:=mulr_ge0 (ltW hc) hx2.
    nra.
  have hSecond:c^+2*u^+3<c^+2*v^+3 by rewrite ltr_pM2l.
  nra.
case:(ltgtP y w)=>[h|h|h];last exact:h.
- have hContradiction:=hStrict y w hy hw h;rewrite hEqual ltxx in hContradiction;done.
- have hContradiction:=hStrict w y hw hy h;rewrite hEqual ltxx in hContradiction;done.
Qed.
