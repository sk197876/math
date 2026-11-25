(** Federer (1969), 3.4.10, p. 338,
    citing Bruhat and Whitney, section 11(c),
    p. 159: bounds for the original
    surface where z is negative. These
    are supporting algebraic estimates for its actual
    regular manifold chart, not a regularity premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [bruhat_whitney_negative_root_bounds]: the
    negative-axis part of the example cited in
    3.4.10, p. 338. The original
    cubic equation forces 0<=y<=x^2/(-z);
    its division-free form includes x=0. *)
Theorem bruhat_whitney_negative_root_bounds (R:realType) (x y z:R):
  z<0 ->y*z*(x^+2-z*y^+2)+x^+4=0 ->
  0<=y /\(-z)*y<=x^+2.
Proof.
move=>hz hEquation.
pose c:=-z.
have hC:0<c by rewrite /c oppr_gt0.
have hX2:0<=x^+2:=sqr_ge0 x.
have hY2:0<=y^+2:=sqr_ge0 y.
have hC2:0<c^+2:=exprn_gt0 _ hC.
have hX4:0<=x^+4.
  have h:=sqr_ge0 (x^+2);by rewrite -exprM in h.
have hIdentity:y*z*(x^+2-z*y^+2)+x^+4=
    x^+4-(c*x^+2*y+c^+2*y^+3) by rewrite /c;ring.
rewrite hIdentity in hEquation.
have hEqual:c*x^+2*y+c^+2*y^+3=x^+4 by nra.
have hY:0<=y.
  case hSign:(0<=y);first done.
  have hNegative:y<0 by rewrite ltNge hSign.
  have hY2Positive:0<y^+2.
    have hNonzero:y!=0 by rewrite (lt_eqF hNegative).
    rewrite lt_neqAle eq_sym sqrf_eq0 hNonzero hY2.
    done.
  have hCube:y^+3<0.
    have hId:y^+3=y*y^+2 by ring.
    rewrite hId;nra.
  have hFirst:c*x^+2*y<=0.
    have hNonnegative:0<=c*x^+2:=mulr_ge0 (ltW hC) hX2.
    nra.
  have hSecond:c^+2*y^+3<0 by nra.
  nra.
split;first exact:hY.
have hDifference:x^+2*(x^+2-c*y)=c^+2*y^+3.
  have hId:x^+4=x^+2*x^+2 by ring.
  rewrite hId in hEqual;nra.
case:(eqVneq x 0)=>[hx|hx].
- have hCube:y^+3=0.
    rewrite hx !expr0n /= !mulr0 !mul0r add0r in hEqual.
    have hC20:c^+2!=0 by rewrite (gt_eqF hC2).
    apply:(mulfI hC20);rewrite mulr0;exact:hEqual.
  have hy:y=0 by apply/eqP;move/eqP:hCube;rewrite expf_eq0 /=.
  by rewrite hy mulr0 hx expr0n.
- have hX2Positive:0<x^+2.
    rewrite lt_neqAle eq_sym sqrf_eq0 hx hX2;done.
  have hCubeNonnegative:0<=y^+3:=exprn_ge0 _ hY.
  have hRight:0<=c^+2*y^+3:=mulr_ge0 (ltW hC2) hCubeNonnegative.
  have hGap:0<=x^+2-c*y by nra.
  change (c*y<=x^+2);nra.
Qed.

(** Source for [bruhat_whitney_rescaled_equation]: the
    substitution y=x^2 t in the original
    polynomial of Bruhat and Whitney, section 11(c),
    p. 159, cited in 3.4.10,
    p. 338. The identity holds also
    at x=0; no division is used. *)
Lemma bruhat_whitney_rescaled_equation (R:realType) (x t z:R):
  (x^+2*t)*z*(x^+2-z*(x^+2*t)^+2)+x^+4=
    x^+4*(z*t-z^+2*x^+2*t^+3+1).
Proof. ring. Qed.
