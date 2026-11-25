(** Federer (1969), 2.9.22, p. 168: small first-order mean errors over
    intervals containing x imply the actual two-sided norm derivative. This
    supporting local calculus lemma handles both orientations and the zero
    increment directly. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealNormUP NormedCurveDerivativeUP NormedDerivativeRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normed_interval_error_derivative]: direct
    supporting implication from the norm-error display to g'(x)=v,
    Federer 2.9.22, p. 168. Test intervals [x,x+h] for
    h>0 and [x+h,x] for h<0. Symmetry of the norm
    identifies their remainders; no one-sided derivative is
    substituted for the printed two-sided limit. *)
Theorem normed_interval_error_derivative (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> E) (x : R) (v : E) :
  (forall e : R, 0<e -> exists d : R, 0<d /\ forall a b : R,
    a<b -> a<=x<=b -> b-a<d -> N (g b-g a-(b-a) *: v)/(b-a)<e) ->
  has_normed_curve_derivative N g x v.
Proof.
move=> hc; apply: (normed_derivative_from_displacement_error hN)=> e he.
have [d [hd hB]] := hc e he.
exists d; split=> // h hsmall.
case: (eqVneq h 0)=> [->|hn].
  by rewrite addr0 subrr scale0r subrr (real_seminorm_zero hN.1) normr0 mulr0.
case: (ltP 0 h)=> [hp|h0].
- have hxb : x<x+h by rewrite ltrDl.
  have haxb : x<=x<=x+h by rewrite lexx andTb; exact: ltW hxb.
  have hwidth : x+h-x=h by rewrite addrAC subrr add0r.
  have hh : h<d by move: hsmall; rewrite (ger0_norm (ltW hp)).
  have hb := hB x (x+h) hxb haxb (ltac:(by rewrite hwidth)).
  rewrite hwidth ltr_pdivrMr // in hb.
  by rewrite (ger0_norm (ltW hp)); exact: ltW hb.
- have hm : h<0 by rewrite lt_neqAle hn h0.
  have hxb : x+h<x by lra.
  have haxb : x+h<=x<=x.
    apply/andP; split; [exact: ltW hxb|exact: lexx].
  have hwidth : x-(x+h)= -h by rewrite opprD addrA subrr add0r.
  have hh : -h<d by move: hsmall; rewrite (ltr0_norm hm).
  have hb := hB (x+h) x hxb haxb (ltac:(by rewrite hwidth)).
  have hpos : 0< -h by rewrite oppr_gt0.
  rewrite hwidth ltr_pdivrMr // in hb.
  have hid : g x-g (x+h)-(-h) *: v= -(g (x+h)-g x-h *: v).
    by rewrite scaleNr opprK !opprB addrC.
  rewrite hid (real_seminorm_negate hN.1) in hb.
  by rewrite (ltr0_norm hm); exact: ltW hb.
Qed.
