(** Federer (1969), 2.9.22, p. 168, final chain-rule argument: control the
    increment error before dividing by its size. These supporting laws
    express the actual norm derivative by a first-order remainder, including
    increment zero. Chapter 21 has no corresponding Banach-chain argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealNormUP NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normed_derivative_small_displacement_error]:
    supporting first-order error for the last quotient display
    in Federer 2.9.22, p. 168. Multiplication by |h| turns
    the punctured norm estimate into a remainder bound which
    also holds at h=0. No chain rule is assumed. *)
Lemma normed_derivative_small_displacement_error (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> E) (x e : R) v :
  has_normed_curve_derivative N g x v -> 0<e -> exists d : R, 0<d /\
    forall h : R, `|h|<d -> N (g (x+h)-g x-h *: v)<=e * `|h|.
Proof.
move=> hg he; have [d [hd hB]] := hg e he.
exists d; split=> // h hsmall.
case: (eqVneq h 0)=> [->|hn].
  by rewrite addr0 subrr scale0r subrr (real_seminorm_zero hN.1) normr0 mulr0.
have hh : 0<`|h|<d by apply/andP; split=> //; rewrite normr_gt0.
have hq := hB h hh.
have hid : h *: (h^-1 *: (g (x+h)-g x)-v)=g (x+h)-g x-h *: v.
  by rewrite scalerBr scalerA mulfV // scale1r.
rewrite -hid (real_seminorm_scale hN.1).
have hm := ler_wpM2l (normr_ge0 h) (ltW hq).
by rewrite [X in _<=X]mulrC in hm.
Qed.

(** Source for [normed_derivative_from_displacement_error]:
    supporting converse first-order estimate for Federer 2.9.22,
    p. 168. A weak epsilon remainder bound at every small
    increment yields the strict punctured difference-quotient limit
    by using half the requested error. *)
Lemma normed_derivative_from_displacement_error (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> E) (x : R) v :
  (forall e : R, 0<e -> exists d : R, 0<d /\
    forall h : R, `|h|<d -> N (g (x+h)-g x-h *: v)<=e * `|h|) ->
  has_normed_curve_derivative N g x v.
Proof.
move=> hc e he.
have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have [d [hd hB]] := hc (e/2) he2.
exists d; split=> // h /andP [hh hhd].
have hn : h!=0 by move: hh; rewrite normr_gt0.
have hb := hB h hhd.
have hid : h^-1 *: (g (x+h)-g x-h *: v)=h^-1 *: (g (x+h)-g x)-v.
  by rewrite scalerBr scalerA mulVf // scale1r.
rewrite -hid (real_seminorm_scale hN.1) normfV mulrC.
have hq : N (g (x+h)-g x-h *: v)/`|h|<=e/2.
  by rewrite ler_pdivrMr // mulrC.
apply: le_lt_trans hq _; by lra.
Qed.
