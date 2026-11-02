(** Federer (1969), 2.9.19, pp. 164–165: finite derivatives control the
    increments over every short interval containing the base point. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_derivative_small_displacement_error]: supporting linear
    error estimate in Federer 2.9.19, p. 165 Multiply the actual
    nonzero-increment difference-quotient estimate by |h|. At h=0 both
    errors vanish, so the weak bound includes that boundary case. *)
Lemma real_derivative_small_displacement_error (R : realType) (g : R -> R) (x v e : R) :
  has_real_curve_derivative g x v -> 0<e -> exists d : R, 0<d /\
    forall h : R, `|h|<d -> `|g (x+h)-g x-v*h|<=e*`|h|.
Proof.
move=> hder he; have [d [hd hB]] := hder e he.
exists d; split=> // h hsmall.
case: (eqVneq h 0)=> [->|hn].
- by rewrite addr0 subrr mulr0 subrr !normr0 mulr0.
- have hp : 0<`|h| by rewrite normr_gt0.
  have hq := hB h (ltac:(by apply/andP; split)).
  have heq : ((g (x+h)-g x)/h-v)*h=g (x+h)-g x-v*h.
    by field; rewrite (negbTE hn).
  rewrite -heq normrM; exact (ler_wpM2r (normr_ge0 h) (ltW hq)).
Qed.

(** Source for [real_derivative_interval_error]: supporting short-interval
    estimate in Federer 2.9.19, p. 165 Split the increment at x and add the
    two displacement errors. Since a<=x<=b, the two absolute widths sum
    exactly to b-a. Endpoint equality is allowed and does not require a
    quotient at zero. *)
Lemma real_derivative_interval_error (R : realType) (g : R -> R) (x v e : R) :
  has_real_curve_derivative g x v -> 0<e -> exists d : R, 0<d /\
    forall a b : R, a<=x<=b -> 0<b-a<d ->
      `|g b-g a-v*(b-a)|<=e*(b-a).
Proof.
move=> hder he.
have [d [hd hB]] := real_derivative_small_displacement_error hder he.
exists d; split=> // a b /andP [hax hxb] /andP [hw hwd].
have han : a-x<=0 by rewrite subr_le0.
have hbn : 0<=b-x by rewrite subr_ge0.
have hna : `|a-x|=x-a by rewrite (ler0_norm han) opprB.
have hnb : `|b-x|=b-x by rewrite (ger0_norm hbn).
have hda : `|a-x|<d by rewrite hna; lra.
have hdb : `|b-x|<d by rewrite hnb; lra.
have ha := hB (a-x) hda.
have hb := hB (b-x) hdb.
have hxa : x+(a-x)=a by rewrite addrC subrK.
have hxb' : x+(b-x)=b by rewrite addrC subrK.
rewrite hxa hna in ha; rewrite hxb' hnb in hb.
have heq : g b-g a-v*(b-a)=
    (g b-g x-v*(b-x))-(g a-g x-v*(a-x)) by ring.
rewrite heq; apply: le_trans (ler_normB _ _) _.
apply: le_trans (lerD hb ha) _.
have heq' : e*(b-x)+e*(x-a)=e*(b-a) by ring.
by rewrite heq'.
Qed.

(** Source for [real_derivative_interval_bounds]: supporting two-sided
    short-interval increment bounds in Federer 2.9.19, pp. 164–165 The norm
    error estimate implies the lower and upper affine bounds, for arbitrary
    finite derivative value v. *)
Lemma real_derivative_interval_bounds (R : realType) (g : R -> R) (x v e : R) :
  has_real_curve_derivative g x v -> 0<e -> exists d : R, 0<d /\
    forall a b : R, a<=x<=b -> 0<b-a<d ->
      (v-e)*(b-a)<=g b-g a /\ g b-g a<=(v+e)*(b-a).
Proof.
move=> hder he; have [d [hd hB]] := real_derivative_interval_error hder he.
exists d; split=> // a b haxb hw.
have herror := hB a b haxb hw.
move: herror; rewrite ler_norml=> /andP [hl hu].
rewrite mulrBl mulrDl; split; lra.
Qed.
