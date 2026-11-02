(** Federer (1969), 2.9.22, pp. 167–168: the variation conclusion of 2.9.19
    extends to norm derivatives. The supporting estimate below is the normed
    version of the two-endpoint error calculation on p. 165. It uses the
    actual derivative's remainder, without assuming the desired arc-length
    derivative equality. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealNormUP NormedCurveDerivativeUP NormedDerivativeRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normed_derivative_interval_error]: supporting normed
    interval estimate for Federer 2.9.22, pp. 167–168, extending the
    calculation of 2.9.19, p. 165 Add the actual remainder bounds at both
    endpoints of a short interval containing x. Endpoint equality is
    included; no quotient at zero is needed. *)
Lemma normed_derivative_interval_error (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> E) (x e : R) (v : E) :
  has_normed_curve_derivative N g x v -> 0<e -> exists d : R, 0<d /\
    forall a b : R, a<=x<=b -> 0<b-a<d ->
      N (g b-g a-(b-a) *: v)<=e*(b-a).
Proof.
move=> hg he; have [d [hd hB]] := normed_derivative_small_displacement_error hN hg he.
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
have heq : g b-g a-(b-a) *: v=
    (g b-g x-(b-x) *: v)-(g a-g x-(a-x) *: v).
  have hs : (b-a) *: v=(b-x) *: v-(a-x) *: v.
    rewrite -scalerBl; congr (_ *: v); ring.
  rewrite hs !opprB [(a-x) *: v+(g x-g a)]addrC.
  rewrite [RHS]addrACA.
  rewrite [g b-g x+(g x-g a)]addrA subrK.
  by rewrite [-((b-x) *: v)+(a-x) *: v]addrC.
rewrite heq; apply: le_trans (real_seminorm_triangle hN.1 _ _) _.
rewrite (real_seminorm_negate hN.1).
apply: le_trans (lerD hb ha) _.
have heq' : e*(b-x)+e*(x-a)=e*(b-a) by ring.
by rewrite heq'.
Qed.
