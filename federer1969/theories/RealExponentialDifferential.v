(** Federer (1969), 3.1.11, p. 223:
    elementary differentiability of the exponential,
    supporting the smooth cutoff example. The proof
    uses the project's sealed exponential laws and derives
    the remainder estimate without an external calculus library. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals lra ring.
From Federer Require Import Hom RealNormUP RealExponentialUP RealExponentialSealed
  NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section ExponentialDifferential.
Variable R : realType.
Local Notation E := (@RealExponential.exponential R).
Local Notation hE := (@RealExponential.laws R).

(** Source for [real_exponential_quadratic_remainder]:
    a supporting second-order bound at zero for the
    exponential in Federer 3.1.11, p. 223.
    It follows from the addition and tangent laws already
    proved for the sealed exponential. *)
Lemma real_exponential_quadratic_remainder t :
  `|t|<= 1/2 -> `|E t-1-t|<= 2*t^+2.
Proof.
move=> ht.
have htupper : t<= 1/2 := le_trans (ler_norm t) ht.
have hpos := real_exponential_positive hE t.
have hlo := real_exponential_tangent hE t.
have hneg := real_exponential_tangent hE (-t).
have hprod : E t*E (-t)= 1.
  by rewrite -(real_exponential_add hE) addrN (real_exponential_zero hE).
have hbound := ler_wpM2l (ltW hpos) hneg.
rewrite hprod in hbound.
have herr : 0<=E t-1-t by lra.
rewrite ger0_norm //.
have hden : 1/2<= 1-t by lra.
have herrprod : (E t-1-t)*(1-t)<=t^+2 by rewrite expr2; nra.
have hmul := ler_wpM2l herr hden.
nra.
Qed.

(** Source for [real_exponential_linear_term]:
    the first differential of exp at a is multiplication
    by exp(a), supporting Federer 3.1.11, p. 223. *)
Definition real_exponential_linear_term (a : R) : Hom R^o R^o.
Proof.
apply: (@HomMap R R^o R^o (fun t=>E a*t)).
apply/asboolP=> c t u; change (E a*(c*t+u)=c*(E a*t)+E a*u); ring.
Defined.

(** Source for [real_exponential_differential]:
    differentiability of the exponential used in the
    smooth example of Federer 3.1.11, p. 223.
    The derivative and its error bound are derived from
    the abstract scalar laws. *)
Theorem real_exponential_differential a :
  has_norm_differential (fun t : R^o=>`|t|) (fun t : R^o=>`|t|)
    (fun _=>True) E a (real_exponential_linear_term a).
Proof.
have hpos := real_exponential_positive hE a.
constructor.
- exists 1; split; first exact: ltr01; by move=> h _.
- exists (E a); split; first exact: ltW hpos.
  move=> h; change (`|E a*h|<=E a*`|h|).
  by rewrite normrM ger0_norm //; exact: ltW hpos.
- move=> e he.
  have hden : 0<2*E a+1 by nra.
  have hquot : 0<e/(2*E a+1) by rewrite divr_gt0.
  exists (Num.min (1/2) (e/(2*E a+1))); split.
  + rewrite lt_min hquot andbT; by rewrite divr_gt0 // ltr0n.
  + move=> h _; rewrite lt_min=> /andP [hh hs].
    have hb := real_exponential_quadratic_remainder (ltW hh).
    change (`|E (a+h)-E a-E a*h|<=e*`|h|).
    have hid : E (a+h)-E a-E a*h=E a*(E h-1-h).
      rewrite (real_exponential_add hE); ring.
    rewrite hid normrM (ger0_norm (ltW hpos)).
    apply: le_trans (ler_wpM2l (ltW hpos) hb) _.
    have hs' : (2*E a+1)*`|h|<e.
      by move: hs; rewrite ltr_pdivlMr // mulrC.
    have hn := normr_ge0 h.
    have hcoef : 2*E a*`|h|<=e by nra.
    have hlast := ler_wpM2r hn hcoef.
    have hsq : h^+2=`|h|^+2 by rewrite -normrX ger0_norm // sqr_ge0.
    rewrite hsq expr2; nra.
Qed.
End ExponentialDifferential.
