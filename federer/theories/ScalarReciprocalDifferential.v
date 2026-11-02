(** Federer (1969), 3.1.11, p. 223:
    the first derivative of the scalar reciprocal,
    supporting both the reciprocal differentiation
    formula and the flat exponential example. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormHigherCurveDerivativeUP NormedPrimitiveCell.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_reciprocal_half_ball]:
    the reciprocal is defined throughout a ball
    of radius |a|/2 around a nonzero scalar,
    supporting Federer 3.1.11, p. 223. *)
Lemma scalar_reciprocal_half_ball (R : realType) (a h : R) :
  a!= 0 -> `|h|<`|a|/2 -> `|a|/2<`|a+h|.
Proof.
move=> ha hh.
have heq : a=(a+h)+(-h) by rewrite addrK.
have hb := ler_normD (a+h) (-h).
rewrite -heq normrN in hb; lra.
Qed.

(** Source for [scalar_reciprocal_differential]:
    the reciprocal derivative is -a^-2,
    used in Federer 3.1.11, p. 223.
    Its quadratic remainder is proved from the
    exact rational identity and a nonvanishing
    denominator bound on |h|<|a|/2. *)
Theorem scalar_reciprocal_differential (R : realType) (a : R) :
  a!= 0 ->
  has_norm_differential (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) (fun t=>t!= 0) (fun t=>t^-1) a
    (@scalar_coefficient_linear_map R R^o (-((a^-1)^+2))).
Proof.
move=> ha.
have hapos : 0<`|a| by rewrite normr_gt0.
have ha2 : 0<`|a|/2 by rewrite divr_gt0 // ltr0n.
have ha3 : 0<`|a|^+3 := exprn_gt0 _ hapos.
constructor.
- exists (`|a|/2); split=> // h hh.
  have hb := scalar_reciprocal_half_ball ha hh.
  have hn : 0<`|a+h| := lt_trans ha2 hb.
  by move: hn; rewrite normr_gt0.
- exact: scalar_coefficient_linear_bound (@scalar_absolute_value_norm R) _.
- move=> e he.
  have hep : 0<e*`|a|^+3/2 by rewrite divr_gt0 ?mulr_gt0 // ltr0n.
  exists (Num.min (`|a|/2) (e*`|a|^+3/2)).
  split; first by rewrite lt_min ha2 hep.
  move=> h hah; rewrite lt_min=>/andP [hh hsmall].
  have hhalf := scalar_reciprocal_half_ball ha hh.
  have hnew : 0<`|a+h| := lt_trans ha2 hhalf.
  have heq : (a+h)^-1-a^-1-h*(-((a^-1)^+2))=
      h^+2/(a^+2*(a+h)).
    by field; rewrite ha hah.
  change (`|(a+h)^-1-a^-1-h*(-((a^-1)^+2))|<=e*`|h|).
  rewrite heq normf_div normrX normrM normrX.
  have hden : 0<`|a|^+2*`|a+h|.
    exact: mulr_gt0 (exprn_gt0 _ hapos) hnew.
  rewrite ler_pdivrMr //.
  have hn := normr_ge0 h.
  have ha20 : 0<=`|a|^+2 := exprn_ge0 _ (ltW hapos).
  have hlow := ler_wpM2l ha20 (ltW hhalf).
  have helow := ler_wpM2l (ltW he) hlow.
  have halg : e*(`|a|^+2*(`|a|/2))=e*`|a|^+3/2.
    by rewrite !exprS expr0; ring.
  rewrite halg in helow.
  have hcoef : `|h|<=e*(`|a|^+2*`|a+h|).
    exact: le_trans (ltW hsmall) helow.
  have hp := ler_wpM2r hn hcoef.
  rewrite expr2; nra.
Qed.
