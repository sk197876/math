(** Federer (1969), 2.10.28, pp. 191, 193: t^m is an admissible strictly
    concave gauge when 0<m<1. This supporting proof derives strict concavity
    from the project's proved weighted arithmetic-geometric inequality
    2.4.13, p. 88, including zero endpoints. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealPower RealPowerSuccessor WeightedArithmeticGeometricMean.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [fractional_power_arithmetic_tangent_strict]:
    supporting strict power tangent comparison
    for the gauge in 2.10.28, p. 191.
    Apply 2.4.13 to weights m,1-m and
    bases a,x; its equality criterion includes a = 0. *)
Lemma fractional_power_arithmetic_tangent_strict (R : realType) (m a x : R) :
  0<m -> m<1 -> 0<=a -> 0<x -> a!=x ->
  real_power a m*real_power x (1-m)<m*a+(1-m)*x.
Proof.
move=> hm hm1 ha hx hne.
have hq : 0<1-m by lra.
have hsum : m+(1-m) = 1 by lra.
have hw := @weighted_arithmetic_geometric_mean R m (1-m) a x hm hq hsum ha (ltW hx).
rewrite lt_neqAle hw andbT; apply/eqP=> he.
have heq := (@weighted_arithmetic_geometric_mean_equality R m (1-m) a x hm hq hsum ha (ltW hx)).1 he.
by move: hne; rewrite heq eqxx.
Qed.

(** Source for [fractional_power_strict_concavity]: supporting
    strict concavity of t^m on the whole
    nonnegative axis for 0<m<1, required by
    2.10.28, pp. 191, 193. Both
    endpoints may be zero individually; distinctness
    ensures their interior weighted mean is positive. *)
Theorem fractional_power_strict_concavity (R : realType) (m a b t : R) :
  0<m -> m<1 -> 0<=a -> 0<=b -> a!=b -> 0<t -> t<1 ->
  (1-t)*real_power a m+t*real_power b m<real_power ((1-t)*a+t*b) m.
Proof.
move=> hm hm1 ha hb hab ht ht1.
pose x := (1-t)*a+t*b.
have hweight : 0<1-t by lra.
have hxa : 0<=(1-t)*a := mulr_ge0 (ltW hweight) ha.
have hxb : 0<=t*b := mulr_ge0 (ltW ht) hb.
have hx : 0<x.
  case: (eqVneq a 0)=> [ha0|ha0].
  - have hbne : b!=0 by move: hab; rewrite ha0 eq_sym.
    have hb0 : 0<b by rewrite lt_neqAle eq_sym hbne hb.
    have hh : 0<t*b := mulr_gt0 ht hb0; rewrite /x; lra.
  - have hap : 0<a by rewrite lt_neqAle eq_sym ha0 ha.
    have hh : 0<(1-t)*a := mulr_gt0 hweight hap; rewrite /x; lra.
have hax : a!=x.
  apply/eqP=> he; have hh : t*(a-b) = 0 by rewrite /x in he; lra.
  have hab0 : a-b!=0 by rewrite subr_eq0.
  have ht0 : t!=0 by rewrite gt_eqF.
  have hh0 : t*(a-b)!=0 := mulf_neq0 ht0 hab0.
  by move: hh0; rewrite hh eqxx.
have hbx : b!=x.
  apply/eqP=> he; have hh : (1-t)*(b-a) = 0 by rewrite /x in he; lra.
  have hba0 : b-a!=0 by rewrite subr_eq0 eq_sym.
  have hw0 : 1-t!=0 by rewrite gt_eqF.
  have hh0 : (1-t)*(b-a)!=0 := mulf_neq0 hw0 hba0.
  by move: hh0; rewrite hh eqxx.
have hA := @fractional_power_arithmetic_tangent_strict R m a x hm hm1 ha hx hax.
have hB := @fractional_power_arithmetic_tangent_strict R m b x hm hm1 hb hx hbx.
have hWA : (1-t)*(real_power a m*real_power x (1-m))<(1-t)*(m*a+(1-m)*x).
  by rewrite (ltr_pM2l hweight).
have hWB : t*(real_power b m*real_power x (1-m))<t*(m*b+(1-m)*x).
  by rewrite (ltr_pM2l ht).
have hh := ltrD hWA hWB.
have hright : (1-t)*(m*a+(1-m)*x)+t*(m*b+(1-m)*x)=x by rewrite /x; lra.
have hleft : (1-t)*(real_power a m*real_power x (1-m))+
    t*(real_power b m*real_power x (1-m))=
    ((1-t)*real_power a m+t*real_power b m)*real_power x (1-m) by lra.
rewrite hright hleft in hh.
have hxq := @real_power_strictly_positive R x (1-m) hx.
have hprod : real_power x m*real_power x (1-m)=x.
  rewrite -real_power_add_exponents_positive //; have he : m+(1-m) = 1 by lra.
  by rewrite he real_power_one_exponent // ltW.
have hh' : ((1-t)*real_power a m+t*real_power b m)*real_power x (1-m)<
    real_power x m*real_power x (1-m) by rewrite hprod.
by move: hh'; rewrite (ltr_pM2r hxq).
Qed.
