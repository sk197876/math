(** Federer (1969), 2.10.47, p. 204: diameter-zero sets require a limiting
    argument in the dyadic comparison when the degree is positive. The
    printed adjacent-scale choice applies only to positive diameters. This
    scalar lemma provides the missing endpoint by arbitrarily small dyadic
    sides and the real power root law. Source context: DyadicScaleBounds.v
    and RealPower.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal lra.
From Federer Require Import DyadicScaleBounds RealPower RealPowerContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [dyadic_power_bounds_force_zero]: supporting
    zero-diameter case of the second comparison in
    2.10.47, p. 204. No convergence axiom or
    positive-multiplier assumption is needed. *)
Theorem dyadic_power_bounds_force_zero (R : realType) (a p : R) i (v : \bar R) :
  (0<=a)%R -> (0<p)%R ->
  (forall j, (i<=j)%N -> v<=(a*real_power (((2^j)%N)%:R^-1) p)%:E) -> v<=0.
Proof.
move=> ha hp hbound; apply/lee_addgt0Pr=> e he; rewrite add0e.
have ha1 : (0<a+1)%R by lra.
have heta : (0<e/(a+1))%R by rewrite divr_gt0.
have hpi : (0<p^-1)%R by rewrite invr_gt0.
pose t := real_power (e/(a+1)) p^-1.
have ht : (0<t)%R := real_power_strictly_positive _ heta.
have [N hN] := dyadic_sides_arbitrarily_small ht.
pose j := maxn i N.
have hij : (i<=j)%N by rewrite /j leq_max leqnn.
have hNj : (N<=j)%N by rewrite /j leq_max leqnn orbT.
have hjpos := @dyadic_side_positive R j.
have hjt : ((((2^j)%N)%:R^-1 : R)<t)%R := le_lt_trans (@dyadic_side_antitone R N j hNj) hN.
have hpow : (real_power (((2^j)%N)%:R^-1) p<=e/(a+1))%R.
  have hh := real_power_monotone (ltW hjpos) (ltW hjt) hp.
  by rewrite /t (@real_power_inverse_power R (e/(a+1)) p (ltW heta) hp) in hh.
apply: le_trans (hbound j hij) _; rewrite lee_fin.
apply: le_trans (ler_wpM2l ha hpow) _.
have haA : (a<=a+1)%R by rewrite lerDl ler01.
have hh := ler_wpM2r (ltW heta) haA.
have heq : ((a+1)*(e/(a+1))=e)%R.
  by rewrite mulrCA divff ?mulr1 //; exact: lt0r_neq0 ha1.
by rewrite heq in hh.
Qed.
