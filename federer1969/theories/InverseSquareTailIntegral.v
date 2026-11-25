(** Federer (1969), 2.6.3(2), p. 118: the elementary integral of x^-2 from
    one to infinity equals one. This proof follows that route with the
    actual Lebesgue measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderLimit RealScalarOrderLimits
  StieltjesSegmentIdentity RealSubsetIntegralGraph MeasureIntegralUP MeasureSubsetIntegral
  SummableRealFunctionUP RealIncreasingIntegralLimit ReciprocalSequenceLimits
  LebesgueScalarMeasure InverseSquareSegmentIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inverse_square_lebesgue_tail]: the actual improper Lebesgue
    integral used in Federer 2.6.3(2), p. 118 Increasing restrictions to
    [1,n+2] have integrals 1-1/(n+2), converging to one. *)
Theorem inverse_square_lebesgue_tail (R : realType) :
  is_measure_subset_integral (@lebesgue_scalar_measure R) [set x : R | 1 <= x]
    (real_total_integrand (fun x => (x^-1)^+2)) 1%:E.
Proof.
pose fn (n : nat) (x : R) := if (1 <= x) && (x <= n.+2%:R) then (x^-1)^+2 else 0.
pose g (x : R) := if 1 <= x then (x^-1)^+2 else 0.
pose an (n : nat) := (1-(n.+2%:R : R)^-1)%:E.
have hp n x : 0 <= fn n x.
  rewrite /fn; case: ifP=> _; last exact: lexx.
  exact: sqr_ge0.
have hmon n x : fn n x <= fn n.+1 x.
  rewrite /fn; case: ifP=> hx.
  - have /andP[hx1 hxn] := hx.
    have hn : (n.+2%:R : R) <= n.+3%:R by rewrite ler_nat leqnSn.
    by rewrite hx1 (le_trans hxn hn) /= lexx.
  - case: ifP=> _; [exact: sqr_ge0 | exact: lexx].
have hconv x : extended_order_limit (fun n => (fn n x)%:E) (g x)%:E.
  case: (boolP (1 <= x))=> hx.
  - have /andP[_ htr] := truncn_itv (normr_ge0 x).
    pose N := (Num.truncn `|x|).+1.
    have hxN : x <= (N%:R : R) := le_trans (ler_norm x) (ltW htr).
    apply: (@eventually_constant_order_limit R _ _ N)=> n hn.
    have hNn : (N%:R : R) <= n.+2%:R.
      rewrite ler_nat; exact: leq_trans hn (leq_trans (leqnSn n) (leqnSn n.+1)).
    by rewrite /fn /g hx (le_trans hxN hNn).
  - apply: (@eventually_constant_order_limit R _ _ 0%N)=> n _.
    by rewrite /fn /g (negPf hx).
have hi n : is_measure_integral (@lebesgue_scalar_measure R) (real_total_integrand (fn n)) (an n).
  have hb : (1 : R) < n.+2%:R by rewrite ltr1n.
  have hseg := @inverse_square_lebesgue_segment R n.+2%:R hb.
  apply: ((@real_subset_integral_total R R _ `[1,n.+2%:R] (fun x => (x^-1)^+2) (fn n) (an n) _ _).1 hseg).
  - move=> x hx; move: hx; rewrite /= in_itv /= => hx.
    by rewrite /fn hx.
  - move=> x hx; have hn : ~ ((1 <= x) && (x <= n.+2%:R)).
      by move=> hh; apply: hx; rewrite /= in_itv.
    by rewrite /fn (negPf (introT negP hn)).
have hrec : extended_order_limit (fun n : nat => ((n.+2%:R : R)^-1)%:E) 0%E.
  apply: reciprocal_natural_error_limit=> n.
  rewrite ger0_norm; last by rewrite invr_ge0 ler0n.
  have h1 : (0 : R) < n.+1%:R by rewrite ltr0n.
  have h2 : (0 : R) < n.+2%:R by rewrite ltr0n.
  by rewrite (@lef_pV2 R _ _ h2 h1) ler_nat leqnSn.
have halim : extended_order_limit an 1%:E.
  have hh := @real_affine_order_limit R (fun n => (n.+2%:R : R)^-1) 0 (-1) 1 hrec.
  have he : (fun n => (1+ -1*(n.+2%:R : R)^-1)%:E)=an.
    by apply: funext=> n; rewrite /an mulN1r.
  by rewrite he mulr0 addr0 in hh.
have hg := @real_nonnegative_increasing_integral_limit R R _ (lebesgue_scalar_is_measure R)
  fn g an 1%:E hp hmon hconv hi halim.
apply: ((@real_subset_integral_total R R _ [set x : R | 1 <= x] (fun x => (x^-1)^+2) g 1%:E _ _).2 hg).
- by move=> x hx; rewrite /g hx.
- move=> x hx; have hn : ~~ (1 <= x) by apply/negP.
  by rewrite /g (negPf hn).
Qed.
