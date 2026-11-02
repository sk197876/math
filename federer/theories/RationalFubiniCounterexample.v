(** Federer (1969), 2.6.3(2), p. 118: the rational kernel has both iterated
    integrals zero but is not L^1 times L^1 integrable. We prove the book's
    arbitrary positive-slope rectangle formula separately, then use m=1
    here: its value 1/4 contradicts the zero value forced by the proved
    iterated integrals. This is the same argument with one sufficient
    rectangle slope. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderLimit RealScalarOrderLimits StieltjesSegmentIdentity
  MeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureSubsetIntegral SummableRealFunctionUP SummableRealArithmetic
  ProductMeasure LebesgueScalarMeasure RealSubsetIntegralGraph RealDominatedIntegralLimit
  RationalFubiniKernel RationalIteratedIntegrals RationalProductIntegralValue RationalRectangleIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rational_fubini_kernel_not_integrable]: the
    non-integrability assertion of Federer 2.6.3(2), p. 118 Assuming
    integrability first gives value zero by Fubini and hence summability.
    Bounded convergence on the printed open rectangles then gives the
    incompatible value 1/4. *)
Theorem rational_fubini_kernel_not_integrable (R : realType) :
  ~ is_measure_integrable
    (product_measure (lebesgue_scalar_is_measure R) (lebesgue_scalar_is_measure R))
    (@rational_fubini_integrand R).
Proof.
move=> [z hi].
have hz := rational_integrable_product_value_zero hi.
rewrite hz in hi.
pose mu := product_measure (lebesgue_scalar_is_measure R) (lebesgue_scalar_is_measure R).
have hm : is_measure mu := product_measure_is_measure (lebesgue_scalar_is_measure R) (lebesgue_scalar_is_measure R).
pose f (p : R*R) := rational_fubini_kernel p.1 p.2.
pose Q (p : R*R) := (0 < p.1) && (0 < p.2).
pose fn (n : nat) (p : R*R) := if Q p && (p.1 < n.+1%:R) && (p.2 < n.+1%:R) then f p else 0.
pose q : R := 1/(1+1)^+2.
have hsum : summable_real_functions mu f by exists 0; exact: hi.
have hH : is_measure_summable mu (real_total_integrand (fun p => `|f p|)) := summable_real_absolute hm hsum.
have hb n p : `|fn n p| <= `|f p|.
  rewrite /fn; case: ifP=> _; first exact: lexx.
  rewrite normr0; exact: normr_ge0.
have hconv p : extended_order_limit (fun n => (fn n p)%:E) (f p)%:E.
  case: (boolP (Q p))=> hp.
  - have /andP[_ hx] := truncn_itv (normr_ge0 p.1).
    have /andP[_ hy] := truncn_itv (normr_ge0 p.2).
    pose N := maxn (Num.truncn `|p.1|).+1 (Num.truncn `|p.2|).+1.
    have h1 : p.1 < (N%:R : R).
      apply: lt_le_trans (le_lt_trans (ler_norm _) hx) _.
      by rewrite /N ler_nat leq_maxl.
    have h2 : p.2 < (N%:R : R).
      apply: lt_le_trans (le_lt_trans (ler_norm _) hy) _.
      by rewrite /N ler_nat leq_maxr.
    apply: (@eventually_constant_order_limit R _ _ N)=> n hn.
    have hn' : (N%:R : R) <= n.+1%:R by rewrite ler_nat; exact: leq_trans hn (leqnSn n).
    by rewrite /fn hp (lt_le_trans h1 hn') (lt_le_trans h2 hn').
  - have hf0 : f p=0 by rewrite /f /rational_fubini_kernel -/(Q p) (negPf hp).
    apply: (@eventually_constant_order_limit R _ _ 0%N)=> n _.
    by rewrite /fn (negPf hp) hf0.
have hfi n : is_measure_integral mu (real_total_integrand (fn n)) q%:E.
  have hn : (0 : R) < n.+1%:R by rewrite ltr0n.
  have hrect := @rational_scaled_rectangle_integral_if_integrable R n.+1%:R 1 hn ltr01
    (ex_intro _ 0%E hi).
  rewrite mul1r in hrect.
  apply: ((@real_subset_integral_total R (Choice.clone (R*R)%type _) mu
    (`]0,n.+1%:R[ `*` `]0,n.+1%:R[) f (fn n) q%:E _ _).1 hrect).
  - move=> p [hx hy]; move: hx hy; rewrite /= !in_itv /= => /andP[hx0 hxn] /andP[hy0 hyn].
    by rewrite /fn /Q hx0 hy0 hxn hyn.
  - move=> p hp; have hh : ~~ (Q p && (p.1 < n.+1%:R) && (p.2 < n.+1%:R)).
      apply/negP=> /andP[/andP[/andP[hx0 hy0] hxn] hyn]; apply: hp; split;
        by rewrite /= in_itv /= ?hx0 ?hy0 ?hxn ?hyn.
    by rewrite /fn (negPf hh).
have hq := @real_dominated_integral_limit R (Choice.clone (R*R)%type _) mu hm
  fn f (fun p => `|f p|) (fun _ => q) q hH hi.1 hb hconv hfi (@real_constant_order_limit R q).
have he := measure_integral_unique hi hq.
have heq : (0 : R)=q := EFin_inj he.
have hqpos : 0 < q.
  rewrite /q divr_gt0 //; exact: exprn_gt0 2 (addr_gt0 ltr01 ltr01).
by move: hqpos; rewrite -heq ltxx.
Qed.
