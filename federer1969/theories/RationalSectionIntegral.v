(** Federer (1969), 2.6.3(2), pp. 117–118: each positive-coordinate section
    is absolutely integrable and has integral zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderLimit StieltjesSegmentIdentity
  PartialFunctionBasic MeasurableFunctionUP MeasureIntegralUP MeasureSubsetIntegral SummableRealFunctionUP
  MeasureStepIntegralIdentification LebesgueScalarMeasure RealSubsetIntegralGraph
  RealDominatedIntegralLimit RationalFubiniKernel RationalLebesgueIntegrals
  RationalSectionMeasurability RationalSectionDominator ReciprocalSequenceLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rational_positive_section_integral]: the first improper
    integral equals zero in Federer 2.6.3(2), p. 118 Every finite
    restriction is evaluated from its primitive, the section is bounded by a
    proved summable majorant, and bounded convergence identifies its actual
    integral. *)
Theorem rational_positive_section_integral (R : realType) (y : R) :
  0 < y -> is_measure_integral (@lebesgue_scalar_measure R)
    (real_total_integrand (fun x => rational_fubini_kernel x y)) 0%E.
Proof.
move=> hy.
pose f (x : R) := rational_fubini_kernel x y.
pose fn (n : nat) (x : R) := if (0 <= x) && (x <= n.+1%:R) then f x else 0.
pose an (n : nat) := rational_first_primitive y n.+1%:R.
have [H [hHi [hH0 hbound]]] := rational_positive_section_dominator hy.
have hHs : is_measure_summable (@lebesgue_scalar_measure R) (real_total_integrand H).
  by eexists; exact: hHi.
have hf : is_measure_measurable_function (@lebesgue_scalar_measure R) (real_total_integrand f).
  apply: (@measurable_partial_real_embedding R R _ (lebesgue_scalar_is_measure R)).
  exact: rational_positive_section_measurable hy.
have hb n x : `|fn n x| <= H x.
  rewrite /fn; case: ifP=> hx; first exact: hbound.
  rewrite normr0; exact: hH0.
have hconv x : extended_order_limit (fun n => (fn n x)%:E) (f x)%:E.
  case: (boolP (0 <= x))=> hx.
  - have /andP[_ htr] := truncn_itv (normr_ge0 x).
    pose N := (Num.truncn `|x|).+1.
    have hxN : x <= (N%:R : R) := le_trans (ler_norm x) (ltW htr).
    apply: (@eventually_constant_order_limit R _ _ N)=> n hn.
    have hNn : (N%:R : R) <= n.+1%:R by rewrite ler_nat; exact: leq_trans hn (leqnSn n).
    by rewrite /fn hx (le_trans hxN hNn).
  - have hx0 : x <= 0 by apply: ltW; by rewrite ltNge hx.
    have hz : f x=0 := @rational_fubini_kernel_nonpositive_left R x y hx0.
    apply: (@eventually_constant_order_limit R _ _ 0%N)=> n _.
    by rewrite /fn (negPf hx) hz.
have hi n : is_measure_integral (@lebesgue_scalar_measure R) (real_total_integrand (fn n)) (an n)%:E.
  have hn : (0 : R) < n.+1%:R by rewrite ltr0n.
  have hseg := @rational_first_lebesgue_integral R y n.+1%:R hy hn.
  apply: ((@real_subset_integral_total R R _ `[0,n.+1%:R] f (fn n) (an n)%:E _ _).1 hseg).
  - move=> x hx; move: hx; rewrite /= in_itv /= => hx.
    by rewrite /fn hx.
  - move=> x hx; have hoff : ~~ ((0 <= x) && (x <= n.+1%:R)).
      apply/negP=> hh; apply: hx; by rewrite /= in_itv.
    by rewrite /fn (negPf hoff).
exact (@real_dominated_integral_limit R R _ (lebesgue_scalar_is_measure R)
  fn f H an 0 hHs hf hb hconv hi (@rational_first_primitive_order_limit R y hy)).
Qed.
