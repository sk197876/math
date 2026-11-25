(** Federer (1969), 2.4.19, p. 91: passage from finite images to the bounded
    case. The reference-point majorant in our approximation permits
    unbounded C at this stage; F remains bounded, as required for the
    printed dominated-convergence argument. Continuity is required only on
    C. Federer's erratum, p. 2, book p. 91, lines 10–11, corrects the L1
    notation and inserts the proof heading. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormMetricScaleContinuity CompleteMetricUP
  RealMetricBackground MetricSubsetBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionPostcomposition MeasureStepFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureLpMembershipUP
  MeasureIntegralUP MeasureIntegralUniqueness MeasureVectorIntegralUP MeasureVectorIntegral
  ConvexFunctionUP MeasureClosedRangeLpApproximation BoundedClosedCompositeConvergence
  FiniteImageJensen JensenLimitTopology RealScalarOrderLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_range_jensen]: the bounded-F approximation stage of
    Federer 2.4.19, p. 91 The proof derives both membership of the mean in C
    and Jensen's inequality from actual finite-image approximations. Unlike
    this stage of the printed argument, C itself need not be bounded. Null
    range exceptions are removed in the later general statement. *)
Theorem bounded_range_jensen (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu : set X -> \bar R) (hm : is_measure mu) (m M : R)
    (C : set (real_norm_metric_space hN)) (c : metric_subset C)
    (F : real_norm_metric_space hN -> real_line_metric R)
    (g : X -> real_norm_metric_space hN) (y : real_norm_metric_space hN) (a : \bar R) :
  mu setT=m%:E -> (0 < m)%R -> closed C -> is_real_convex_function_on C F ->
  continuous (fun z : metric_subset C => F (val z)) ->
  (forall z, C z -> (0 <= F z <= M)%R) -> (forall x, C (g x)) ->
  is_measure_vector_integral mu (partial_function_total g) y ->
  is_measure_integral mu (partial_function_postcompose (partial_function_total g)
    (fun z => ((F z)%:E : extended_real_line R))) a ->
  C ((m^-1)%R *: y)%R /\ (F ((m^-1)%R *: y)%R)%:E <= a * (m^-1)%R%:E.
Proof.
move=> hmass hm0 hC hconv hF hb hgC hy ha.
have hgpre : measure_almost_everywhere mu [set x | C (g x)].
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  by move=> x _; exact: hgC.
have [f [hf [hfin [hfC [hl hlp]]]]] :=
  @measure_closed_range_lp_one_approximation R X V N hN mu hm m C g hmass hm0 hC hy.1 hgpre.
have [b [d [hbi [hdi hbd]]]] := @bounded_closed_composite_integrals_converge R X
  (real_norm_metric_space hN) mu hm m M C c F f g hmass hC hF hb hfC hgC
  (fun n => (hf n).2.1.1) hy.1.2.1.1 hl.
pose v n := @measure_vector_integral R X V N hN hY mu hm (partial_function_total (f n)) (hf n).
have hv n : is_measure_vector_integral mu (partial_function_total (f n)) (v n).
  exact: measure_vector_integral_specification.
have hfr n : finite_set (partial_function_range (partial_function_total (f n))).
  have he : partial_function_range (partial_function_total (f n))=f n @` setT.
    apply/seteqP; split=> z; first by move=> [x hx]; exists x.
    by move=> [x _ hx]; exists x.
  rewrite he; exact: hfin.
have hfc n z : partial_function_range (partial_function_total (f n)) z -> C z.
  move=> [x hx]; rewrite -(hx : f n x=z); exact: hfC.
have hj n := @finite_image_jensen R X V N hN mu hm m C F (partial_function_total (f n))
  (v n) (b n)%:E hmass hm0 hconv (fun z hz => (andP (hb z hz)).1) (hfr n) (hfc n) (hv n) (hbi n).
have hvl := @measure_vector_integral_sequence_continuous R X V N hN mu hm
  (fun n => partial_function_total (f n)) (partial_function_total g) v y hv hy hlp.
pose w n : real_norm_metric_space hN := ((m^-1)%R *: v n)%R.
pose z : real_norm_metric_space hN := ((m^-1)%R *: y)%R.
have hw : w @ \oo --> z.
  move=> U hU; exact: (hvl _ (@real_norm_metric_scale_continuous R V N hN (m^-1)%R y U hU)).
have hwC : \oo (fun n => C (w n)).
  exists 0%N; first exact Logic.I.
  move=> n _; exact: (hj n).1.
have PF0 : ProperFilter (\oo : set_system nat) by typeclasses eauto.
have hzC : C z := @closed_cvg nat [the topologicalType of real_norm_metric_space hN]
  \oo PF0 w C hC hwC z hw.
have hFw := @relative_continuous_sequence_limit R (real_norm_metric_space hN) (real_line_metric R)
  C F w z hF (fun n => (hj n).1) hzC hw.
have hleft := real_metric_extended_order_limit hFw.
have hright := @real_scalar_order_limit R b d (m^-1)%R hbd.
have hineq n : (F (w n))%:E <= ((m^-1)%R * b n)%R%:E.
  rewrite mulrC EFinM; exact: (hj n).2.
have hbound := extended_order_limits_comparison hleft hright hineq.
split=> //; rewrite (measure_integral_unique ha hdi) -EFinM mulrC.
exact hbound.
Qed.
