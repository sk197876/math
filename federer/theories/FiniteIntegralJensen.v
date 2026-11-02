(** Federer (1969), 2.4.19, p. 91: the final passage from bounded sublevels
    to C, when the scalar integral is finite. The cofinal sublevel cutoff
    uses a fixed reference value outside each level, as documented in
    JensenSublevelApproximation.v; dominated convergence removes its
    contribution while preserving the original normalisation. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormMetricScaleContinuity CompleteMetricUP RealMetricBackground
  MetricSubsetBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition
  MeasureUP MeasureIntegralUP MeasureVectorIntegralUP MeasureVectorIntegral ConvexFunctionUP
  ConvexClosedSublevels JensenSublevelApproximation SublevelCompositeConvergence BoundedRangeJensen
  JensenLimitTopology RealScalarOrderLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_integral_jensen]: the unbounded-C and unbounded-F
    case of Federer 2.4.19, p. 91, under finite scalar integral The separate
    infinite-integral case requires no domination of F(g). *)
Theorem finite_integral_jensen (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu : set X -> \bar R) (hm : is_measure mu) (m b : R)
    (C : set (real_norm_metric_space hN)) (c : metric_subset C)
    (F : real_norm_metric_space hN -> real_line_metric R)
    (g : X -> real_norm_metric_space hN) (y : real_norm_metric_space hN) :
  mu setT=m%:E -> (0 < m)%R -> closed C -> is_real_convex_function_on C F ->
  continuous (fun z : metric_subset C => F (val z)) ->
  (forall z, C z -> (0 <= F z)%R) -> (forall x, C (g x)) ->
  is_measure_vector_integral mu (partial_function_total g) y ->
  is_measure_integral mu (partial_function_postcompose (partial_function_total g)
    (fun z => ((F z)%:E : extended_real_line R))) b%:E ->
  C ((m^-1)%R *: y)%R /\ (F ((m^-1)%R *: y)%R <= b * m^-1)%R.
Proof.
move=> hmass hm0 hC hconv hF hpos hgC hy hbi.
have [t [f [hcD [hfD [hf [hl [hlp hb]]]]]]] := @jensen_sublevel_approximation R X V N hN
  mu hm m C (val c) F g hmass hC hconv hF (set_valP c) hpos hgC hy.1.
have [a [hai hal]] := @sublevel_composite_integrals_converge R X (real_norm_metric_space hN)
  mu hm m (F (val c)) b C c F f g hmass hC hF hpos (fun n x => (hfD n x).1) hgC
  (fun n => (hf n).2.1.1) hbi hb hl.
pose D n : set (real_norm_metric_space hN) := jensen_closed_sublevel N C F (t n).
pose v n := @measure_vector_integral R X V N hN hY mu hm (partial_function_total (f n)) (hf n).
have hv n : is_measure_vector_integral mu (partial_function_total (f n)) (v n).
  exact: measure_vector_integral_specification.
have hj n : C ((m^-1)%R *: v n)%R /\ (F ((m^-1)%R *: v n)%R)%:E <= (a n)%:E * (m^-1)%R%:E.
  have hD := @jensen_sublevel_closed_convex R V N hN C F (t n) hC hconv hF.
  pose cn : metric_subset (D n) := @exist (real_norm_metric_space hN) (fun z => z \in D n)
    (val c) (mem_set (hcD n)).
  have hDF : is_real_convex_function_on (D n) F.
    split; first exact hD.2.
    move=> x z hx hz u hu hu1; exact: (hconv.2 x z hx.1 hz.1 u hu hu1).
  have hcts := @relative_continuity_restrict R (real_norm_metric_space hN) (real_line_metric R)
    C (D n) F (fun z hz => hz.1) hF.
  have hbounds z : D n z -> (0 <= F z <= t n)%R.
    move=> hz; apply/andP; split; [exact: hpos z hz.1|exact hz.2.2].
  have hh := @bounded_range_jensen R X V N hN hY mu hm m (t n) (D n) cn F (f n) (v n) (a n)%:E
    hmass hm0 hD.1 hDF hcts hbounds (hfD n) (hv n) (hai n).
  exact (conj hh.1.1 hh.2).
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
have hright := @real_scalar_order_limit R a b (m^-1)%R hal.
have hineq n : (F (w n))%:E <= ((m^-1)%R * a n)%R%:E.
  rewrite mulrC EFinM; exact: (hj n).2.
have hbound := extended_order_limits_comparison hleft hright hineq.
split=> //; by move: hbound; rewrite lee_fin mulrC.
Qed.
