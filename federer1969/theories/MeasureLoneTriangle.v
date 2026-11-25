(** Federer (1969), 2.4.12, p. 87: the seminorm assertion is immediate at
    p=1 from the integral laws. This supporting proof makes the p=1 step
    explicit, using the norm triangle inequality and integral monotonicity. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic PartialNormPower RealPower
  ExtendedRealPartial PartialExtendedArithmetic PartialExtendedOrderLoci DominatedErrorGraphs
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableNormedFunctionUP
  MeasureLpNorm MeasureLpPowerIntegral MeasureLpMembershipUP MeasureLpSumMembership
  MeasureIntegralUP MeasureIntegralAddition MeasureIntegralComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lone_triangle]: direct p=1 part of
    the seminorm assertion in Federer 2.4.12, p. 87.
    All three norms are finite by L1 membership and addition closure;
    the pointwise norm inequality then integrates without approximation. *)
Theorem measure_lone_triangle (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_norm_metric_space hN)) :
  is_measure_lp_function mu 1%R f -> is_measure_lp_function mu 1%R g ->
  measure_lp_norm mu N 1%R (partial_vector_add f g) <= measure_lp_norm mu N 1%R f + measure_lp_norm mu N 1%R g.
Proof.
move=> hf hg.
have hs := @measure_lp_function_add R X V N hN mu hm 1%R f g hf hg.
have hint (u : partial_function X (real_norm_metric_space hN)) (hu : is_measure_lp_function mu 1%R u) :
    is_measure_integral mu (partial_norm_power N 1%R u) (measure_lp_norm mu N 1%R u).
  have hn := @measure_lp_norm_nonnegative R X V N hN mu 1%R u hm hu.1 hu.2.1.1.
  have hfin : measure_lp_norm mu N 1%R u \is a fin_num by rewrite (ge0_fin_numE hn); exact hu.2.2.1.
  have ha : measure_lp_norm mu N 1%R u = (fine (measure_lp_norm mu N 1%R u))%:E by rewrite fineK.
  have hi := @measure_power_integral_from_finite_lp_norm R X V N hN mu hm 1%R _ u hu.1 hu.2.1.1 ha.
  have ha0 : (0 <= fine (measure_lp_norm mu N 1%R u))%R by move: hn; rewrite ha lee_fin.
  by rewrite real_power_one_exponent // fineK in hi.
have hfi := hint f hf; have hgi := hint g hg; have hsi := hint _ hs.
have hnF := @measure_lp_norm_nonnegative R X V N hN mu 1%R f hm hf.1 hf.2.1.1.
have hnG := @measure_lp_norm_nonnegative R X V N hN mu 1%R g hm hg.1 hg.2.1.1.
have hadd : extended_add (measure_lp_norm mu N 1%R f) (measure_lp_norm mu N 1%R g) =
    Some (measure_lp_norm mu N 1%R f + measure_lp_norm mu N 1%R g).
  by rewrite /extended_add ge0_adde_def.
have hi := @measure_integral_add R X mu hm _ _ _ _ _ hfi hgi hadd.
apply: (@measure_integral_monotone R X mu hm _ _ _ _ hsi hi).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _
    (measurable_function_domain hf.2.1.1) (measurable_function_domain hg.2.1.1))).
move=> x [[u hu] [v hv]].
exists (N (u+v)%R)%:E,(N u+N v)%:E; split.
- exists (u+v)%R; split.
  + apply/partial_vector_add_graph; exists u,v; by split=> //; split.
  + by rewrite real_power_one_exponent //; exact: real_seminorm_nonnegative hN.1 _.
- split.
  + apply: partial_finite_sum_graph.
    * exists u; split=> //; by rewrite real_power_one_exponent //; exact: real_seminorm_nonnegative hN.1 _.
    * exists v; split=> //; by rewrite real_power_one_exponent //; exact: real_seminorm_nonnegative hN.1 _.
  + rewrite lee_fin; exact: real_seminorm_triangle hN.1 u v.
Qed.
