(** Federer (1969), 2.5.7, p. 98: a bounded linear functional is a Daniell
    integral for finite p. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialFunctionLimitUP PartialNormPower
  PartialAbsolutePartsGraph PartialExtendedOrderLoci RealPower MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureLpPowerIntegral MeasureLpDominatedZero MeasureExponentDomain
  TotalScalarLpUP TotalScalarLpLattice TotalScalarLpFiniteSeminorm IncreasingScalarErrors
  MonotoneDaniellIntegralUP ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_lp_increasing_error_norm_limit]: complete supporting
    norm convergence g-f_n -> 0 in Federer 2.5.7, p. 98 No finite measure of
    X is assumed. *)
Theorem finite_lp_increasing_error_norm_limit (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : nat -> X -> R) (g : X -> R) :
  (1 <= p)%R -> (forall n, total_scalar_lp mu p%:E (f n)) -> total_scalar_lp mu p%:E g ->
  real_functions_increase_to f g ->
  extended_order_limit (fun n => total_scalar_lp_norm mu p%:E (fun x => (g x-f n x)%R)) 0.
Proof.
move=> hp hf hg hl.
pose d n x := (g x-f n x)%R.
pose D n := total_scalar_function (d n).
have hd n : total_scalar_lp mu p%:E (d n).
  exact: (@total_scalar_lp_subtract R X mu hm p%:E g (f n) hg (hf n)).
pose a := finite_total_scalar_lp_norm mu p%:E (d 0%N).
have ha : total_scalar_lp_norm mu p%:E (d 0%N)=a%:E.
  exact: esym (@finite_total_scalar_lp_norm_exact R X mu hm p%:E (d 0%N) (hd 0%N)).
pose H := partial_norm_power (fun y : R => `|y|%R) p (D 0%N).
have hi : is_measure_integral mu H (real_power a p)%:E.
  exact: (@measure_power_integral_from_finite_lp_norm R X R^o (fun y : R => `|y|%R)
    (scalar_absolute_value_norm R) mu hm p a (D 0%N) hp (hd 0%N).2.1 ha).
have hsum : is_measure_summable mu H by exists (real_power a p).
have hdom n : measure_almost_everywhere mu (partial_extended_le_locus
    (partial_extended_function_absolute_value (partial_norm_power (fun y : R => `|y|%R) p (D n))) H).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (real_power `|d n x| p)%:E,(real_power `|d 0%N x| p)%:E.
  split.
  - exists (real_power `|d n x| p)%:E; split.
    + exists (d n x); by split.
    + by rewrite abse_EFin (ger0_norm (real_power_nonnegative _ _)).
  - split; first by exists (d 0%N x); split.
    rewrite lee_fin.
    have [hn0 hnb] := andP (@increasing_scalar_error_bounds R X f g hl n x).
    have h00 := (andP (@increasing_scalar_error_bounds R X f g hl 0%N x)).1.
    apply: (@real_power_monotone R _ _ p (normr_ge0 _) _ (lt_le_trans ltr01 hp)).
    by rewrite /d (ger0_norm hn0) (ger0_norm h00).
have hlim : measure_almost_everywhere mu (partial_function_limit_locus D
    (partial_function_total (fun _ : X => (0%R : real_norm_metric_space (scalar_absolute_value_norm R))))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (fun n => (d n x : real_norm_metric_space (scalar_absolute_value_norm R))),0%R.
  split; first by move=> n.
  split; first by [].
  exact: (@increasing_scalar_error_limit R X f g hl x).
have [_ hc] := @lp_power_dominated_zero_limit R X R^o (fun y : R => `|y|%R)
  (scalar_absolute_value_norm R) mu hm p D H hp (fun n => (hd n).2.1) hsum hdom hlim.
exact: hc.
Qed.
