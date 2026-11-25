(** Federer (1969), 2.4.12, p. 87, lower-semicontinuity display at
    p=infinity. We use a common conull region for the countably many
    attained bounds and compare scalar lower limits. No measurability beyond
    the stated almost-everywhere convergence is needed for this endpoint
    strengthening. Source context: MeasureEssentialNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionLimitUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureEssentialNorm MeasureEssentialNormAttainment
  MeasureEssentialNormComparison ExtendedLowerLimitUP ExtendedLowerLimit ExtendedConvergentLowerLimit NormSequenceLowerLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_essential_norm_lower_semicontinuous]: complete
    p=infinity case of the lower-limit inequality in Federer 2.4.12, p. 87
    Exact partial domains and infinite essential-norm values are retained. *)
Theorem measure_essential_norm_lower_semicontinuous (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (g : partial_function X (real_norm_metric_space hN)) :
  measure_almost_everywhere mu (partial_function_limit_locus f g) ->
  measure_essential_norm mu N g <= extended_lower_limit (fun n => measure_essential_norm mu N (f n)).
Proof.
move=> hl; pose a n := measure_essential_norm mu N (f n).
have ha : 0 <= extended_lower_limit a.
  apply: (extended_lower_limit_eventual_bound (extended_lower_limit_laws a)).
  exists 0%N=> n _; exact: measure_essential_norm_nonnegative.
apply: (@measure_essential_norm_of_almost_bound R X (real_norm_metric_space hN) mu hm N g _ ha).
have hdom n : measure_almost_everywhere mu (partial_function_domain (f n)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hl).
  move=> x [u [z [hu _]]]; exists (u n); exact: hu.
have hbound n := @measure_essential_norm_almost_bound R X (real_norm_metric_space hN) mu hm N (f n) (hdom n).
have hall := @measure_almost_everywhere_countable R X [the choiceType of (nat : Type)] mu hm setT
  (fun n => [set x | exists y, partial_function_graph (f n) x y /\ (N y)%:E <= a n])
  (countableP setT) (fun n _ => hbound n).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ hl hall)).
move=> x [[u [z [hu [hz hlim]]]] hx]; exists z; split=> //.
have hc := @norm_sequence_extended_order_limit R V N hN u z hlim.
apply: (@extended_lower_limit_pointwise_comparison R (fun n => (N (u n))%:E) a
  (N z)%:E (extended_lower_limit a) (extended_convergent_lower_limit hc) (extended_lower_limit_laws a)).
move=> n; have [y [hy hb]] := hx n I.
have he := partial_function_single_valued (hu n) hy; by rewrite he.
Qed.
