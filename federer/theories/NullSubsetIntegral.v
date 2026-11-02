(** Supporting flat-image boundary case of Federer (1969), 2.9.21, p. 166.
    The integral over a null target is zero by the null-replacement
    convention in 2.4.3(2), p. 81, and subset convention in 2.4.10, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialZeroExtension MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureDensityNullSets
  MeasureSubsetIntegral MeasureIntegralAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [null_target_subset_integral]: supporting null-target
    assertion for Federer 2.9.21, p. 166, from 2.4.3(2),
    p. 81, and 2.4.10, p. 85. The zero extension agrees
    with the total zero function off the null set, even if the
    original integrand is undefined everywhere on that target. *)
Lemma null_target_subset_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : partial_function X (extended_real_line R))
    (A : set X) : is_measure mu -> mu A=0 -> is_measure_subset_integral mu A f 0.
Proof.
move=> hm hA.
have hConull : measure_almost_everywhere mu (~` A).
  by rewrite /measure_almost_everywhere setCK.
apply: (@measure_integral_almost_equal R X mu hm
  (partial_function_total (fun _ => (0 : extended_real_line R))) _ 0
  (measure_extended_zero_integral hm)).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hConull)=> x hx.
exists 0; split; first by [].
by apply/(partial_function_zero_extension_off _ _ _ hx).
Qed.
