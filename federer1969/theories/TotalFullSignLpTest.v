(** Federer (1969), 2.5.7, p. 99: choose r with the same positive support as
    g by 2.4.16, pp. 89–90. This supporting existence step reuses the proved
    full-sign unit tests and transfers them to total functions without
    changing their values. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialFunctionExtensionSealed
  MeasureUP CountablyMeasurableUP MeasureDualTestUP FullSignUnitTest ScalarSignTest ScalarSignTestIntegral
  TotalScalarLpUP TotalSignMatchingExtension TotalScalarTestTransfer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_full_sign_lp_test_exists]: the full- support test used
    in Federer 2.5.7, p. 99, from 2.4.16, pp. 89–90 The unit-ball convention
    is erratum p. 2, book p. 89 line 19. Any admissible test exponent is
    allowed at this existence stage. *)
Theorem total_full_sign_lp_test_exists (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) q (g : X -> R) :
  1 <= q ->
  is_countably_measure_measurable_function mu
    (0%R : real_norm_metric_space (scalar_absolute_value_norm R)) (total_scalar_function g) ->
  exists r : X -> R, total_scalar_lp mu q r /\ total_scalar_lp_norm mu q r <= 1 /\
    forall x, Num.sg (r x)=Num.sg (g x).
Proof.
case: q=> [q| |] hq hg; last by [].
- have hqr : (1 <= q)%R by move: hq; rewrite lee_fin.
  have [r [hr hs]] := @full_sign_unit_test_exists R X mu hm q g hqr hg.
  have he := @sign_matching_total_extension_graph R X g _ hs.
  have [hmem hunit] := @finite_unit_test_total_transfer R X mu hm q _ _ hr he.
  exists (PartialFunctionExtension.value (partial_function_total r) 0%R); split=> //; split=> //.
  exact: (@sign_matching_extension_pointwise R X g _ hs).
- have ht := @scalar_sign_linfinity_test R X mu hm (total_scalar_function g) hg.
  have hs := @scalar_sign_test_sign_matching R X (total_scalar_function g).
  have he := @sign_matching_total_extension_graph R X g _ hs.
  have [hmem hunit] := @infinity_unit_test_total_transfer R X mu hm _ _ ht he.
  exists (PartialFunctionExtension.value (partial_scalar_sign (total_scalar_function g)) 0%R); split=> //; split=> //.
  exact: (@sign_matching_extension_pointwise R X g _ hs).
Qed.
