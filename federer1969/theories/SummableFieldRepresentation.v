(** Federer (1969), 4.1.19, p. 377: retain
    every original L1 field in the raw
    extension space, including its original conull
    partial domain. The total representative is zero
    on undefined null points, as in 2.3.2,
    p. 73. No compact carrier is required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric ModuleQuotient
  SubspaceCarrier MeasureUP MeasureAlmostUP MeasurableFunctionUP
  MeasurableNormedFunctionUP MeasurableNormedBasic
  PartialFunctionUP PartialFunctionBasic PartialFunctionExtensionUP
  PartialFunctionExtensionSealed PartialZeroExtension MeasurableTotalExtension
  MeasureLpNorm MeasureLpNormAlmostEquality MeasureLpNormTotal
  MeasureLpMembershipUP TotalMeasurableFunctionSpace
  SummableFieldUP SummableFieldSealed SummableFieldLaws
  LinearSubspaceRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Representation.
Variable R : realType.
Variable X : topologicalType.
Variable V : lmodType R.
Variable N : V -> R.
Variable hN : is_real_norm N.
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.
Local Notation M := (real_norm_metric_space hN).
Local Notation F := (GRing.Lmodule.clone R (X -> M) _).
Local Notation A := (@total_measurable_normed_subspace R X V N hN mu hm).
Local Notation W := (@SummableField.space R X V N hN mu hm).
Local Notation value := (@summable_field_value R X V N hN mu hm).
Local Notation size := (@summable_field_size R X V N hN mu hm).

(** Source for [summable_partial_field_representative]:
    the raw L1 extension in Federer 4.1.19,
    p. 377, contains every original partial field
    of 2.4.12, p. 86. The original
    values and L1 norm are preserved; no
    compact support or whole-target separability is added. *)
Theorem summable_partial_field_representative
    (f : partial_function X M)
    (hMeas : is_measurable_normed_function mu f)
    (hFinite : (measure_lp_norm mu N 1 f < +oo)%E) :
  exists w : W,
    is_partial_function_total_extension f (value w) /\
    (forall x, ~ partial_function_domain f x -> value w x = 0%R) /\
    measure_almost_equal mu f (partial_function_total (value w)) /\
    measure_lp_norm mu N 1 f = (size w)%:E.
Proof.
pose f0 := partial_function_zero_extension (0%R : M)
  (partial_function_domain f) f.
pose g := @PartialFunctionExtension.value X M f0 0%R.
pose hG := @PartialFunctionExtension.laws X M f0 0%R.
have hExtend : is_partial_function_total_extension f g.
  move=> x y hxy; apply: (@hG x y).
  apply/partial_function_zero_extension_graph; left; split.
  - by exists y.
  - exact: hxy.
have hUndefined : forall x, ~ partial_function_domain f x -> g x = 0%R.
  move=> x hx; apply: (@hG x 0%R).
  apply/partial_function_zero_extension_graph; right; by split.
have hAlmost := @partial_function_total_extension_almost_equal R X M mu f g
  (measurable_function_domain hMeas.1) hExtend.
have hGMeas := @measurable_normed_almost_equal R X V N hN mu hm f
  (partial_function_total g) hMeas hAlmost.
have hEqual := @measure_lp_norm_almost_equal R X V N hN mu hm 1 f
  (partial_function_total g) (lexx 1) hMeas.1 hGMeas.1 hAlmost.
pose a := @subspace_lift R F A g hGMeas.
have hA : @summable_field_subspace R X V N hN mu hm a.
  change (is_true ((measure_lp_norm mu N 1 (partial_function_total g) < +oo)%E)).
  by rewrite -hEqual.
have [w hW] := @subspace_representation_full R (subspace_space A) W
  (@summable_field_subspace R X V N hN mu hm)
  (@SummableField.inclusion R X V N hN mu hm)
  (@SummableField.laws R X V N hN mu hm) a hA.
have hValue : value w = g.
  by rewrite /summable_field_value hW subspace_liftE.
exists w; split; first by rewrite hValue.
split; first by rewrite hValue.
split; first by rewrite hValue.
rewrite (@summable_field_size_exact R X V N hN mu hm w).
change (measure_lp_norm mu N 1 f =
  measure_lp_norm mu N 1 (partial_function_total (value w))).
rewrite hValue; exact: hEqual.
Qed.

(** Source for [summable_total_field_representative]:
    every total L1 field in the extension
    step of Federer 4.1.19, p. 377,
    has exactly its original values in the
    opaque raw carrier. Its L1 norm is
    the original integral norm, without a quotient. *)
Theorem summable_total_field_representative (f : X -> M) :
  is_measure_lp_function mu 1 (partial_function_total f) ->
  exists w : W, value w = f /\
    measure_lp_norm mu N 1 (partial_function_total f) = (size w)%:E.
Proof.
move=> hF.
have [w [hExtend [_ [_ hSize]]]] :=
  @summable_partial_field_representative (partial_function_total f)
    hF.2.1 hF.2.2.1.
exists w; split; last exact: hSize.
apply: funext=> x; exact: (@hExtend x (f x) erefl).
Qed.
End Representation.
