(** Federer (1969), proof of 2.4.4(2), p. 83: u is a lower function and t*u
    an upper function when f is nonnegative and finite almost everywhere.
    Source context: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP PartialExtendedOrderLoci
  MeasureIntegralUP MeasureIntegralBounds MeasureStepFunctionUP MeasureStepScalarOperation MeasureStepScaling
  MeasureStepNonnegative GeometricQuantisationUP GeometricQuantisationLaws MeasureGeometricApproximant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [geometric_approximant_lower_upper]: both
    approximant comparisons in the proof of Federer 2.4.4(2),
    p. 83, on the common conull finite nonnegative region. *)
Lemma geometric_approximant_lower_upper (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (t : R) (q : R -> R)
    (f : partial_function X (extended_real_line R)) :
  (1 < t)%R -> is_geometric_quantisation t q -> is_measure_measurable_function mu f ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  measure_almost_everywhere mu (partial_extended_below_infinity_locus f) ->
  is_measure_lower_function mu f (partial_geometric_approximant q f) /\
  is_measure_upper_function mu f (partial_real_function_scale t (partial_geometric_approximant q f)).
Proof.
move=> ht hq hf hp hfin.
pose u := partial_geometric_approximant q f.
have hu := @geometric_approximant_step R X mu hm t q f ht hq hf.
have [a ha] := step_function_sum_defined hu.
have [htu hta] := @measure_step_function_scale R X mu hm u t a hu ha.
have hgood := @measure_almost_everywhere_and R X mu hm _ _ hp hfin.
have hpoint x : (partial_extended_nonnegative_locus f `&` partial_extended_below_infinity_locus f) x ->
    partial_step_lower_locus u f x /\ partial_step_upper_locus (partial_real_function_scale t u) f x.
  move=> [[z [hz hz0]] [w [hw hwf]]]; have he := partial_function_single_valued hz hw.
  have hzf : z < +oo by rewrite he.
  have hzn : z \is a fin_num by rewrite (ge0_fin_numE hz0).
  have hzR : (0 <= fine z)%R by move: hz0; rewrite -(fineK hzn) lee_fin.
  have [_ [hlo hup]] := @geometric_quantisation_bounds R t q ht hq (fine z) hzR.
  split.
  - exists (q (fine z)),z; split; first by exists z; split.
    split=> //; by rewrite -(fineK hzn) lee_fin.
  - exists (t*q (fine z))%R,z; split.
    + exists (q (fine z)); split=> //; exists z; by split.
    + split=> //; by rewrite -(fineK hzn) lee_fin.
split; split=> //.
- apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hgood)=> x hx; exact: (hpoint x hx).1.
- apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hgood)=> x hx; exact: (hpoint x hx).2.
Qed.

(** Source for [measure_geometric_integral_bound]: the displayed
    multiplicative bound in Federer 2.4.4(2), p. 83:
    the upper integral is at most t times the lower integral. *)
Lemma measure_geometric_integral_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (t : R) (q : R -> R)
    (f : partial_function X (extended_real_line R)) :
  (1 < t)%R -> is_geometric_quantisation t q -> is_measure_measurable_function mu f ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  measure_almost_everywhere mu (partial_extended_below_infinity_locus f) ->
  measure_upper_integral mu f <= t%:E * measure_lower_integral mu f.
Proof.
move=> ht hq hf hp hfin.
have [hlo hup] := @geometric_approximant_lower_upper R X mu hm t q f ht hq hf hp hfin.
have [a ha] := step_function_sum_defined hlo.1.
have [_ hta] := @measure_step_function_scale R X mu hm _ t a hlo.1 ha.
have hl := @measure_lower_integral_bound R X mu f _ a hlo ha.
have hu := @measure_upper_integral_bound R X mu f _ (t%:E*a) hup hta.
apply: le_trans hu _; rewrite lee_pmul2l // lte_fin; exact: lt_trans ltr01 ht.
Qed.
