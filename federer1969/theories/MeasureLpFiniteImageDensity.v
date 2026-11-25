(** Federer (1969), 2.4.12, p. 87: finite-image density for all finite p>=1.
    Federer's erratum p. 2, book p. 87 line 18, restricts the infinity case
    separately to finite-dimensional targets. The result below is the
    complete finite-p part, with no finite-dimensionality or finite-measure
    hypothesis. The approximation proof itself does not require completeness
    of the target. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureStepFunctionUP MeasurableNormedBasic MeasureLpMembershipUP MeasureLpConvergence MeasureLpAlmostEquality
  MeasureLpTotalFiniteApproximation ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_finite_image_dense]: direct finite-p part of the
    density assertion in Federer 2.4.12, p. 87 For every positive error
    there is an Lp function with finite image at smaller Lp distance. The
    input may have any conull partial domain. *)
Theorem measure_lp_finite_image_dense (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : partial_function X (real_norm_metric_space hN)) (epsilon : R) :
  is_measure_lp_function mu p f -> (0 < epsilon)%R ->
  exists g : partial_function X (real_norm_metric_space hN),
    is_measure_lp_function mu p g /\ finite_set (partial_function_range g) /\
    measure_lp_distance mu N p f g < epsilon%:E.
Proof.
move=> hf he.
have [F [hext [hagree hF]]] := @measurable_normed_total_representative R X V N hN mu hm f hf.2.1.
have hFlp := @measure_lp_function_almost_equal R X V N hN mu hm p f _ hf hagree.
have [g [hglp [hfinite hlim]]] := @measure_lp_total_finite_image_approximation R X V N hN mu hm p F hFlp.
have heE : (0 : \bar R) < epsilon%:E by rewrite lte_fin.
have [K hK] := hlim.2 epsilon%:E heE.
exists (partial_function_total (g K)); split; first exact: hglp K.
split.
- have hr : partial_function_range (partial_function_total (g K)) = g K @` setT.
    apply/seteqP; split=> y; first by move=> [x hx]; exists x.
    by move=> [x _ hx]; exists x.
  rewrite hr; exact: hfinite K.
- rewrite (@measure_lp_distance_almost_left R X V N hN mu hm p f _ _ hf.1 hf.2.1 hF (hglp K).2.1 hagree).
  exact: hK K (leqnn K).
Qed.
