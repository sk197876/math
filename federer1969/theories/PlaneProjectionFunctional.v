(** Federer (1969), 2.5.10, p. 101: the norm-bounded linear functional on
    H^1 summable functions in the Euclidean plane. It is integration against
    the actual projected-counting measure. The inner fibre-sum formula is
    proved separately. Source context and erratum: PlaneProjectionMeasure.v;
    the dominated-integral argument is documented in
    BorelDominatedRealSummability.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MeasureUP BorelRegularMeasureUP
  HausdorffLength PlaneProjectionMeasure TopologicalBorel
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureIntegralAbsolute PartialAbsolutePartsGraph SummableRealFunctionUP SummableRealArithmetic
  TotalScalarLpUP TotalScalarLpClosure TotalScalarLpFiniteSeminorm TotalScalarPairing
  TotalLoneSummability RealIntegralFunctionalUP RealIntegralFunctional
  FunctionLatticeSeminormUP FunctionOperatorSeminorm BorelDominatedRealSummability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section PlaneFunctional.
Variable R : realType.
Local Notation X := [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)].
Local Notation H := (@hausdorff_length R X).
Local Notation psi := (@plane_projection_measure R).
Local Notation L := (total_scalar_lp H 1).

(** Source for [plane_projection_lone_summable]: the
    whole summable domain stated in Federer 2.5.10,
    p. 101, is integrable for the projected-counting
    measure. Countable measurability follows from finite
    L1 norm and is not a global hypothesis on the plane. *)
Lemma plane_projection_lone_summable : L `<=` summable_real_functions psi.
Proof.
move=> f hf.
have hi := @total_scalar_lone_absolute_integral R X H (@hausdorff_length_is_measure R X) f hf.
have hs := @total_lone_summable_real R X H (@hausdorff_length_is_measure R X) f hf.
apply: (proj1 (@borel_dominated_real_absolute_integral R X H psi
  (@hausdorff_length_is_measure R X) (plane_projection_is_measure R)
  (@hausdorff_length_borel_regular R X) f _ _ (@plane_projection_hausdorff_bound R) hs hi)).
move=> B hB; exact (@borel_regular_borel_measurable R X psi
  (plane_projection_is_measure R) (plane_projection_borel_regular R) B hB).
Qed.

(** Source for [plane_projection_functional]: the
    functional mu of Federer 2.5.10, p. 101,
    as a real functional on the full total H^1-L1
    space. Its value is selected by the existing
    sealed integral interface; values off L are unused. *)
Definition plane_projection_functional :=
  @lattice_measure_integral R X psi L plane_projection_lone_summable.

(** Source for [plane_projection_functional_integral]:
    actual integral law defining the functional of
    Federer 2.5.10, p. 101, before identifying
    it with the printed iterated fibre sum. *)
Lemma plane_projection_functional_integral :
  is_real_integral_functional psi L plane_projection_functional.
Proof. exact: lattice_measure_integral_specification. Qed.

(** Source for [plane_projection_functional_linear]:
    linearity of the example functional in Federer
    2.5.10, p. 101, by the integral laws
    2.4.4(3)–(4), p. 82. *)
Lemma plane_projection_functional_linear :
  is_linear_functional_on_functions L plane_projection_functional.
Proof.
split.
- move=> f g hf hg; apply: EFin_inj.
  exact: (measure_integral_unique
    (plane_projection_functional_integral (total_scalar_lp_add (@hausdorff_length_is_measure R X) hf hg))
    (@real_total_integral_add R X psi (plane_projection_is_measure R) f g _ _
      (plane_projection_functional_integral hf) (plane_projection_functional_integral hg))).
- move=> c f hf; apply: EFin_inj.
  exact: (measure_integral_unique
    (plane_projection_functional_integral (total_scalar_lp_scale (@hausdorff_length_is_measure R X) c hf))
    (@real_total_integral_scale R X psi (plane_projection_is_measure R) f _ c
      (plane_projection_functional_integral hf))).
Qed.

(** Source for [plane_projection_functional_bound]: the
    displayed unit L1 bound of Federer 2.5.10,
    p. 101. Absolute value on the functional follows
    also by applying the printed one-sided bound to -f. *)
Lemma plane_projection_functional_bound f : L f ->
  (`|plane_projection_functional f|<=finite_total_scalar_lp_norm H 1 f)%R.
Proof.
move=> hf.
have hi := @total_scalar_lone_absolute_integral R X H (@hausdorff_length_is_measure R X) f hf.
have hs := @total_lone_summable_real R X H (@hausdorff_length_is_measure R X) f hf.
have hB B (hB : borel_set B) := @borel_regular_borel_measurable R X psi
  (plane_projection_is_measure R) (plane_projection_borel_regular R) B hB.
have [_ [b [hbi hba]]] := @borel_dominated_real_absolute_integral R X H psi
  (@hausdorff_length_is_measure R X) (plane_projection_is_measure R)
  (@hausdorff_length_borel_regular R X) f _ hB (@plane_projection_hausdorff_bound R) hs hi.
have [c [hci hcb]] := @measure_integral_absolute_bound R X psi (plane_projection_is_measure R)
  _ _ (plane_projection_functional_integral hf).
have hc' : is_measure_integral psi (real_total_integrand (fun x => `|f x|%R)) c.
  apply: (@measure_integral_graph_equivalent R X psi _ _ _ _ hci)=> x z; split.
  - move=> [y [hy <-]]; apply/real_total_integrand_graph.
    have hyE := (real_total_integrand_graph f x y).1 hy.
    by rewrite -hyE abse_EFin.
  - move/real_total_integrand_graph=> hz; exists (f x)%:E; split.
    + by apply/real_total_integrand_graph.
    + by rewrite abse_EFin.
rewrite (measure_integral_unique hc' hbi) abse_EFin lee_fin in hcb.
exact: le_trans hcb hba.
Qed.
End PlaneFunctional.
