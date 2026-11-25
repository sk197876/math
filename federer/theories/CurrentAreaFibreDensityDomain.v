(** Federer (1969), 4.1.25, p. 383: the
    actual opaque target density retains the original
    full-fibre domain and is defined Hausdorff almost
    everywhere. Measurability and summability require
    additional proofs and are not part of its definition. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric ExteriorGrading CurrentCoefficientNorms
  EuclideanLebesgueDimensions LipschitzUP HausdorffMeasure
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  CurrentAreaNormalisedImageSealed CurrentAreaFibreSumUP
  CurrentAreaFibreAlmostExistence CurrentAreaFibreDensitySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section FibreDensityDomain.
Variable R : realType.
Hypothesis h2 : ((1+1 : R) != 0)%R.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R n)).
Variable f : X -> Y.
Variable xi : R_n R m -> exterior_power (R_n R m) m.
Local Notation u := (@CurrentAreaNormalisedImage.value R m n f xi).
Local Notation eta := (@CurrentAreaFibreDensity.value R h2 X n m f u).
Local Notation H := (@hausdorff_measure R Y m).

(** Source for [current_area_fibre_density_input_domain]:
    every point of a defined full fibre belongs to
    the original normalized-summand domain, as required
    by Federer 4.1.25, p. 383. *)
Lemma current_area_fibre_density_input_domain y :
  partial_function_domain eta y ->
  forall x, f x = y -> partial_function_domain u x.
Proof.
move=> [v hValue].
exact: current_area_fibre_sum_input_domain
  ((@CurrentAreaFibreDensity.laws R h2 X n m f u y v).1 hValue).
Qed.

(** Source for [current_area_fibre_density_conull_domain]:
    the full-fibre target density is defined for
    Hausdorff almost every y, as in Federer 4.1.25,
    p. 383. No finite measure of the whole source
    or injectivity of the original map is imposed. *)
Theorem current_area_fibre_density_conull_domain :
  is_metric_lipschitz setT f ->
  (exists a : R, is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun x =>
      ((@current_vector_mass R h2 m m (xi x))%:E : extended_real_line R))) a%:E) ->
  measure_almost_everywhere H (partial_function_domain eta).
Proof.
move=> hLip hSummable.
apply: (measure_almost_everywhere_mono (@hausdorff_measure_is_measure R Y m) _
  (@current_area_fibre_almost_exists R h2 m n f xi hLip hSummable)).
move=> y [v hSum]; exists v.
exact: (@CurrentAreaFibreDensity.laws R h2 X n m f u y v).2 hSum.
Qed.
End FibreDensityDomain.
