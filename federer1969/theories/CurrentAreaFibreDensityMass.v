(** Federer (1969), 4.1.25, p. 383: the
    mass of the original vector fibre density is
    bounded by the scalar sum of the source masses.
    The weighted area formula proves this scalar sum
    finite almost everywhere. No target summability or
    finite-total-source-measure premise is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations
  EuclideanInnerProduct InnerMetric ExteriorGrading CurrentCoefficientNorms
  EuclideanLebesgueDimensions LipschitzUP HausdorffMeasure
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionExtensionUP PartialFunctionExtensionSealed
  NonnegativeSum NonnegativeSumSupport FibreNonnegativeSum
  CurrentVectorNumericalSumMass CurrentAreaNormalisedImageSealed
  CurrentAreaNormalisedImageMass CurrentAreaFibreSumUP
  CurrentAreaFibreSumEvaluations CurrentAreaFibreDensitySealed
  CurrentAreaFibreDensityDomain CurrentAreaFibreMassIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section FibreDensityMass.
Variable R : realType.
Hypothesis h2 : ((1+1 : R) != 0)%R.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation V := (exterior_power (R_n R n) m).
Variable f : X -> Y.
Variable xi : R_n R m -> exterior_power (R_n R m) m.
Local Notation r := (fun x => @current_vector_mass R h2 m m (xi x)).
Local Notation M := (@current_vector_mass R h2 n m).
Local Notation H := (@hausdorff_measure R Y m).
Local Notation u := (@CurrentAreaNormalisedImage.value R m n f xi).
Local Notation eta := (@CurrentAreaFibreDensity.value R h2 X n m f u).

(** Source for [current_area_fibre_density_mass_bound]:
    the mass triangle inequality for the literal
    vector fibre sum of Federer 4.1.25, p. 383.
    Every target total representative has the same
    almost-everywhere bound; values outside the original
    partial density domain remain immaterial. *)
Theorem current_area_fibre_density_mass_bound (w : R_n R n -> V) :
  is_metric_lipschitz setT f ->
  (exists a : R, is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun x => ((r x)%:E : extended_real_line R))) a%:E) ->
  is_partial_function_total_extension eta w ->
  measure_almost_everywhere H [set y |
    (M (w y))%:E <= fibre_nonnegative_sum f (fun x => (r x)%:E) y].
Proof.
move=> hLip hMass hW.
have hH := @hausdorff_measure_is_measure R Y m.
have hDomain := @current_area_fibre_density_conull_domain R h2 m n f xi hLip hMass.
have hNonnegative x : (0 <= r x)%R.
  exact: real_seminorm_nonnegative (@current_vector_mass_real_norm R h2 m m).1 _.
have hFinite := @current_area_fibre_mass_almost_finite R m n f r
  hLip hNonnegative hMass.
pose p := @PartialFunctionExtension.value X V u 0%R.
have hP : is_partial_function_total_extension u p :=
  @PartialFunctionExtension.laws X V u 0%R.
apply: (measure_almost_everywhere_mono hH _
  (measure_almost_everywhere_and hH hDomain hFinite)) => y [[v hValue] hSize].
have hSum := (@CurrentAreaFibreDensity.laws R h2 X n m f u y v).1 hValue.
have hOriginalDomain (x : X) : f x = y -> partial_function_domain u x :=
  @current_area_fibre_sum_input_domain R X n m f u y v hSum x.
have hSums := @current_area_fibre_sum_extension_evaluations R X n m f u p y v hP hSum.
have hMassEqual : nonnegative_sum [set x | f x = y]
    (fun x => (M (p x))%:E) = fibre_nonnegative_sum f (fun x => (r x)%:E) y.
  apply: nonnegative_sum_ext => x hx.
  have [z hZ] := hOriginalDomain x hx.
  rewrite (hP x z hZ).
  by rewrite (@current_area_normalised_image_mass R h2 m n f xi x z hZ).
have hSizeP : nonnegative_sum [set x | f x = y] (fun x => (M (p x))%:E) < +oo.
  by rewrite hMassEqual.
have hBound := @current_vector_numerical_sum_mass_bound R h2 X n m
  [set x | f x = y] p v hSizeP hSums.
rewrite hMassEqual in hBound.
have hSizeFinite : fibre_nonnegative_sum f (fun x => (r x)%:E) y \is a fin_num.
  rewrite (ge0_fin_numE (nonnegative_sum_nonnegative _ _)); exact: hSize.
rewrite /= (hW y v hValue) -(fineK hSizeFinite) lee_fin.
exact: hBound.
Qed.
End FibreDensityMass.
