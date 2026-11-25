(** Federer (1969), 4.1.25, p. 383: the
    original full-fibre vector sum exists for Hausdorff
    almost every target point. The weighted area formula
    proves absolute convergence; the original 3.2.3
    reduction removes the image of every undefined
    normalized summand. No countability of all fibres
    or finiteness of the whole source is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations
  EuclideanInnerProduct InnerMetric ExteriorGrading CurrentCoefficientNorms
  EuclideanLebesgueDimensions LipschitzUP HausdorffMeasure
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionExtensionUP PartialFunctionExtensionSealed
  NonnegativeSum NonnegativeSumSupport FibreNonnegativeSum
  CurrentAreaNormalisedImageSealed
  CurrentAreaNormalisedImageMass CurrentAreaGoodFibres
  CurrentAreaFibreSumUP CurrentAreaFibreSumExistence
  CurrentAreaFibreMassIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section AlmostFibreExistence.
Variable R : realType.
Hypothesis h2 : ((1+1 : R) != 0)%R.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation V := (exterior_power (R_n R n) m).
Variable f : X -> Y.
Variable xi : R_n R m -> exterior_power (R_n R m) m.
Local Notation u := (@CurrentAreaNormalisedImage.value R m n f xi).
Local Notation H := (@hausdorff_measure R Y m).
Local Notation r := (fun x => @current_vector_mass R h2 m m (xi x)).

(** Source for [current_area_fibre_almost_exists]:
    almost-everywhere existence of the literal vector
    sum displayed in Federer 4.1.25, p. 383.
    The proof uses an auxiliary source extension only
    on fibres already proved to lie in the original
    partial domain; it assigns no original summand at
    an undefined differential. *)
Theorem current_area_fibre_almost_exists :
  is_metric_lipschitz setT f ->
  (exists a : R, is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun x => ((r x)%:E : extended_real_line R))) a%:E) ->
  measure_almost_everywhere H [set y | exists eta : V,
    @is_current_area_fibre_sum R X n m f u y eta].
Proof.
move=> hLip hSummable.
have hH := @hausdorff_measure_is_measure R Y m.
have hGood := @current_area_good_fibres R m n f xi hLip.
have hNonnegative x : (0 <= r x)%R.
  exact: real_seminorm_nonnegative (@current_vector_mass_real_norm R h2 m m).1 _.
have hFinite := @current_area_fibre_mass_almost_finite R m n f r
  hLip hNonnegative hSummable.
pose w := @PartialFunctionExtension.value X V u 0%R.
have hW : is_partial_function_total_extension u w :=
  @PartialFunctionExtension.laws X V u 0%R.
apply: (measure_almost_everywhere_mono hH _
  (measure_almost_everywhere_and hH hGood hFinite)) => y [hDomain hSize].
have hSizeEqual : nonnegative_sum [set x | f x = y]
    (fun x => (@current_vector_mass R h2 n m (w x))%:E) =
    fibre_nonnegative_sum f (fun x => (r x)%:E) y.
  apply: nonnegative_sum_ext => x hx.
  have [v hValue] := hDomain x hx.
  rewrite (hW x v hValue).
  by rewrite (@current_area_normalised_image_mass R h2 m n f xi x v hValue).
apply: (@current_area_fibre_sum_exists R h2 X n m f u w y hW hDomain).
by rewrite hSizeEqual.
Qed.
End AlmostFibreExistence.
