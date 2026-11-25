(** Federer (1969), 2.6.5, p. 120, final sentence: a nonzero polynomial on
    Euclidean space has a Lebesgue-null zero set. This follows the printed
    induction using Fubini. Taylor coefficients are the already formalised
    coefficients of 1.10.4, p. 46; no alternate polynomial construction or
    external polynomial-null-set theorem is imported. it has no
    corresponding measure result. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  MeasureUP MeasurePushforward PushforwardMeasurabilityTransfer BorelRegularMeasureUP
  ProductMeasure LebesgueScalarMeasure EuclideanCoordinateSplit EuclideanLebesgue EuclideanLebesgueRegularity
  PolynomialFunctions PolynomialRepresentations PolynomialCoefficientUniqueness PolynomialContinuity
  PolynomialSliceNullCoefficients PolynomialFiberNull EuclideanPolynomialSlices EuclideanPolynomialLineNull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_euclidean_polynomial_null]: direct
    positive-dimensional assertion of Federer 2.6.5, p. 120,
    with the actual polynomial functions and Euclidean spaces
    of Chapter 1. A nonzero value witnesses nonzero P.
    The induction removes the null zero set of one nonzero
    coefficient; all remaining scalar slices have finitely
    many roots. Fubini applies to the actual measurable root set. *)
Theorem positive_euclidean_polynomial_null (R : realType) n :
  forall P : PolynomialFunction (R_n R n.+1) R^o,
    (exists x, P x <> 0) ->
    @positive_euclidean_lebesgue_measure R n [set x | P x = 0] = 0%:E.
Proof.
elim: n=> [|n ih] P hP; first exact: euclidean_polynomial_line_null hP.
have [i [hi hci]] := euclidean_polynomial_nonzero_coefficient hP.
have hpoly := euclidean_polynomial_coefficient_polynomial P i.
pose Q := @PolynomialMap R (R_n R n.+1) R^o (euclidean_polynomial_coefficient P i)
  (introT (asboolP _) hpoly).
have hzero := ih Q hci.
have hc := @polynomial_coefficients_almost_nonzero R (Choice.clone (R_n R n.+1) _) R^o
  (@positive_euclidean_lebesgue_measure R n) (positive_euclidean_lebesgue_is_measure R n)
  (polynomial_degree P).+1 (euclidean_polynomial_coefficient P) i hi hzero.
have [hrn [hcn _]] := positive_euclidean_lebesgue_regularity R n.
have [hrnext _] := positive_euclidean_lebesgue_regularity R n.+1.
have hB := @finite_inner_polynomial_zero_set_borel R (R_n R n.+2)
  (@euclidean_inner_product R n.+2) (@euclidean_inner_productP R n.+2)
  n.+2 (@coordinate_basis R n.+2) (@coordinate_basisP R n.+2) P
  (elimT (asboolP _) (polynomial_function_proof P)).
have hmeas := borel_regular_borel_measurable (positive_euclidean_lebesgue_is_measure R n.+1) hrnext hB.
rewrite positive_euclidean_lebesgue_successor in hmeas.
have hs := @measure_pushforward_preimage_measurable R
  (Choice.clone (inner_metric_space (@euclidean_inner_productP R n.+1) * R)%type _)
  (Choice.clone (inner_metric_space (@euclidean_inner_productP R n.+2)) _)
  (@euclidean_join R n.+1)
  (product_measure (positive_euclidean_lebesgue_is_measure R n) (lebesgue_scalar_is_measure R))
  [set x | P x = 0] (can_inj (@euclidean_joinK R n.+1)) hmeas.
have he : (@euclidean_join R n.+1) @^-1` [set x | P x = 0] =
    [set p | coefficient_polynomial_value (euclidean_polynomial_coefficients P p.1) p.2 = 0].
  apply: funext=> p; case: p=> u t.
  change ((P (euclidean_join (u,t)) = 0) =
    (coefficient_polynomial_value (euclidean_polynomial_coefficients P u) t = 0)).
  by rewrite euclidean_polynomial_slice_value.
rewrite he in hs.
rewrite positive_euclidean_lebesgue_successor /measure_pushforward he.
exact (@polynomial_fiber_null_sigma_finite R
  (Choice.clone (inner_metric_space (@euclidean_inner_productP R n.+1)) _) R^o
  (@positive_euclidean_lebesgue_measure R n) (@lebesgue_scalar_measure R)
  (positive_euclidean_lebesgue_is_measure R n) (lebesgue_scalar_is_measure R)
  (euclidean_polynomial_coefficients P) hcn (lebesgue_scalar_countably_measurable R)
  (@lebesgue_scalar_singleton R) hc hs).
Qed.
