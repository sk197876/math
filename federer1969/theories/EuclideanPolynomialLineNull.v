(** Federer (1969), 2.6.5, p. 120, base case of the induction proving
    nonzero polynomial zero sets null. The actual one-coordinate Euclidean
    measure is identified with the sealed scalar L^1 from 2.5.17, p. 111. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanCoordinateSplit EuclideanOneCoordinate EuclideanLebesgue LebesgueScalarMeasure
  MeasurePushforward PolynomialFunctions PolynomialRepresentations PolynomialCoefficientUniqueness PolynomialFiniteRoots
  PolynomialSliceNullCoefficients EuclideanPolynomialSlices.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_join_zero_dimension]: the
    zero-dimensional remainder in the scalar base case of
    Federer 2.6.5, p. 120; the sole coordinate is t. *)
Lemma euclidean_join_zero_dimension (R : realType) (t : R) :
  @euclidean_join R 0 (0,t) = euclidean_one_embed t.
Proof.
apply/ffunP=> i; rewrite (ord1 i) euclidean_join_head.
by rewrite /euclidean_one_embed ffunE.
Qed.

(** Source for [euclidean_polynomial_line_null]: the base
    case of Federer 2.6.5, p. 120, for the existing
    Chapter 1 polynomial functions. A nonzero scalar
    polynomial has finitely many roots, and each is L^1-null. *)
Theorem euclidean_polynomial_line_null (R : realType)
    (P : PolynomialFunction (R_n R 1) R^o) :
  (exists x, P x <> 0) ->
  @positive_euclidean_lebesgue_measure R 0 [set x | P x = 0] = 0%:E.
Proof.
move=> hP.
have [i [hi [u hu]]] := euclidean_polynomial_nonzero_coefficient hP.
have hu0 : u = 0 := coordinate_zero u.
rewrite hu0 in hu.
have hn : ~~ all (pred1 0) (euclidean_polynomial_coefficients P (0 : R_n R 0)).
  apply/negP=> /allP ha; apply: hu; apply/eqP; apply: ha.
  apply/mapP; exists i=> //; by rewrite mem_iota add0n leq0n hi.
have he : (@euclidean_one_embed R) @^-1` [set x | P x = 0] =
    [set t | coefficient_polynomial_value (euclidean_polynomial_coefficients P (0 : R_n R 0)) t = 0].
  apply: funext=> t.
  change ((P (euclidean_one_embed t) = 0) =
    (coefficient_polynomial_value (euclidean_polynomial_coefficients P (0 : R_n R 0)) t = 0)).
  by rewrite euclidean_polynomial_slice_value euclidean_join_zero_dimension.
rewrite positive_euclidean_lebesgue_first /measure_pushforward he.
exact (@coefficient_polynomial_root_set_null R R^o (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) _ (@lebesgue_scalar_singleton R) hn).
Qed.
