(** Federer (1969), 2.6.5, pp. 119–120: Euclidean Lebesgue measures in every
    positive dimension, with an explicit zero-dimensional extension by unit
    mass at the sole vector. The latter is an empty-product convention
    extending the printed definition, not an additional claim attributed to
    Federer. Source context: EuclideanLebesgueUP.v. Positive-dimensional
    results use only the sealed family. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  MeasureUP MeasureBasic BorelRegularMeasureUP CountablyMeasurableUP PointMassMeasure PointMassRegularity
  EuclideanLebesgue EuclideanLebesgueRegularity PolynomialFunctions EuclideanPolynomialNull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_lebesgue_measure]: the Euclidean
    measure L^n of Federer 2.6.5, pp. 119–120.
    For n=0 we explicitly take unit mass at the sole vector,
    so that the empty Cartesian product has measure one. *)
Definition euclidean_lebesgue_measure (R : realType) n :
    set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R :=
  match n as k return set (inner_metric_space (@euclidean_inner_productP R k)) -> \bar R with
  | 0 => point_mass R 0
  | k.+1 => @positive_euclidean_lebesgue_measure R k
  end.
Arguments euclidean_lebesgue_measure {R} n A.

(** Source for [euclidean_lebesgue_is_measure]: finite
    Euclidean product measure assertion of Federer 2.6.5,
    pp. 119–120, including the explicit empty-product convention. *)
Lemma euclidean_lebesgue_is_measure (R : realType) n : is_measure (@euclidean_lebesgue_measure R n).
Proof. case: n=> [|n]; [exact: point_mass_is_measure | exact: positive_euclidean_lebesgue_is_measure]. Qed.

(** Source for [euclidean_lebesgue_borel_regular]: direct
    Borel regularity assertion of Federer 2.6.5, p. 120,
    with the same harmless zero-dimensional extension. *)
Theorem euclidean_lebesgue_borel_regular (R : realType) n :
  is_borel_regular_measure (@euclidean_lebesgue_measure R n).
Proof.
case: n=> [|n]; last exact: (positive_euclidean_lebesgue_regularity R n).1.
apply: point_mass_borel_regular.
have he : [set (0 : inner_metric_space (@euclidean_inner_productP R 0))] = setT.
  apply/seteqP; split=> x _; first exact Logic.I; exact: coordinate_zero.
rewrite he; exact: closedT.
Qed.

(** Source for [euclidean_lebesgue_countably_measurable]: the countability
    hypotheses justifying Fubini and arbitrary product associations in
    Federer 2.6.5, pp. 119–120 They are proved, not assumed. *)
Lemma euclidean_lebesgue_countably_measurable (R : realType) n :
  measure_countably_measurable (@euclidean_lebesgue_measure R n) setT.
Proof.
case: n=> [|n]; first exact: point_mass_countably_measurable.
exact: (positive_euclidean_lebesgue_regularity R n).2.1.
Qed.

(** Source for [euclidean_polynomial_zero_set_null]: direct
    final assertion of Federer 2.6.5, p. 120, for all
    nonzero polynomial functions on R^n. The proof uses
    induction and Fubini as printed. At n=0 a nonzero
    polynomial has no zeros, so the extension also holds. *)
Theorem euclidean_polynomial_zero_set_null (R : realType) n
    (P : PolynomialFunction (R_n R n) R^o) :
  (exists x, P x <> 0) -> euclidean_lebesgue_measure n [set x | P x = 0] = 0%:E.
Proof.
case: n P=> [P [x hx]|n P hP]; last exact: positive_euclidean_polynomial_null hP.
have he : [set y | P y = 0] = set0.
  apply/seteqP; split=> y; last by [].
  move=> hy; apply: hx.
  have hxy : x = y by rewrite (coordinate_zero x) (coordinate_zero y).
  by rewrite hxy.
rewrite he; exact: measure_empty (euclidean_lebesgue_is_measure R 0).
Qed.
