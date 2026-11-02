(** Federer (1969), 3.2.16, p. 254:
    the new definition generalizes 3.1.2.
    The erratum p. 5 corrects "coincides with"
    to "generalizes"; the older actual base
    value is retained in the implication proved here. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm RealNormUP HilbertFormCompactness EuclideanLebesgueDimensions
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  ApproximateDifferentialUP MeasureApproximateDifferentialUP
  EuclideanMeasureAffineCriterion MeasureApproximateAffineReverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [euclidean_approximate_differential_generalizes]:
    the comparison with 3.1.2, Federer
    3.2.16, p. 254 line 2; erratum p. 5.
    No boundedness assumption on D is added:
    finite-dimensional boundedness is proved in the
    preceding affine-criterion theorem. *)
Theorem euclidean_approximate_differential_generalizes (R : realType) n
    (Y : lmodType R) (NY : Y -> R) (hNY : is_real_norm NY)
    (A : set (R_n R n)) (f : R_n R n -> Y) a (D : Hom (R_n R n) Y) :
  has_approximate_differential NY A f a D ->
  has_measure_approximate_differential NY
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (@euclidean_lebesgue_measure R n) n
    (partial_function_source_restrict A (partial_function_total f)) a D.
Proof.
move=> hD.
apply: (@measure_affine_criterion_approximate_differential R (R_n R n) Y
  (inner_norm (@euclidean_inner_productP R n)) NY
  (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY
  (@euclidean_lebesgue_measure R n) n
  (partial_function_source_restrict A (partial_function_total f)) a (f a) D
  (euclidean_lebesgue_is_measure R n)).
exact: (@euclidean_approximate_differential_affine_criterion R n Y NY hNY A f a D hD).
Qed.
