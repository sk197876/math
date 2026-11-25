(** Federer (1969), 3.2.17, p. 255:
    extend the differential of the composite
    along the injective differential of psi.
    A linear left inverse exists algebraically;
    finite-dimensional boundedness is proved internally. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness RealNormUP
  LinearRetraction NormDifferentialUP NormFiniteLinearBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [euclidean_injective_bounded_left_inverse]:
    the linear extension chosen in the final
    proof of Federer 3.2.17, p. 255.
    It also supplies the lower-bound hypothesis
    for the tangent-image theorem of 3.1.21. *)
Theorem euclidean_injective_bounded_left_inverse (R : realType) m n
    (L : Hom (R_n R m) (R_n R n)) :
  injective L -> exists P : Hom (R_n R n) (R_n R m),
    norm_bounded_linear (inner_norm (@euclidean_inner_productP R n))
      (inner_norm (@euclidean_inner_productP R m)) P /\ cancel L P.
Proof.
move=> hL.
pose P := hom_of_linear (linear_retraction (i:=hom_as_linear L) hL).
exists P; split.
- exact: (@norm_finite_linear_bounded R (R_n R n) (R_n R m)
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R m)) n
    (@coordinate_basis R n) (@coordinate_basisP R n) P).
- exact: linear_retractionK.
Qed.
