(** Federer (1969), 4.1.19, p. 377: the
    weak divergence pairing is the transpose of the
    original exterior differential. Both coordinate formulas
    were proved in 4.1.6, pp. 353–354. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates
  EuclideanCoordinateForms ExteriorGrading AlternatingForms AlternatingPairing
  PairingLinear AlternatingProduct ScalarTensorContraction MixedAlternatingProduct
  MixedOrdinaryFormProduct ExteriorDifferentialSealed ExteriorDerivativeCoordinates
  OneCovectorInterior CurrentPositiveInteriorPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_exterior_differential_transpose]:
    <theta,d phi>=sum_j <theta contracted DX_j,D_j phi>,
    the coefficient transposition behind the weak and
    smoothing criteria of Federer 4.1.19,
    p. 377. No dimension or degree
    restriction is added to the actual finite sum. *)
Theorem current_exterior_differential_transpose
    (R : realType) (h2 : (1+1:R)!=0) n m
    (L : Hom (R_n R n) (A_m (R_n R n) R^o m))
    (theta : exterior_power (R_n R n) m.+1) :
  pairing theta (@ExteriorDifferential.value R h2 n R^o m L)=
    \sum_(j : 'I_n) pairing
      (positive_one_covector_interior h2 theta (euclidean_coordinate_form j))
      (L (@coordinate_basis R n j)).
Proof.
rewrite exterior_differential_coordinate_formula.
change (pairing_right theta
    (\sum_j mixed_form_product h2 (@scalar_action_bilinear R R^o)
      (euclidean_coordinate_form j) (L (@coordinate_basis R n j)))=
  \sum_(j : 'I_n) pairing
    (positive_one_covector_interior h2 theta (euclidean_coordinate_form j))
    (L (@coordinate_basis R n j))).
rewrite linear_sum; apply: eq_bigr=> j _.
rewrite pairing_rightE mixed_real_form_product.
exact: (esym (@current_positive_interior_pairing R h2 (R_n R n) m theta
  (euclidean_coordinate_form j) (L (@coordinate_basis R n j)))).
Qed.
