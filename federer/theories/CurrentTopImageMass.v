(** Federer (1969), 4.1.25, p. 383: on the
    source-top exterior power, mass scales by the
    top Jacobian. Reuse 1.7.6, p. 34, and the
    simple-vector equality of 1.8.1, p. 38. The
    degree-zero endpoint uses the existing absolute-scalar
    mass and J_0=1; no assertion of literal simplicity
    of arbitrary zero-vectors is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps
  ExteriorGrading ExteriorPowers ExteriorMaps ExteriorNorm
  ExteriorFrameUnitNorm ExteriorNormNaturality TopExteriorNorm
  SimpleElementary SimpleVectors MassEquality
  CurrentCoefficientNorms CurrentPositiveCoefficientNorms
  CurrentZeroDegreeExteriorLaws EuclideanLinearJacobian
  EuclideanTopExteriorVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_top_image_mass]: the norm
    identity for each normalized summand in Federer
    4.1.25, p. 383. Every source-top vector, including
    zero, has image mass J_m(D) times its mass.
    A singular differential is allowed. *)
Theorem current_top_image_mass (R : realType) (h2 : (1+1 : R) != 0)
    m n (D : Hom (R_n R m) (R_n R n))
    (xi : exterior_power (R_n R m) m) :
  @current_vector_mass R h2 n m (exterior_power_map (hom_as_linear D) m xi) =
    euclidean_linear_jacobian m D * @current_vector_mass R h2 m m xi.
Proof.
rewrite (bool_irrelevance h2 (euclidean_two_nonzero R)).
case: m D xi => [|k] D xi.
- rewrite -{1}(exterior_zeroth_inverseK xi) exterior_power_map_zeroth_scalar
    current_vector_mass_zeroth_scalar current_vector_mass_zeroth_value
    euclidean_linear_jacobian_zero_degree mul1r.
  reflexivity.
- pose X := R_n R k.+1.
  pose Y := R_n R n.
  pose hx := @euclidean_inner_productP R k.+1.
  pose hy := @euclidean_inner_productP R n.
  pose two := euclidean_two_nonzero R.
  pose e := @coordinate_basis R k.+1.
  have hWord : e_lambda e (ord_tuple k.+1) != 0.
    by rewrite -(exterior_norm_eq0 two hx)
      (@euclidean_top_product_unit_norm R two k.+1) oner_eq0.
  have [c hXi] := @nonzero_top_vector_spans R two X k.+1 e
    (@coordinate_basisP R k.+1) (e_lambda e (ord_tuple k.+1)) hWord xi.
  have hSimple : simple xi.
    rewrite hXi; apply: simple_scale; first exact: ltn0Sn.
    exact: product_simple.
  have hImageSimple := exterior_power_map_simple (hom_as_linear D) hSimple.
  have hSource := @simple_mass_euclidean R two X (@euclidean_inner_product R k.+1)
    hx k.+1 e (@coordinate_basisP R k.+1) k.+1 (ltn0Sn k)
    (@current_form_comass R two k.+1 k.+1)
    (@current_positive_comass_laws R two k.+1 k.+1 (ltn0Sn k))
    xi (@current_vector_mass R two k.+1 k.+1 xi) hSimple
    (@current_positive_mass_laws R two k.+1 k.+1 (ltn0Sn k) xi).
  have hImage := @simple_mass_euclidean R two Y (@euclidean_inner_product R n)
    hy n (@coordinate_basis R n) (@coordinate_basisP R n) k.+1 (ltn0Sn k)
    (@current_form_comass R two n k.+1)
    (@current_positive_comass_laws R two n k.+1 (ltn0Sn k))
    (exterior_power_map (hom_as_linear D) k.+1 xi)
    (@current_vector_mass R two n k.+1 (exterior_power_map (hom_as_linear D) k.+1 xi))
    hImageSimple (@current_positive_mass_laws R two n k.+1 (ltn0Sn k) _).
  rewrite hSource hImage.
  exact: euclidean_top_exterior_volume_scale.
Qed.

(** Source for [current_top_image_singular_zero]: at
    a zero top Jacobian the original exterior image
    vanishes, supporting the weighted-area calculation in
    Federer 4.1.25, p. 383. This follows from the
    preceding mass identity and the already proved
    definiteness of the actual coefficient mass. *)
Theorem current_top_image_singular_zero (R : realType)
    (h2 : (1+1 : R) != 0) m n
    (D : Hom (R_n R m) (R_n R n))
    (xi : exterior_power (R_n R m) m) :
  euclidean_linear_jacobian m D = 0 ->
  exterior_power_map (hom_as_linear D) m xi = 0.
Proof.
move=> hZero.
apply: (@current_vector_mass_real_norm R h2 n m).2.
by rewrite (@current_top_image_mass R h2 m n D xi) hZero mul0r.
Qed.
