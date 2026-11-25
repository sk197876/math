(** Federer (1969), 4.1.25, p. 383: the
    norm in the final signed direction formula is
    the Euclidean exterior norm. Reuse its equality
    with mass on simple positive-degree vectors from
    1.8.1, p. 38. In degree zero both norms
    are the absolute scalar, with no simplicity premise. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP GrassmannAbbreviations EuclideanInnerProduct
  EuclideanLinearMaps ExteriorGrading ExteriorPowers ExteriorNorm ExteriorFrameUnitNorm TopExteriorNorm
  SimpleVectors SimpleElementary MassEquality CurrentCoefficientNorms CurrentPositiveCoefficientNorms
  CurrentZeroDegreeExteriorLaws ZeroDegreeCovectorNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_simple_vector_euclidean_norm]:
    the norm identification used in the last formula
    of Federer 4.1.25, p. 383. The conditional
    simplicity hypothesis retains arbitrary scalar
    coefficients in degree zero. *)
Theorem current_simple_vector_euclidean_norm (R : realType)
    (h2 : (1+1 : R) != 0) n m
    (v : exterior_power (R_n R n) m) :
  ((0 < m)%N -> simple v) ->
  @current_vector_mass R h2 n m v =
    exterior_norm h2 (@euclidean_inner_productP R n) v.
Proof.
case: m v => [|k] v hSimple.
- rewrite -{1}(exterior_zeroth_inverseK v) current_vector_mass_zeroth_scalar.
  rewrite -{2}(exterior_zeroth_inverseK v).
  exact: esym (zeroth_exterior_scalar_norm h2 (@euclidean_inner_productP R n) _).
- exact: (@simple_mass_euclidean R h2 (R_n R n) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n)
    k.+1 (ltn0Sn k) (@current_form_comass R h2 n k.+1)
    (@current_positive_comass_laws R h2 n k.+1 (ltn0Sn k))
    v (@current_vector_mass R h2 n k.+1 v) (hSimple (ltn0Sn k))
    (@current_positive_mass_laws R h2 n k.+1 (ltn0Sn k) v)).
Qed.

(** Source for [current_top_vector_euclidean_norm]:
    the source norm in the final formula of
    Federer 4.1.25, p. 383. Every source-top
    vector has equal mass and Euclidean norm,
    including zero and the zero-dimensional source. *)
Theorem current_top_vector_euclidean_norm (R : realType)
    (h2 : (1+1 : R) != 0) m
    (xi : exterior_power (R_n R m) m) :
  @current_vector_mass R h2 m m xi =
    exterior_norm h2 (@euclidean_inner_productP R m) xi.
Proof.
apply: current_simple_vector_euclidean_norm => hPositive.
pose e := @coordinate_basis R m.
pose omega := e_lambda e (ord_tuple m).
have hOmega : omega != 0.
  by rewrite -(exterior_norm_eq0 h2 (@euclidean_inner_productP R m))
    (@euclidean_top_product_unit_norm R h2 m) oner_eq0.
have [c ->] := @nonzero_top_vector_spans R h2 (R_n R m) m e
  (@coordinate_basisP R m) omega hOmega xi.
exact: simple_scale hPositive (product_simple e).
Qed.
