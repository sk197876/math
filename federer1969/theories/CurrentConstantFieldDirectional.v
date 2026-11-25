(** Federer (1969), 4.1.7, p. 356: all
    directional derivatives of the original constant
    form and multivector fields vanish. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms CurrentCoefficientNorms
  CurrentSpaces CurrentVectorSpaces CurrentConstantFields CurrentDirectionalDerivative
  CurrentVectorDirectionalDerivative SmoothConstantUP SmoothConstantDirectional
  SmoothDirectionalDerivativeUP SmoothDirectionalDerivativeSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentConstantFormDirectional.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y := (A_m X R^o m).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation D := (@current_smooth_derivatives R h2 n U hU m).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU m).
Local Notation L := (@current_constant_form R h2 n U hU m).

(** Source for [current_constant_form_directional_zero]:
    actual original constant form fields have
    D_v equal to zero, supporting Federer 4.1.7,
    p. 356. *)
Theorem current_constant_form_directional_zero v a:
  @current_smooth_directional_derivative R h2 n m U hU v (L a)=0.
Proof.
exact:(@smooth_constant_directional_zero R X Y NX NY hNX hNY U hU E ev hE D hD L
  (@current_constant_form_values R h2 n U hU m) v
  (@current_smooth_directional_derivative R h2 n m U hU v)
  (@SmoothDirectionalDerivative.laws R X Y NX NY hNX hNY U E ev hE D hD v) a).
Qed.
End CurrentConstantFormDirectional.
Section CurrentConstantVectorDirectional.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y := (exterior_power X m).
Local Notation NY := (@current_vector_mass R h2 n m).
Local Notation hNY := (@current_vector_mass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation E := (@current_vector_smooth_space R h2 n U hU m).
Local Notation ev := (@current_vector_smooth_value R h2 n U hU m).
Local Notation hE := (@current_vector_smooth_space_laws R h2 n U hU m).
Local Notation D := (@current_vector_smooth_derivatives R h2 n U hU m).
Local Notation hD := (@current_vector_smooth_derivative_laws R h2 n U hU m).
Local Notation L := (@current_constant_vector R h2 n U hU m).

(** Source for [current_constant_vector_directional_zero]:
    actual original constant vector fields have
    D_v equal to zero, supporting Federer 4.1.7,
    p. 356. *)
Theorem current_constant_vector_directional_zero v a:
  @current_vector_smooth_directional_derivative R h2 n m U hU v (L a)=0.
Proof.
exact:(@smooth_constant_directional_zero R X Y NX NY hNX hNY U hU E ev hE D hD L
  (@current_constant_vector_values R h2 n U hU m) v
  (@current_vector_smooth_directional_derivative R h2 n m U hU v)
  (@SmoothDirectionalDerivative.laws R X Y NX NY hNX hNY U E ev hE D hD v) a).
Qed.
End CurrentConstantVectorDirectional.
