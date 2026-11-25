(** Federer (1969), 4.1.7, p. 356: the
    original coordinate identity for d before
    transposition to the current boundary formula.
    Reuse the exact coordinate formula of 4.1.6,
    p. 353, with actual smooth directional derivatives. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanCoordinateForms
  AlternatingForms Alternating AlternatingProduct ScalarCoefficients MixedOrdinaryFormProduct
  CurrentCoefficientNorms CurrentSpaces CurrentDirectionalDerivative SmoothCurrentExteriorDerivative
  SmoothDirectionalDerivativeUP SmoothDirectionalDerivativeSealed SmoothDirectionalOrdinary
  ExteriorDerivativeUP ExteriorDifferentialUP ExteriorDifferentialSealed ExteriorDerivativeCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SmoothCurrentExteriorCoordinates.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation D := (@current_smooth_derivatives R h2 n U hU m).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU m).
Local Notation dir := (fun j=>@current_smooth_directional_derivative R h2 n m U hU (@coordinate_basis R n j)).
Local Notation dd := (@smooth_current_exterior_derivative R h2 n m U hU).

(** Source for [smooth_current_exterior_coordinate_values]:
    the actual d phi is the sum of DX_j wedge
    D_j phi, supporting the third displayed current
    equation of Federer 4.1.7, p. 356. *)
Theorem smooth_current_exterior_coordinate_values (phi:E) x:U x->
  form_include (@current_smooth_value R h2 n U hU m.+1 (dd phi) x)=
    \sum_j form_include (form_wedge h2 (@scalar_bilinear R)
      (euclidean_coordinate_form j) (ev (dir j phi) x)).
Proof.
move=>hx.
have [L [hL hAlt]]:=@smooth_current_exterior_derivative_actual R h2 n m U hU phi x hx.
have hEqual:=exterior_differential_value_unique (@ExteriorDifferential.laws R h2 n R^o m L) hAlt.
rewrite -hEqual exterior_differential_coordinate_formula linear_sum.
apply:eq_bigr=>j _;rewrite mixed_real_form_product.
have hDir:=@smooth_directional_ordinary_evaluation R X Y NX NY hNX hNY U E ev D hD
  (@coordinate_basis R n j) (dir j)
  (@SmoothDirectionalDerivative.laws R X Y NX NY hNX hNY U E ev hE D hD (@coordinate_basis R n j))
  phi x L hx hL.
by rewrite hDir.
Qed.
End SmoothCurrentExteriorCoordinates.
