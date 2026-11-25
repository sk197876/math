(** Federer (1969), 4.1.7, p. 356: the
    actual directional product identity on smooth
    forms, before its original transpose to currents. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  AlternatingProduct ScalarCoefficients CurrentCoefficientNorms CurrentCoefficientCompleteness
  CurrentSpaces CurrentDirectionalDerivative SmoothCurrentFormProduct SmoothFunctionSpaceLaws
  SmoothBilinearMultiplierUP SmoothBilinearMultiplierDifferential NormBoundedBilinearUP NormFiniteBilinearBound
  SmoothDirectionalDerivativeUP SmoothDirectionalDerivativeSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section SmoothCurrentFormDirectionalProduct.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Local Notation Y := (fun m=>A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (fun m=>@current_form_comass R h2 n m).
Local Notation hNY := (fun m=>@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation E := (fun m=>@current_smooth_space R h2 n U hU m).
Local Notation ev := (fun m=>@current_smooth_value R h2 n U hU m).
Local Notation hE := (fun m=>@current_smooth_space_laws R h2 n U hU m).
Local Notation D := (fun m=>@current_smooth_derivatives R h2 n U hU m).
Local Notation hD := (fun m=>@current_smooth_derivative_laws R h2 n U hU m).
Local Notation Fin := (fun m=>@current_form_finite_basis R h2 n m).
Local Notation B := (@form_wedge R h2 X R^o (fun a b=>a*b) (@scalar_bilinear R) k p).
Local Notation hB := (@form_wedge_bilinear R h2 X R^o (fun a b=>a*b) (@scalar_bilinear R) k p).


Variable v:X.
Local Notation L := (fun m=>@current_smooth_directional_derivative R h2 n m U hU v).
Local Notation hL := (fun m=>@SmoothDirectionalDerivative.laws R X (Y m) NX (NY m) hNX (hNY m)
  U (E m) (ev m) (hE m) (D m) (hD m) v).

(** Source for [smooth_current_form_product_directional]:
    the original form coefficient product rule used
    in Federer 4.1.7, p. 356. All three
    derivatives are the actual smooth derivatives. *)
Theorem smooth_current_form_product_directional phi psi:
  L (k+p) (@smooth_current_form_product R h2 n k p U hU phi psi)=
    @smooth_current_form_product R h2 n k p U hU (L k phi) psi+
      @smooth_current_form_product R h2 n k p U hU phi (L p psi).
Proof.
have [n1 [b1 hb1]]:=Fin k;have [n2 [b2 hb2]]:=Fin p.
have hBound:norm_bounded_bilinear (NY k) (NY p) (NY (k+p)) B:=
  @norm_finite_bilinear_bounded R (Y k) (Y p) (Y (k+p)) (NY k) (NY p) (NY (k+p))
    (hNY k) (hNY p) (hNY (k+p)) n1 n2 b1 b2 hb1 hb2 B hB.
apply:(smooth_function_extensional (hE (k+p)))=>x hx.
rewrite (smooth_function_add_value (hE (k+p)))
  (@smooth_current_form_product_values R h2 n k p U hU (L k phi) psi x hx)
  (@smooth_current_form_product_values R h2 n k p U hU phi (L p psi) x hx).
exact (@smooth_bilinear_multiplier_directional_values R X (Y k) (Y p) (Y (k+p))
  NX (NY k) (NY p) (NY (k+p)) hNX (hNY k) (hNY p) (hNY (k+p)) U
  (E k) (E p) (E (k+p)) (ev k) (ev p) (ev (k+p))
  (D k) (D p) (D (k+p)) (hD k) (hD p) (hD (k+p)) v
  (L k) (L p) (L (k+p)) (hL k) (hL p) (hL (k+p)) B hBound phi
  (@smooth_current_form_product R h2 n k p U hU phi)
  (@smooth_current_form_product_values R h2 n k p U hU phi) psi x hx).
Qed.
End SmoothCurrentFormDirectionalProduct.
