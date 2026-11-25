(** Federer (1969), 4.1.7, p. 356: the
    original directional product identity for smooth
    multivector interiors, before transposition. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  ExteriorGrading CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces
  CurrentVectorSpaces CurrentVectorFormInterior SmoothFunctionTopology SmoothFunctionSupport
  SmoothCompactSet OpenFamilyTopologyUP SmoothBilinearMultiplierUP SmoothBilinearMultiplierSealed
  SmoothBilinearMultiplierContinuity SmoothBilinearMultiplierSupport
  SmoothCurrentVectorInterior CurrentDirectionalDerivative CurrentVectorDirectionalDerivative
  SmoothFunctionSpaceLaws SmoothBilinearMultiplierDifferential NormBoundedBilinearUP NormFiniteBilinearBound
  SmoothDirectionalDerivativeUP SmoothDirectionalDerivativeSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothCurrentVectorDirectionalProduct.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Local Notation Y := (fun m=>A_m X R^o m).
Local Notation Z := (fun m=>exterior_power X m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (fun m=>@current_form_comass R h2 n m).
Local Notation hNY := (fun m=>@current_form_comass_real_norm R h2 n m).
Local Notation NZ := (fun m=>@current_vector_mass R h2 n m).
Local Notation hNZ := (fun m=>@current_vector_mass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation E := (fun m=>@current_smooth_space R h2 n U hU m).
Local Notation ev := (fun m=>@current_smooth_value R h2 n U hU m).
Local Notation hE := (fun m=>@current_smooth_space_laws R h2 n U hU m).
Local Notation D := (fun m=>@current_smooth_derivatives R h2 n U hU m).
Local Notation hD := (fun m=>@current_smooth_derivative_laws R h2 n U hU m).
Local Notation V := (fun m=>@current_vector_smooth_space R h2 n U hU m).
Local Notation vv := (fun m=>@current_vector_smooth_value R h2 n U hU m).
Local Notation hV := (fun m=>@current_vector_smooth_space_laws R h2 n U hU m).
Local Notation Fin := (fun m=>@current_form_finite_basis R h2 n m).
Local Notation VFin := (fun m=>@current_vector_finite_basis R h2 n m).
Local Notation B := (@current_vector_form_interior R X k p).
Local Notation hB := (@current_vector_form_interior_bilinear R X k p).

Variable v:X.
Local Notation L := (fun m=>@current_smooth_directional_derivative R h2 n m U hU v).
Local Notation VL := (fun m=>@current_vector_smooth_directional_derivative R h2 n m U hU v).
Local Notation VD := (fun m=>@current_vector_smooth_derivatives R h2 n U hU m).
Local Notation hVD := (fun m=>@current_vector_smooth_derivative_laws R h2 n U hU m).
Local Notation hL := (fun m=>@SmoothDirectionalDerivative.laws R X (Y m) NX (NY m) hNX (hNY m)
  U (E m) (ev m) (hE m) (D m) (hD m) v).
Local Notation hVL := (fun m=>@current_vector_smooth_directional_derivative_laws R h2 n m U hU v).

(** Source for [smooth_current_vector_interior_directional]:
    D_v(xi interior psi)=(D_v xi) interior psi
    plus xi interior D_v psi, supporting the
    current product rule of Federer 4.1.7,
    p. 356. Every term is the original operation. *)
Theorem smooth_current_vector_interior_directional xi psi:
  L p (@smooth_current_vector_interior R h2 n k p U hU xi psi)=
    @smooth_current_vector_interior R h2 n k p U hU (VL k xi) psi+
      @smooth_current_vector_interior R h2 n k p U hU xi (L (k+p) psi).
Proof.
have [n1 [b1 hb1]]:=VFin k;have [n2 [b2 hb2]]:=Fin (k+p).
have hBound:norm_bounded_bilinear (NZ k) (NY (k+p)) (NY p) B:=
  @norm_finite_bilinear_bounded R (Z k) (Y (k+p)) (Y p) (NZ k) (NY (k+p)) (NY p)
    (hNZ k) (hNY (k+p)) (hNY p) n1 n2 b1 b2 hb1 hb2 B hB.
apply:(smooth_function_extensional (hE p))=>x hx.
rewrite (smooth_function_add_value (hE p))
  (@smooth_current_vector_interior_values R h2 n k p U hU (VL k xi) psi x hx)
  (@smooth_current_vector_interior_values R h2 n k p U hU xi (L (k+p) psi) x hx).
exact (@smooth_bilinear_multiplier_directional_values R X (Z k) (Y (k+p)) (Y p)
  NX (NZ k) (NY (k+p)) (NY p) hNX (hNZ k) (hNY (k+p)) (hNY p) U
  (V k) (E (k+p)) (E p) (vv k) (ev (k+p)) (ev p)
  (VD k) (D (k+p)) (D p) (hVD k) (hD (k+p)) (hD p) v
  (VL k) (L (k+p)) (L p) (hVL k) (hL (k+p)) (hL p) B hBound xi
  (@smooth_current_vector_interior R h2 n k p U hU xi)
  (@smooth_current_vector_interior_values R h2 n k p U hU xi) psi x hx).
Qed.
End SmoothCurrentVectorDirectionalProduct.
