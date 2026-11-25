(** Federer (1969), 4.1.7, pp. 355–356:
    a fixed smooth multivector acts by the original
    right interior on actual smooth test forms. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  ExteriorGrading CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces
  CurrentVectorSpaces CurrentVectorFormInterior SmoothFunctionTopology SmoothFunctionSupport
  SmoothCompactSet OpenFamilyTopologyUP SmoothBilinearMultiplierUP SmoothBilinearMultiplierSealed
  SmoothBilinearMultiplierContinuity SmoothBilinearMultiplierSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothCurrentVectorInterior.
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

(** Source for [smooth_current_vector_interior]: the
    original smooth operator psi to xi interior psi,
    supporting Federer 4.1.7, pp. 355–356. *)
Definition smooth_current_vector_interior (xi:V k):Hom (E (k+p)) (E p):=
  @SmoothBilinearMultiplier.operator R X (Z k) (Y (k+p)) (Y p) NX (NZ k) (NY (k+p)) (NY p)
    hNX (hNZ k) (hNY (k+p)) (hNY p) U (V k) (E (k+p)) (E p) (vv k) (ev (k+p)) (ev p)
    (hV k) (hE (k+p)) (hE p) (VFin k) (Fin (k+p)) B hB xi.

(** Source for [smooth_current_vector_interior_values]:
    exact original pointwise interior, supporting
    Federer 4.1.7, pp. 355–356. *)
Lemma smooth_current_vector_interior_values xi psi x:U x->
  ev p (smooth_current_vector_interior xi psi) x=B (vv k xi x) (ev (k+p) psi x).
Proof. exact:SmoothBilinearMultiplier.laws. Qed.

(** Source for [smooth_current_vector_interior_continuous]:
    fixed smooth vector multiplication acts continuously
    on original E spaces, supporting Federer 4.1.7,
    pp. 355–356. *)
Theorem smooth_current_vector_interior_continuous xi:
  open_family_continuous (smooth_function_opens (hD (k+p)))
    (smooth_function_opens (hD p)) (smooth_current_vector_interior xi).
Proof.
exact (@smooth_bilinear_multiplier_continuous R X (Z k) (Y (k+p)) (Y p) NX (NZ k) (NY (k+p)) (NY p)
  hNX (hNZ k) (hNY (k+p)) (hNY p) U (V k) (E (k+p)) (E p) (vv k) (ev (k+p)) (ev p)
  (hV k) (hE (k+p)) (hE p) (VFin k) (Fin (k+p)) B hB xi hU (D (k+p)) (D p)
  (hD (k+p)) (hD p) _ (@SmoothBilinearMultiplier.laws R X (Z k) (Y (k+p)) (Y p) NX (NZ k) (NY (k+p)) (NY p)
    hNX (hNZ k) (hNY (k+p)) (hNY p) U (V k) (E (k+p)) (E p) (vv k) (ev (k+p)) (ev p)
    (hV k) (hE (k+p)) (hE p) (VFin k) (Fin (k+p)) B hB xi)).
Qed.

(** Source for [smooth_current_vector_interior_preserves_support]:
    the original product preserves each compact
    support step, supporting Federer 4.1.7,
    pp. 355–356. *)
Theorem smooth_current_vector_interior_preserves_support xi (K:smooth_compact_set hNX U) psi:
  @smooth_function_support R X (Y (k+p)) NX hNX U (E (k+p)) (ev (k+p)) psi `<=` smooth_compact_carrier K ->
  @smooth_function_support R X (Y p) NX hNX U (E p) (ev p)
    (smooth_current_vector_interior xi psi) `<=` smooth_compact_carrier K.
Proof.
exact (@smooth_bilinear_multiplier_preserves_support R X (Z k) (Y (k+p)) (Y p) NX (NY p)
  hNX (hNY p) U (V k) (E (k+p)) (E p) (vv k) (ev (k+p)) (ev p) (hE p)
  B hB xi _ (@SmoothBilinearMultiplier.laws R X (Z k) (Y (k+p)) (Y p) NX (NZ k) (NY (k+p)) (NY p)
    hNX (hNZ k) (hNY (k+p)) (hNY p) U (V k) (E (k+p)) (E p) (vv k) (ev (k+p)) (ev p)
    (hV k) (hE (k+p)) (hE p) (VFin k) (Fin (k+p)) B hB xi) K psi).
Qed.
End SmoothCurrentVectorInterior.
