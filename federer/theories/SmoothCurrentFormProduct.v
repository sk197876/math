(** Federer (1969), 4.1.7, pp. 355–356: the
    original smooth alternating product on comass-
    normed form spaces. This is the actual pointwise
    product of 4.1.6, p. 351. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  AlternatingProduct ScalarCoefficients CurrentCoefficientNorms CurrentCoefficientCompleteness
  CurrentSpaces SmoothBilinearMultiplierUP SmoothBilinearMultiplierSealed
  SmoothBilinearMultiplierContinuity SmoothBilinearMultiplierSupport OpenFamilyTopologyUP
  SmoothFunctionTopology SmoothFunctionSupport SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothCurrentFormProduct.
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

(** Source for [smooth_current_form_product]: fixed
    multiplication by an original smooth k-form,
    supporting Federer 4.1.7, pp. 355–356. *)
Definition smooth_current_form_product (phi:E k):Hom (E p) (E (k+p)):=
  @SmoothBilinearMultiplier.operator R X (Y k) (Y p) (Y (k+p)) NX (NY k) (NY p) (NY (k+p))
    hNX (hNY k) (hNY p) (hNY (k+p)) U (E k) (E p) (E (k+p)) (ev k) (ev p) (ev (k+p))
    (hE k) (hE p) (hE (k+p)) (Fin k) (Fin p) B hB phi.

(** Source for [smooth_current_form_product_values]:
    the actual original pointwise alternating product,
    supporting Federer 4.1.7, pp. 355–356. *)
Lemma smooth_current_form_product_values phi psi x:U x->
  ev (k+p) (smooth_current_form_product phi psi) x=B (ev k phi x) (ev p psi x).
Proof. exact:SmoothBilinearMultiplier.laws. Qed.

(** Source for [smooth_current_form_product_continuous]:
    fixed multiplication is continuous in the
    original E topologies, supporting Federer 4.1.7,
    pp. 355–356. *)
Theorem smooth_current_form_product_continuous phi:
  open_family_continuous (smooth_function_opens (hD p))
    (smooth_function_opens (hD (k+p))) (smooth_current_form_product phi).
Proof.
exact (@smooth_bilinear_multiplier_continuous R X (Y k) (Y p) (Y (k+p)) NX (NY k) (NY p) (NY (k+p))
  hNX (hNY k) (hNY p) (hNY (k+p)) U (E k) (E p) (E (k+p)) (ev k) (ev p) (ev (k+p))
  (hE k) (hE p) (hE (k+p)) (Fin k) (Fin p) B hB phi hU (D p) (D (k+p))
  (hD p) (hD (k+p)) _ (@SmoothBilinearMultiplier.laws R X (Y k) (Y p) (Y (k+p)) NX (NY k) (NY p) (NY (k+p))
    hNX (hNY k) (hNY p) (hNY (k+p)) U (E k) (E p) (E (k+p)) (ev k) (ev p) (ev (k+p))
    (hE k) (hE p) (hE (k+p)) (Fin k) (Fin p) B hB phi)).
Qed.

(** Source for [smooth_current_form_product_preserves_support]:
    the product preserves the original compact test
    support, supporting Federer 4.1.7, pp. 355–356. *)
Theorem smooth_current_form_product_preserves_support phi (K:smooth_compact_set hNX U) psi:
  @smooth_function_support R X (Y p) NX hNX U (E p) (ev p) psi `<=` smooth_compact_carrier K ->
  @smooth_function_support R X (Y (k+p)) NX hNX U (E (k+p)) (ev (k+p))
    (smooth_current_form_product phi psi) `<=` smooth_compact_carrier K.
Proof.
exact (@smooth_bilinear_multiplier_preserves_support R X (Y k) (Y p) (Y (k+p)) NX (NY (k+p))
  hNX (hNY (k+p)) U (E k) (E p) (E (k+p)) (ev k) (ev p) (ev (k+p)) (hE (k+p))
  B hB phi _ (@SmoothBilinearMultiplier.laws R X (Y k) (Y p) (Y (k+p)) NX (NY k) (NY p) (NY (k+p))
    hNX (hNY k) (hNY p) (hNY (k+p)) U (E k) (E p) (E (k+p)) (ev k) (ev p) (ev (k+p))
    (hE k) (hE p) (hE (k+p)) (Fin k) (Fin p) B hB phi) K psi).
Qed.
End SmoothCurrentFormProduct.
