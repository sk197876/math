(** Federer (1969), 4.1.7, pp. 355–356:
    multiplication of actual compact test forms by
    a fixed original smooth form. The topology is
    the literal final topology of 4.1.1, p. 344. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  AlternatingProduct ScalarCoefficients CurrentCoefficientNorms CurrentSpaces SmoothFunctionSpaceUP
  SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  OpenFamilyTopologyUP SmoothCurrentFormProduct SupportedSmoothOperatorTests.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentTestFormProduct.
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
Variable phi:E k.
Local Notation P := (@smooth_current_form_product R h2 n k p U hU phi).
Local Notation hSupport := (@smooth_current_form_product_preserves_support R h2 n k p U hU phi).

(** Source for [current_test_form_product]: the actual
    test operator psi to phi wedge psi, used to
    define the contraction of Federer 4.1.7,
    pp. 355–356. *)
Definition current_test_form_product:
    Hom (@current_test_space R h2 n U hU p) (@current_test_space R h2 n U hU (k+p)):=
  @supported_smooth_test_operator R X (Y p) (Y (k+p)) NX (NY p) (NY (k+p))
    hNX (hNY p) (hNY (k+p)) U (E p) (E (k+p)) (ev p) (ev (k+p))
    (hE p) (hE (k+p)) P hSupport.

(** Source for [current_test_form_product_inclusion]:
    the test product has precisely the original
    smooth representative, supporting Federer
    4.1.7, pp. 355–356. *)
Lemma current_test_form_product_inclusion psi:
  smooth_test_inclusion (hE (k+p)) (current_test_form_product psi)=
    P (smooth_test_inclusion (hE p) psi).
Proof. exact:supported_smooth_test_evaluation. Qed.

(** Source for [current_test_form_product_values]:
    the original alternating product at every point,
    supporting Federer 4.1.7, pp. 355–356. *)
Lemma current_test_form_product_values psi x:U x->
  @current_test_value R h2 n U hU (k+p) (current_test_form_product psi) x=
    form_wedge h2 (@scalar_bilinear R) (ev k phi x)
      (@current_test_value R h2 n U hU p psi x).
Proof.
move=>hx.
change (ev (k+p) (smooth_test_inclusion (hE (k+p)) (current_test_form_product psi)) x=
  form_wedge h2 (@scalar_bilinear R) (ev k phi x)
    (ev p (smooth_test_inclusion (hE p) psi) x)).
rewrite current_test_form_product_inclusion.
exact:smooth_current_form_product_values.
Qed.

(** Source for [current_test_form_product_continuous]:
    the actual product is continuous on Federer's
    original test spaces, supporting 4.1.7,
    pp. 355–356. *)
Theorem current_test_form_product_continuous:
  open_family_continuous (@current_test_opens R h2 n U hU p)
    (@current_test_opens R h2 n U hU (k+p)) current_test_form_product.
Proof.
exact:(@supported_smooth_test_continuous R X (Y p) (Y (k+p)) NX (NY p) (NY (k+p))
  hNX (hNY p) (hNY (k+p)) U (E p) (E (k+p)) (ev p) (ev (k+p))
  (hE p) (hE (k+p)) (D p) (D (k+p)) (hD p) (hD (k+p)) P hSupport
  (@smooth_current_form_product_continuous R h2 n k p U hU phi)).
Qed.
End CurrentTestFormProduct.
