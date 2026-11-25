(** Federer (1969), 4.1.7, pp. 355–356: actual
    smooth multivectors act on original compact test
    forms by right interior multiplication. The test
    topology is Federer's literal final topology. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  AlternatingProduct ScalarCoefficients CurrentCoefficientNorms CurrentSpaces SmoothFunctionSpaceUP
  SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  OpenFamilyTopologyUP CurrentVectorSpaces CurrentVectorFormInterior SmoothCurrentVectorInterior SupportedSmoothOperatorTests.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentTestVectorInterior.
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
Local Notation V := (fun m=>@current_vector_smooth_space R h2 n U hU m).
Variable xi:V k.
Local Notation P := (@smooth_current_vector_interior R h2 n k p U hU xi).
Local Notation hSupport := (@smooth_current_vector_interior_preserves_support R h2 n k p U hU xi).

(** Source for [current_test_vector_interior]: the
    original test operator psi to xi interior psi,
    supporting Federer 4.1.7, pp. 355–356. *)
Definition current_test_vector_interior:
    Hom (@current_test_space R h2 n U hU (k+p)) (@current_test_space R h2 n U hU p):=
  @supported_smooth_test_operator R X (Y (k+p)) (Y p) NX (NY (k+p)) (NY p)
    hNX (hNY (k+p)) (hNY p) U (E (k+p)) (E p) (ev (k+p)) (ev p)
    (hE (k+p)) (hE p) P hSupport.

(** Source for [current_test_vector_interior_inclusion]:
    exact original smooth representative, supporting
    Federer 4.1.7, pp. 355–356. *)
Lemma current_test_vector_interior_inclusion psi:
  smooth_test_inclusion (hE p) (current_test_vector_interior psi)=
    P (smooth_test_inclusion (hE (k+p)) psi).
Proof. exact:supported_smooth_test_evaluation. Qed.

(** Source for [current_test_vector_interior_values]:
    exact original pointwise interior, supporting
    Federer 4.1.7, pp. 355–356. *)
Lemma current_test_vector_interior_values psi x:U x->
  @current_test_value R h2 n U hU p (current_test_vector_interior psi) x=
    current_vector_form_interior (@current_vector_smooth_value R h2 n U hU k xi x)
      (@current_test_value R h2 n U hU (k+p) psi x).
Proof.
move=>hx.
change (ev p (smooth_test_inclusion (hE p) (current_test_vector_interior psi)) x=
  current_vector_form_interior (@current_vector_smooth_value R h2 n U hU k xi x)
    (ev (k+p) (smooth_test_inclusion (hE (k+p)) psi) x)).
rewrite current_test_vector_interior_inclusion.
exact:smooth_current_vector_interior_values.
Qed.

(** Source for [current_test_vector_interior_continuous]:
    the original vector operation is continuous on
    actual compact test spaces, supporting Federer
    4.1.7, pp. 355–356. *)
Theorem current_test_vector_interior_continuous:
  open_family_continuous (@current_test_opens R h2 n U hU (k+p))
    (@current_test_opens R h2 n U hU p) current_test_vector_interior.
Proof.
exact:(@supported_smooth_test_continuous R X (Y (k+p)) (Y p) NX (NY (k+p)) (NY p)
  hNX (hNY (k+p)) (hNY p) U (E (k+p)) (E p) (ev (k+p)) (ev p)
  (hE (k+p)) (hE p) (D (k+p)) (D p) (hD (k+p)) (hD p) P hSupport
  (@smooth_current_vector_interior_continuous R h2 n k p U hU xi)).
Qed.
End CurrentTestVectorInterior.
