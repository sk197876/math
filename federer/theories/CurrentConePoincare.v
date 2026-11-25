(** Federer (1969), 4.1.10, p. 364: a closed positive-degree
    compact test form is the exterior derivative of its original homotopy
    integral. Apply the published erratum, p. 6, book p. 364 line 11:
    the printed current-space subscript is the test-form superscript.
    Actual test zero extension permits an ambient contraction; on a
    star-shaped source every segment stays in the original domain. The
    primitive is smooth and need not have compact support. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothTestSpaces SmoothCurrentExteriorDerivative
  CurrentTestExteriorDerivative CurrentOpenRestriction CurrentOpenRestrictionBoundary
  CurrentHomotopyUP CurrentHomotopySliceClass CurrentHomotopyGeometry
  CurrentHomotopyTransgressionSealed CurrentHomotopyPositiveFormFormula
  SmoothFormPullbackSealed CurrentConeHomotopySealed CurrentConeHomotopyClass
  CurrentElementaryPullbacks.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CurrentConePoincare.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n j : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Variable U : set X.
Hypothesis hOpen : forall x, U x -> norm_domain_interior NX U x.
Variable u : X.
Local Notation V := (fun _:X => True).
Local Notation A := (fun _:R => True).
Local Notation f := (fun _:X => u).
Local Notation g := (fun x:X => x).
Local Notation h := (@CurrentConeHomotopy.value R n u).
Local Notation hH := (@current_cone_ambient_homotopy R n u U hOpen).
Local Notation hU := (@current_homotopy_source_open R n n A U V f g h hH.1).
Local Notation hV := (@current_homotopy_target_open R n n A U V f g h hH.1).
Local Notation EU := (fun k => @current_smooth_space R h2 n U hU k).
Local Notation EV := (fun k => @current_smooth_space R h2 n V hV k).
Local Notation hEU := (fun k => @current_smooth_space_laws R h2 n U hU k).
Local Notation hEV := (fun k => @current_smooth_space_laws R h2 n V hV k).
Local Notation extension := (fun k => @current_open_test_extension R h2 n k
  U V hU hV (fun _ _ => Logic.I)).
Local Notation K := (@CurrentHomotopyTransgression.value R h2 n n j A U V f g h hH).
Local Notation dU := (fun k => @smooth_current_exterior_derivative R h2 n k U hU).
Local Notation dV := (fun k => @smooth_current_exterior_derivative R h2 n k V hV).

(** Source for [current_cone_test_primitive]: the actual smooth
    homotopy integral in Federer 4.1.10, p. 364, on the original
    compact tests. This composition uses only the opaque test extension,
    actual test inclusion and already sealed transgression of 4.1.9. *)
Definition current_cone_test_primitive : Hom (@current_test_space R h2 n U hU j.+1) (EU j) :=
  hom_comp K (hom_comp (smooth_test_inclusion (hEV j.+1)) (extension j.+1)).

(** Source for [current_cone_test_poincare]: a closed original
    positive-degree test form equals d of its smooth cone primitive,
    Federer 4.1.10, p. 364, with the published superscript correction.
    This ambient zero-extension version is valid on every open U;
    star-shapedness identifies the integral with the original U formula. *)
Theorem current_cone_test_poincare
    (psi : @current_test_space R h2 n U hU j.+1) :
  @current_test_exterior_derivative R h2 n j.+1 U hU psi=0 ->
  smooth_test_inclusion (hEU j.+1) psi=dU j (current_cone_test_primitive psi).
Proof.
move=> hClosed.
pose phi := smooth_test_inclusion (hEV j.+1) (extension j.+1 psi).
have hAmbientClosed : dV j.+1 phi=0.
  rewrite /phi -current_test_exterior_derivative_inclusion
    -current_open_test_exterior_commutes hClosed !linear0.
  by [].
pose endpoints := @current_homotopy_endpoint_images R n n A U V f g h hH.1.
pose classes := @current_smooth_homotopy_endpoint_classes R n n A U V f g h hH.
have hIdentity : @SmoothFormPullback.operator R h2 n n j.+1 U V hU hV
    g endpoints.2 classes.2 phi=smooth_test_inclusion (hEU j.+1) psi.
  apply: (smooth_function_extensional (hEU j.+1)) => x hx.
  rewrite (@current_identity_pullback_values R h2 n U hU j.+1 V hV
    endpoints.2 classes.2 phi x hx).
  change (@current_test_value R h2 n V hV j.+1 (extension j.+1 psi) x=
    @current_test_value R h2 n U hU j.+1 psi x).
  exact: current_open_test_extension_values.
have hFormula := @current_homotopy_positive_form_formula R h2 n n j
  A U V f g h hH phi.
rewrite hIdentity current_constant_positive_pullback subr0
  hAmbientClosed linear0 add0r in hFormula.
exact: hFormula.
Qed.
End CurrentConePoincare.
