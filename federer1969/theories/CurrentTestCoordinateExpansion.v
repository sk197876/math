(** Federer (1969), 4.1.7, p. 356: the
    original finite coordinate expansion on actual
    compact tests. This transposes the coordinate
    form expansion from 4.1.6, p. 352,
    through the original constant form and vector
    fields, with every exterior degree retained. *)
From mathcomp Require Import functions all_boot all_order all_algebra classical_sets reals.
From Federer Require Import FiniteExteriorPowers BoundedHom HomogeneousHom GradedComponents Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading ExteriorIndices
  FiniteCoordinates AlternatingForms AlternatingSum AlternatingPairing AlternatingProduct
  ScalarCoefficients CovectorProducts ExteriorHomogeneousProducts ComassWedgeSymmetry EuclideanCoordinateForms
  CurrentSpaces CurrentVectorSpaces CurrentConstantFields CurrentDegreeTransport CurrentTestFormProduct
  CurrentTestVectorInterior CurrentVectorFormInterior CurrentScalarFormProduct
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentTestCoordinateExpansion.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation hE := (fun d=>@current_smooth_space_laws R h2 n U hU d).
Local Notation ev := (fun d=>@current_test_value R h2 n U hU d).
Local Notation DT := (fun d=>@current_test_space R h2 n U hU d).
Local Notation cf := (@current_constant_form R h2 n U hU).
Local Notation cv := (@current_constant_vector R h2 n U hU).
Local Notation el := (fun lambda:Lambda n m=>e_lambda (@coordinate_basis R n) (val lambda)).
Local Notation wl := (@omega_lambda R h2 X n (@euclidean_coordinate_form R n) m).
Local Notation P := (@current_test_form_product R h2 n m 0 U hU).
Local Notation I := (@current_test_vector_interior R h2 n m 0 U hU).
Local Notation Tr := (@current_test_degree_transport R h2 n U hU (m+0) m (addn0 m)).

(** Source for [current_test_coordinate_expansion]:
    the original coordinate reconstruction on tests,
    supporting the fourth displayed current identity
    of Federer 4.1.7, p. 356.
    The increasing tuple family may be empty;
    no restriction m<=n is added. *)
Theorem current_test_coordinate_expansion (psi:DT (m+0)):
  Tr psi=\sum_(lambda:Lambda n m) Tr (P (cf m (wl lambda)) (I (cv m (el lambda)) psi)).
Proof.
apply:(smooth_test_values_extensional (hE m))=>x hx.
change (smooth_test_values_hom (hE m) (Tr psi) x=
  smooth_test_values_hom (hE m)
    (\sum_(lambda:Lambda n m) Tr (P (cf m (wl lambda)) (I (cv m (el lambda)) psi))) x).
rewrite linear_sum fct_sumE.
change (ev m (Tr psi) x=\sum_(lambda:Lambda n m)
  ev m (Tr (P (cf m (wl lambda)) (I (cv m (el lambda)) psi))) x).
have hTerm (lambda:Lambda n m):
    ev m (Tr (P (cf m (wl lambda)) (I (cv m (el lambda)) psi))) x=
      (form_include (ev (m+0) psi x) (component_val (el lambda)):R)*:wl lambda.
  rewrite (@current_test_degree_transport_values R h2 n U hU (m+0) m (addn0 m)).
  rewrite (@current_test_form_product_values R h2 n m 0 U hU
    (cf m (wl lambda)) (I (cv m (el lambda)) psi) x hx).
  rewrite (@current_constant_form_values R h2 n U hU m (wl lambda) x hx).
  rewrite (@current_test_vector_interior_values R h2 n m 0 U hU (cv m (el lambda)) psi x hx).
  rewrite (@current_constant_vector_values R h2 n U hU m (el lambda) x hx).
  exact:current_form_interior_scalar_product.
rewrite (@current_test_degree_transport_values R h2 n U hU (m+0) m (addn0 m)).
rewrite {1}(@euclidean_real_form_coordinate_expansion R h2 n m
  (form_reindex (addn0 m) (ev (m+0) psi x))).
apply:eq_bigr=>lambda _;rewrite hTerm.
congr (_*:wl lambda).
rewrite pairing_form_homogeneous /pairing_homogeneous form_reindexE.
by [].
Qed.
End CurrentTestCoordinateExpansion.
