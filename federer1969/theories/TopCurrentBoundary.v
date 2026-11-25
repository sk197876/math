(** Federer (1969), 4.1.7, p. 357: in
    top degree, (boundary T) wedge e_j
    =(-1)^n D_j T. The proof is
    the original coordinate boundary sum and
    the 1.5.3 contraction identity after
    Lambda_(n+1) R^n=0. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import FiniteExteriorPowers SingleIndexContraction Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanCoordinateForms ExteriorGrading
  AlternatingForms AlternatingSum ExteriorHomogeneousProducts CurrentSpaces CurrentVectorSpaces
  CurrentConstantFields CurrentDegreeTransport CurrentEvaluation CurrentPointEvaluation
  CurrentVectorProduct CurrentTestVectorInterior CurrentPositiveContraction CurrentTestFormProduct
  CurrentDirectionalDerivative CurrentBoundary TopCurrentContractionAlgebra CurrentSupportGeometry
  CurrentVectorInteriorSupport CurrentDegreeTransportSupport SmoothFunctionSpaceUP
  SmoothTestSpaces SmoothTestEvaluation CurrentTestValueLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TopCurrentBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable p:nat.
Local Notation X := (R_n R p.+1).
Local Notation e := (@coordinate_basis R p.+1).
Local Notation dx := (@euclidean_coordinate_form R p.+1).
Local Notation ej := (fun j=>e_lambda e (val (Lambda_single j))).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R p.+1)) U x.
Arguments hU : clear implicits.
Local Notation C := (fun k=>@current_space R h2 p.+1 U hU k).
Local Notation DT := (fun k=>@current_test_space R h2 p.+1 U hU k).
Local Notation hE := (fun k=>@current_smooth_space_laws R h2 p.+1 U hU k).
Local Notation values := (fun k=>@current_test_value R h2 p.+1 U hU k).
Local Notation ev := (fun k=>@current_value R h2 p.+1 U hU k).
Local Notation Tr := (@current_degree_transport R h2 p.+1 U hU (1+p) p.+1 (add1n p)).
Local Notation TTr := (@current_test_degree_transport R h2 p.+1 U hU p.+1 (1+p) (esym (add1n p))).
Local Notation field := (fun j=>@current_constant_vector R h2 p.+1 U hU 1%N (ej j)).
Local Notation pc := (@current_positive_one_contraction R h2 p.+1 p U hU).

(** Source for [top_current_vector_test_interior]: the
    original e_j interior operation on top
    test forms, supporting Federer 4.1.7,
    p. 357. *)
Definition top_current_vector_test_interior j:Hom (DT p.+1) (DT p):=
  hom_comp (@current_test_vector_interior R h2 p.+1 1%N p U hU (field j)) TTr.

(** Source for [top_current_vector_test_support]: the
    original coordinate interior shrinks test
    support, supporting the constancy implication
    in Federer 4.1.7, p. 357. *)
Theorem top_current_vector_test_support j psi:
  @current_test_support R h2 p.+1 p U hU (top_current_vector_test_interior j psi)
    `<=` @current_test_support R h2 p.+1 p.+1 U hU psi.
Proof.
move=>x hx.
have h:=@current_test_vector_interior_support R h2 p.+1 1%N p U hU (field j) (TTr psi) x hx.
by rewrite current_test_degree_transport_support in h.
Qed.

(** Source for [top_current_vector_product]: the
    original (n-1)-current wedge e_j, supporting
    Federer 4.1.7, p. 357, with
    its equal positive output degree identified. *)
Definition top_current_vector_product j:Hom (C p) (C p.+1):=
  hom_comp Tr (@current_vector_product R h2 p.+1 1%N p U hU (field j)).

(** Source for [top_current_vector_product_evaluation]:
    the original transpose evaluates the actual
    e_j interior test, supporting Federer
    4.1.7, p. 357. *)
Lemma top_current_vector_product_evaluation j T psi:
  ev p.+1 (top_current_vector_product j T) psi=
    ev p T (top_current_vector_test_interior j psi).
Proof.
rewrite /top_current_vector_product hom_compE current_degree_transport_evaluation
  current_vector_product_evaluation;by [].
Qed.

(** Source for [top_current_coordinate_test_identity]:
    the actual top test alpha_i wedge
    (e_j interior psi) is the signed
    coordinate multiple of psi, supporting
    Federer 4.1.7, p. 357. *)
Theorem top_current_coordinate_test_identity i j psi:
  @current_positive_test_wedge R h2 p.+1 p U hU (dx i)
    (top_current_vector_test_interior j psi)=
    ((-1:R)^+p*(if i==j then 1 else 0))*:psi.
Proof.
apply:(smooth_test_values_extensional (hE p.+1))=>x hx.
change (@current_test_value R h2 p.+1 U hU p.+1
    (@current_positive_test_wedge R h2 p.+1 p U hU (dx i)
      (top_current_vector_test_interior j psi)) x=
  @current_test_value R h2 p.+1 U hU p.+1
    (((-1:R)^+p*(if i==j then 1 else 0))*:psi) x).
rewrite current_test_scale_value.
rewrite /current_positive_test_wedge hom_compE
  (@current_test_degree_transport_values R h2 p.+1 U hU (1+p) p.+1 (add1n p) _ x).
rewrite (@current_test_form_product_values R h2 p.+1 1%N p U hU
  (@current_constant_form R h2 p.+1 U hU 1%N (dx i))
  (top_current_vector_test_interior j psi) x hx)
  (@current_constant_form_values R h2 p.+1 U hU 1%N (dx i) x hx).
rewrite /top_current_vector_test_interior hom_compE
  (@current_test_vector_interior_values R h2 p.+1 1%N p U hU (field j) (TTr psi) x hx)
  (@current_constant_vector_values R h2 p.+1 U hU 1%N (ej j) x hx)
  (@current_test_degree_transport_values R h2 p.+1 U hU p.+1 (1+p) (esym (add1n p)) psi x).
exact:top_current_covector_product.
Qed.

(** Source for [top_current_coordinate_contraction]:
    (T contracted DX_i) wedge e_j equals
    (-1)^(n-1) delta_ij T for an arbitrary
    top current, supporting Federer 4.1.7,
    p. 357. Representation by integration
    is not required. *)
Theorem top_current_coordinate_contraction (T:C p.+1) i j:
  top_current_vector_product j (pc (dx i) T)=
    ((-1:R)^+p*(if i==j then 1 else 0))*:T.
Proof.
apply:(@current_values_extensional R h2 p.+1 p.+1 U hU)=>psi.
rewrite top_current_vector_product_evaluation current_positive_one_contraction_evaluation
  top_current_coordinate_test_identity current_value_scale linearZ;by [].
Qed.

(** Source for [top_current_boundary_coordinate]: the
    original identity (boundary T) wedge e_j
    =(-1)^n D_j T, Federer 4.1.7,
    p. 357. Here n=p+1>0;
    the sign is the printed sign. *)
Theorem top_current_boundary_coordinate (T:C p.+1) j:
  top_current_vector_product j (@current_boundary R h2 p.+1 p U hU T)=
    (-1:R)^+p.+1*:@current_directional_derivative R h2 p.+1 p.+1 U hU (e j) T.
Proof.
rewrite current_positive_boundary_coordinates linearN linear_sum.
have hSum:(\sum_i top_current_vector_product j
    (pc (dx i) (@current_directional_derivative R h2 p.+1 p.+1 U hU (e i) T)))=
    (-1:R)^+p*:@current_directional_derivative R h2 p.+1 p.+1 U hU (e j) T.
  transitivity (\sum_i ((-1:R)^+p*(if i==j then 1 else 0))*:
    @current_directional_derivative R h2 p.+1 p.+1 U hU (e i) T).
  - apply:eq_bigr=>i _;exact:top_current_coordinate_contraction.
  - rewrite (bigD1 j) //= eqxx mulr1.
    have hOther:(\sum_(i | i!=j) ((-1:R)^+p*(if i==j then 1 else 0))*:
      @current_directional_derivative R h2 p.+1 p.+1 U hU (e i) T)=0.
      apply:big1=>i hi;by rewrite (negbTE hi) mulr0 scale0r.
    by rewrite hOther addr0.
by rewrite hSum exprS mulN1r scaleNr.
Qed.
End TopCurrentBoundary.
