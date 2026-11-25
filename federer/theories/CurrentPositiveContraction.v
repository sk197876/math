(** Federer (1969), 4.1.7, p. 356: fixed
    one-covector contraction on positive-degree currents.
    The aliases identify 1+p with p+1;
    the actual test multiplication and transpose
    remain the original operations. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import AlternatingSum BoundedHom HomogeneousHom GradedComponents Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanCoordinateForms ExteriorGrading
  AlternatingForms AlternatingPairing AlternatingProduct ExteriorHomogeneousProducts ComassWedgeSymmetry
  OneCovectorInterior CurrentSpaces CurrentContraction CurrentTestFormProduct CurrentConstantFields
  CurrentDegreeTransport CurrentDegreeTransportIdentity CurrentDegreeTransportDerivatives CurrentEvaluation
  CurrentBoundary CurrentBoundaryCoordinates CurrentDirectionalDerivative CurrentPositiveInteriorPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentPositiveContraction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p:nat.
Local Notation X := (R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation C := (fun k=>@current_space R h2 n U hU k).
Local Notation DT := (fun k=>@current_test_space R h2 n U hU k).
Local Notation values := (fun k=>@current_test_value R h2 n U hU k).
Local Notation ev := (fun k=>@current_value R h2 n U hU k).
Local Notation Tr := (@current_degree_transport R h2 n U hU p.+1 (1+p) (esym (add1n p))).
Local Notation TTr := (@current_test_degree_transport R h2 n U hU (1+p) p.+1 (add1n p)).
Local Notation constant := (@current_constant_form R h2 n U hU 1%N).

(** Source for [current_positive_test_wedge]: the
    original test alpha wedge psi, with its
    positive output degree identified, supporting
    Federer 4.1.7, p. 356. *)
Definition current_positive_test_wedge (alpha:A_m X R^o 1):Hom (DT p) (DT p.+1):=
  hom_comp TTr (@current_test_form_product R h2 n 1%N p U hU (constant alpha)).

(** Source for [current_positive_test_wedge_pairing]:
    the actual positive-degree test product has
    the original characteristic interior pairing,
    supporting Federer 4.1.7, p. 356. *)
Lemma current_positive_test_wedge_pairing alpha psi xi x:U x->
  pairing xi (values p.+1 (current_positive_test_wedge alpha psi) x)=
    pairing (positive_one_covector_interior h2 xi alpha) (values p psi x).
Proof.
move=>hx;rewrite /current_positive_test_wedge hom_compE
  (@current_test_degree_transport_values R h2 n U hU (1+p) p.+1 (add1n p) _ x).
change (form_include (form_reindex (add1n p)
  (values (1+p) (@current_test_form_product R h2 n 1%N p U hU (constant alpha) psi) x))
    (component_val xi)=
  pairing (positive_one_covector_interior h2 xi alpha) (values p psi x)).
rewrite form_reindex_include (@current_test_form_product_values R h2 n 1%N p U hU
  (constant alpha) psi x hx) (@current_constant_form_values R h2 n U hU 1%N alpha x hx).
exact:esym (current_positive_interior_pairing h2 xi alpha (values p psi x)).
Qed.

(** Source for [current_positive_one_contraction]: the
    original current contracted alpha in the
    third and eighth equations of Federer
    4.1.7, p. 356. *)
Definition current_positive_one_contraction (alpha:A_m X R^o 1):Hom (C p.+1) (C p):=
  hom_comp (@current_contraction R h2 n 1%N p U hU (constant alpha)) Tr.

(** Source for [current_positive_one_contraction_evaluation]:
    the original transpose action on alpha
    wedge psi, supporting Federer 4.1.7,
    p. 356. *)
Lemma current_positive_one_contraction_evaluation alpha T psi:
  ev p (current_positive_one_contraction alpha T) psi=
    ev p.+1 T (current_positive_test_wedge alpha psi).
Proof.
rewrite /current_positive_one_contraction hom_compE current_contraction_evaluation
  current_degree_reverse_evaluation;by [].
Qed.

(** Source for [current_positive_boundary_coordinates]:
    boundary T=-sum_j (D_j T) contracted DX_j,
    Federer 4.1.7, p. 356, stated
    directly in the original positive degree. *)
Theorem current_positive_boundary_coordinates (T:C p.+1):
  @current_boundary R h2 n p U hU T=
    -\sum_j current_positive_one_contraction (euclidean_coordinate_form j)
      (@current_directional_derivative R h2 n p.+1 U hU (@coordinate_basis R n j) T).
Proof.
have h:=@current_boundary_coordinate_formula R h2 n p U hU (Tr T).
rewrite current_degree_transport_roundtrip in h.
rewrite h;congr (-_);apply:eq_bigr=>j _.
rewrite current_degree_transport_directional;by [].
Qed.
End CurrentPositiveContraction.
