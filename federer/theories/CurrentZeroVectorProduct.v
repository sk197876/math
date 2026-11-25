(** Federer (1969), 4.1.7, p. 356: vector
    multiplication of zero-currents, identifying m+0
    with m explicitly. The operators are the
    original sealed test interiors and dual transposes. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingZero AlternatingPairing
  AlternatingSum ExteriorHomogeneousProducts ComassWedgeSymmetry CurrentSpaces CurrentVectorSpaces
  CurrentDegreeTransport CurrentDegreeTransportDerivatives CurrentEvaluation CurrentPointEvaluation
  CurrentVectorProduct CurrentTestVectorInterior CurrentVectorFormInterior CurrentInteriorPairing
  CurrentTestValueLaws CurrentDirectionalDerivative CurrentVectorDirectionalDerivative CurrentVectorDirectionalProduct
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentZeroVectorProduct.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation C := (fun k=>@current_space R h2 n U hU k).
Local Notation DT := (fun k=>@current_test_space R h2 n U hU k).
Local Notation V := (@current_vector_smooth_space R h2 n U hU m).
Local Notation vv := (@current_vector_smooth_value R h2 n U hU m).
Local Notation hV := (@current_vector_smooth_space_laws R h2 n U hU m).
Local Notation hE := (fun k=>@current_smooth_space_laws R h2 n U hU k).
Local Notation values := (fun k=>@current_test_value R h2 n U hU k).
Local Notation ev := (fun k=>@current_value R h2 n U hU k).
Local Notation Tr := (@current_degree_transport R h2 n U hU (m+0) m (addn0 m)).
Local Notation TTr := (@current_test_degree_transport R h2 n U hU m (m+0) (esym (addn0 m))).

(** Source for [current_zero_test_vector_interior]: the
    original scalar test obtained by evaluating
    a vector field against an m-form test,
    supporting Federer 4.1.7, p. 356. *)
Definition current_zero_test_vector_interior (xi:V):Hom (DT m) (DT 0):=
  hom_comp (@current_test_vector_interior R h2 n m 0 U hU xi) TTr.

(** Source for [current_zero_test_vector_values]: the
    original scalar test has value <xi,psi>,
    supporting Federer 4.1.7, p. 356. *)
Lemma current_zero_test_vector_values xi psi x:U x->
  zero_form_value (values 0 (current_zero_test_vector_interior xi psi) x)=
    pairing (vv xi x) (values m psi x).
Proof.
move=>hx;rewrite /current_zero_test_vector_interior hom_compE
  (@current_test_vector_interior_values R h2 n m 0 U hU xi (TTr psi) x hx)
  current_vector_interior_scalar_value
  (@current_test_degree_transport_values R h2 n U hU m (m+0) (esym (addn0 m)) psi x)
  form_reindex_include.
by [].
Qed.

(** Source for [current_zero_test_vector_field_linear]:
    the original scalar test is linear in
    its vector field, supporting the last
    two displayed equations in Federer 4.1.7,
    p. 356. *)
Lemma current_zero_test_vector_field_linear c (xi eta:V) psi:
  current_zero_test_vector_interior (c*:xi+eta) psi=
    c*:current_zero_test_vector_interior xi psi+current_zero_test_vector_interior eta psi.
Proof.
apply:(smooth_test_values_extensional (hE 0))=>x hx.
change (@current_test_value R h2 n U hU 0%N
    (current_zero_test_vector_interior (c*:xi+eta) psi) x=
  @current_test_value R h2 n U hU 0%N
    (c*:current_zero_test_vector_interior xi psi+
      current_zero_test_vector_interior eta psi) x).
apply:(can_inj (@zero_form_valueK R X R^o)).
rewrite current_test_add_value current_test_scale_value linearD linearZ /=
  !current_zero_test_vector_values //.
rewrite (@smooth_function_add_value R X (exterior_power X m) _ _ _ _ U V vv hV)
  (@smooth_function_scale_value R X (exterior_power X m) _ _ _ _ U V vv hV).
exact ((@pairing_bilinear R X R^o m).1
  (@current_test_value R h2 n U hU m psi x) c (vv xi x) (vv eta x)).
Qed.

(** Source for [current_zero_vector_product]: the
    original T wedge xi for dim T=0,
    with m+0 identified with m, supporting
    Federer 4.1.7, p. 356. *)
Definition current_zero_vector_product (xi:V):Hom (C 0) (C m):=
  hom_comp Tr (@current_vector_product R h2 n m 0 U hU xi).

(** Source for [current_zero_vector_product_evaluation]:
    the original zero-current product acts on
    the actual scalar pairing test, supporting
    Federer 4.1.7, p. 356. *)
Lemma current_zero_vector_product_evaluation xi T psi:
  ev m (current_zero_vector_product xi T) psi=
    ev 0 T (current_zero_test_vector_interior xi psi).
Proof.
rewrite /current_zero_vector_product hom_compE current_degree_transport_evaluation
  current_vector_product_evaluation;by [].
Qed.

(** Source for [current_zero_vector_field_linear]: the
    original product is linear in the smooth
    vector field for each fixed zero-current,
    supporting Federer 4.1.7, p. 356. *)
Lemma current_zero_vector_field_linear (T:C 0):
  linear (fun xi:V=>current_zero_vector_product xi T).
Proof.
move=>c xi eta;apply:(@current_values_extensional R h2 n m U hU)=>psi.
rewrite current_zero_vector_product_evaluation current_zero_test_vector_field_linear linearP.
rewrite linearP hom_addE hom_scaleE !current_zero_vector_product_evaluation;by [].
Qed.

(** Source for [current_zero_vector_field_product]:
    the original field-linear product as an
    actual Hom, supporting finite divergence sums
    in Federer 4.1.7, p. 356. *)
Definition current_zero_vector_field_product (T:C 0):Hom V (C m):=
  @HomMap R V (C m) (fun xi=>current_zero_vector_product xi T)
    (introT (asboolP _) (current_zero_vector_field_linear T)).

(** Source for [current_zero_vector_directional_product]:
    the original directional product identity for
    a zero-current, supporting the eighth equation
    in Federer 4.1.7, p. 356. *)
Theorem current_zero_vector_directional_product v (T:C 0) xi:
  @current_directional_derivative R h2 n m U hU v (current_zero_vector_product xi T)=
    current_zero_vector_product xi (@current_directional_derivative R h2 n 0 U hU v T)+
    current_zero_vector_product (@current_vector_smooth_directional_derivative R h2 n m U hU v xi) T.
Proof.
rewrite /current_zero_vector_product !hom_compE current_degree_transport_directional
  current_vector_directional_product linearD;by [].
Qed.
End CurrentZeroVectorProduct.
