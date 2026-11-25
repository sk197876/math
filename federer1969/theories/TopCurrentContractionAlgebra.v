(** Federer (1969), 4.1.7, p. 357: the
    top-degree boundary identity follows from
    Lambda_(n+1) R^n=0 and 1.5.3, p. 23.
    These are the actual coefficient identities
    used to transpose that printed argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import BoundedHom HomogeneousHom GradedComponents Hom Bilinear GrassmannAbbreviations FiniteCoordinates EuclideanCoordinateForms
  ExteriorAlgebra ExteriorGrading ExteriorAnticommutativity ExteriorHomogeneousProducts FiniteExteriorPowers
  AlternatingForms AlternatingPairing AlternatingSum AlternatingProduct ScalarCoefficients
  OneFormLinear OneFormIdentification OneCovectorInterior LeftInteriorHom LeftCovectorContraction SingleIndexContraction
  CurrentVectorFormInterior CurrentInteriorPairing CurrentPositiveInteriorPairing ComassWedgeSymmetry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section TopCurrentContractionAlgebra.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable p:nat.
Local Notation X := (R_n R p.+1).
Local Notation e := (@coordinate_basis R p.+1).
Local Notation dx := (@euclidean_coordinate_form R p.+1).
Local Notation ej := (fun j=>e_lambda e (val (Lambda_single j))).

(** Source for [top_current_interior_right_product]:
    (xi contracted DX_i) wedge e_j equals
    (-1)^(n-1) delta_ij xi in top degree,
    supporting Federer 4.1.7, p. 357.
    This intermediate sign precedes the minus
    sign in the original boundary sum. *)
Theorem top_current_interior_right_product (xi:exterior_power X p.+1) i j:
  wedge (component_val (positive_one_covector_interior h2 xi (dx i)))
    (exterior_generator (e j))=
    ((-1:R)^+p*(if i==j then 1 else 0))*:component_val xi.
Proof.
have hDegree:(p.+1<1+p.+1)%N by rewrite add1n.
have hVanishing:=@exterior_power_above_dimension R p.+1 X e (@coordinate_basisP R p.+1)
  h2 (1+p.+1) hDegree (exterior_product (ej j) xi).
have hW:wedge (exterior_generator (e j)) (component_val xi)=0.
  rewrite -(e_lambda_single_val e j) -exterior_productE hVanishing;exact:linear0.
have hLeft:=@left_covector_product R h2 X (dx i) (e j) (component_val xi).
rewrite hW (bil0l (@left_interior_hom_bilinear R h2 X)) in hLeft.
have hPair:one_hom (dx i) (e j)=if i==j then 1 else 0.
  exact:euclidean_coordinate_form_dual.
have hValue:wedge (exterior_generator (e j))
    (component_val (positive_one_covector_interior h2 xi (dx i)))=
    (if i==j then 1 else 0)*:component_val xi.
  rewrite positive_one_covector_interior_value.
  apply:esym;apply/eqP;rewrite -subr_eq0;apply/eqP.
  rewrite -hPair;exact:esym hLeft.
have hComm:=@exterior_anticommutative R X p 1%N
  (component_val (positive_one_covector_interior h2 xi (dx i))) (exterior_generator (e j))
  (component_homogeneous _) (exterior_generator_homogeneous _).
by rewrite muln1 hValue scalerA in hComm.
Qed.

(** Source for [top_current_covector_product]: the
    original top-form test identity dual to
    the preceding vector equation, supporting
    Federer 4.1.7, p. 357. All
    products and interiors are the original
    characterised operations. *)
Theorem top_current_covector_product (phi:A_m X R^o p.+1) i j:
  form_reindex (add1n p)
    (form_wedge h2 (scalar_bilinear R) (dx i)
      (current_vector_form_interior (ej j) (form_reindex (esym (add1n p)) phi)))=
    ((-1:R)^+p*(if i==j then 1 else 0))*:phi.
Proof.
apply:pairing_ext=>xi.
change (form_include (form_reindex (add1n p)
    (form_wedge h2 (scalar_bilinear R) (dx i)
      (current_vector_form_interior (ej j) (form_reindex (esym (add1n p)) phi))))
    (component_val xi)=
  pairing xi (((-1:R)^+p*(if i==j then 1 else 0))*:phi)).
rewrite form_reindex_include -current_positive_interior_pairing.
change (form_include (current_vector_form_interior (ej j) (form_reindex (esym (add1n p)) phi))
  (component_val (positive_one_covector_interior h2 xi (dx i)))=
  pairing xi (((-1:R)^+p*(if i==j then 1 else 0))*:phi)).
rewrite current_vector_form_interior_include form_reindex_include /ej e_lambda_single_val
  top_current_interior_right_product linearZ.
change (((-1:R)^+p*(if i==j then 1 else 0))*:form_include phi (component_val xi)=
  form_include (((-1:R)^+p*(if i==j then 1 else 0))*:phi) (component_val xi)).
by rewrite linearZ.
Qed.
End TopCurrentContractionAlgebra.
