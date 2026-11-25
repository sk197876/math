(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    p. 330: conjugated unitary coordinate coefficients are primitive
    almost everywhere. Apply the proved primitive-direction theorem
    with the original scalar map composed with conjugation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed FiniteCoordinates StandardHermitianCoordinates
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric RingScalarRestriction RingSubmoduleUP
  CommutativeSubringUP CommutativePolynomialUP FiniteFieldPrimitiveDirectionsNull EuclideanLebesgueDimensions HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
From Federer Require Import ComplexScalarLaws ComplexConjugationMorphism FiniteFieldPrimitiveComplexDirectionsNull.
(** Source for [finite_field_conjugated_primitive_directions_null]: the
    original ambient and sphere exceptional sets for the exact
    conjugated coordinate sum are null, 3.4.12, p. 339. *)
Theorem finite_field_conjugated_primitive_directions_null (R:realType) (K L:fieldType)
  (eta:{rmorphism ComplexScalars.C R->K}) (phi:{rmorphism K->L})
  q (x:'I_q->L) (B:comNzRingType) (embed:{rmorphism K->B})
  variable coefficient (hP:is_commutative_polynomial_ring embed variable coefficient):
  is_finitely_generated_ring_submodule (setT:set [the lmodType K of ring_restricted_space phi L^o]) ->
  is_generated_commutative_subring (fun y:L=>(exists i:'I_q,y=x i) \/exists a:K,y=phi a) setT ->
  let bad:=fun v:R_n R (q+q)=>~is_generated_commutative_subring
    (fun y:L=>y=\sum_i phi (eta (ComplexScalarTheory.conjugate ((complex_from_real_coordinates v) i)))*x i \/
      exists a:K,y=phi a) setT in
  @euclidean_lebesgue_measure R (q+q) bad=0%:E /\
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (q+q))) (q+q-1)
    [set v|bad v /\inner_norm (@euclidean_inner_productP R (q+q)) v= 1]=0%:E.
Proof.
move=>hFinite hGenerated bad.
pose theta:{rmorphism ComplexScalars.C R->K}:=GRing.RMorphism.clone (ComplexScalars.C R) K
  (eta \o (@complex_conjugation_morphism R)) _.
exact:(@finite_field_primitive_complex_directions_null R K L theta phi q x B embed variable coefficient hP
  hFinite hGenerated).
Qed.
