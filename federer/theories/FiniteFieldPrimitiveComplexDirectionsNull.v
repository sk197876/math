(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    pp. 329–330: almost every original complex coefficient
    direction is primitive. Reuse the proved real primitive
    direction theorem on the paired real and imaginary generators;
    the standard complex coordinate map retains the original sum. *)
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
Section Directions.
Variable R:realType.
Variables K L:fieldType.
Variable eta:{rmorphism ComplexScalars.C R->K}.
Variable phi:{rmorphism K->L}.
Variable q:nat.
Variable x:'I_q->L.
Local Notation C:=(ComplexScalars.C R).
Local Notation z:=(fun v:coordinate_space C q=>\sum_i phi (eta (v i))*x i).
Local Notation paired:=(fun j:'I_(q+q)=>match split j with
  inl i=>x i | inr i=>phi (eta (ComplexScalars.ii R))*x i end).
Local Notation realScalar:=(GRing.RMorphism.clone R K (eta \o ComplexScalars.embed R) _).

(** Source for [complex_primitive_paired_generators]: the paired
    original coordinate classes still generate the same original
    extension, supporting 3.4.12, p. 339. *)
Lemma complex_primitive_paired_generators:
  is_generated_commutative_subring (fun y:L=>(exists i:'I_q,y=x i) \/exists a:K,y=phi a) setT ->
  is_generated_commutative_subring (fun y:L=>(exists j:'I_(q+q),y=paired j) \/exists a:K,y=phi a) setT.
Proof.
move=>hGenerated;constructor.
- exact:generated_commutative_subring_laws hGenerated.
- by move=>y _.
- move=>J hJ hContains;apply:(generated_commutative_subring_minimal hGenerated hJ)=>y.
  move=>[[i hi]|hScalar];last by apply:hContains;right.
  apply:hContains;left;exists (lshift q i).
  by rewrite (unsplitK (inl _ i)).
Qed.

(** Source for [complex_primitive_paired_sum]: the paired real
    expression equals the exact original complex coefficient sum,
    supporting 3.4.12, p. 339. *)
Lemma complex_primitive_paired_sum (v:R_n R (q+q)):
  \sum_(j<q+q) phi (realScalar (v j))*paired j=
    z (complex_from_real_coordinates v).
Proof.
have hLeft:(\sum_(i<q) phi (realScalar (v (lshift q i)))*paired (lshift q i))=
    \sum_(i<q) phi (realScalar (v (lshift q i)))*x i.
  apply:eq_bigr=>i _;by rewrite (unsplitK (inl _ i)).
have hRight:(\sum_(i<q) phi (realScalar (v (rshift q i)))*paired (rshift q i))=
    \sum_(i<q) phi (realScalar (v (rshift q i)))*(phi (eta (ComplexScalars.ii R))*x i).
  apply:eq_bigr=>i _;by rewrite (unsplitK (inr _ i)).
have hSplit:(\sum_(i<q) (phi (realScalar (v (lshift q i)))*x i+
    phi (realScalar (v (rshift q i)))*(phi (eta (ComplexScalars.ii R))*x i)))=
    (\sum_(i<q) phi (realScalar (v (lshift q i)))*x i)+
    (\sum_(i<q) phi (realScalar (v (rshift q i)))*(phi (eta (ComplexScalars.ii R))*x i)).
  exact:big_split.
rewrite big_split_ord hLeft hRight.
change ((\sum_(i<q) phi (realScalar (v (lshift q i)))*x i)+
    (\sum_(i<q) phi (realScalar (v (rshift q i)))*(phi (eta (ComplexScalars.ii R))*x i))=
    z (complex_from_real_coordinates v)).
rewrite -hSplit.
apply:eq_bigr=>i _.
rewrite /complex_from_real_coordinates ffunE rmorphD rmorphM rmorphD rmorphM.
change (phi (eta (ComplexScalars.embed R (v (lshift q i))))*x i+
  phi (eta (ComplexScalars.embed R (v (rshift q i))))*(phi (eta (ComplexScalars.ii R))*x i)=
  (phi (eta (ComplexScalars.embed R (v (lshift q i))))+
    phi (eta (ComplexScalars.ii R))*phi (eta (ComplexScalars.embed R (v (rshift q i)))))*x i).
by rewrite mulrDl mulrA [phi (eta (ComplexScalars.embed R (v (rshift q i))))*phi (eta (ComplexScalars.ii R))]mulrC.
Qed.

(** Source for [finite_field_primitive_complex_directions_null]:
    both original ambient and sphere nullity assertions for complex
    primitive directions, in the standard real coordinate chart,
    3.4.12, p. 339. The extension fields and coordinate classes
    are the original ones; no primitive conclusion is a premise. *)
Theorem finite_field_primitive_complex_directions_null (B:comNzRingType)
    (embed:{rmorphism K->B}) (variable:B) (coefficient:B->nat->K)
    (hP:is_commutative_polynomial_ring embed variable coefficient):
  is_finitely_generated_ring_submodule (setT:set [the lmodType K of ring_restricted_space phi L^o]) ->
  is_generated_commutative_subring (fun y:L=>(exists i:'I_q,y=x i) \/exists a:K,y=phi a) setT ->
  let bad:=fun v:R_n R (q+q)=>~is_generated_commutative_subring
    (fun y:L=>y=z (complex_from_real_coordinates v) \/exists a:K,y=phi a) setT in
  @euclidean_lebesgue_measure R (q+q) bad=0%:E /\
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (q+q))) (q+q-1)
    [set v|bad v /\inner_norm (@euclidean_inner_productP R (q+q)) v= 1]=0%:E.
Proof.
move=>hFinite hGenerated bad.
have hPaired:=complex_primitive_paired_generators hGenerated.
have hNull:=@finite_field_primitive_real_directions_null R K L realScalar phi (q+q) paired
  B embed variable coefficient hP hFinite hPaired.
pose badR:=fun v:R_n R (q+q)=>~is_generated_commutative_subring
    (fun y:L=>y=\sum_(j<q+q) phi (realScalar (v j))*paired j \/exists a:K,y=phi a) setT.
change (@euclidean_lebesgue_measure R (q+q) badR=0%:E /\
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (q+q))) (q+q-1)
    [set v|badR v /\inner_norm (@euclidean_inner_productP R (q+q)) v= 1]=0%:E) in hNull.
have hBad:badR=bad.
  apply:funext=>v;by rewrite /badR /bad complex_primitive_paired_sum.
rewrite hBad in hNull;exact:hNull.
Qed.
End Directions.
