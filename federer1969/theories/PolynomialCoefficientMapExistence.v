(** Federer (1969), 3.4.7, p. 325: actual coefficient
    extension to fractions exists and preserves the ring laws.
    The proof uses only the independent polynomial specifications. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialBasicLaws
  CommutativePolynomialFiniteSums PolynomialCoefficientMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Map.
Variables A B C D:comNzRingType.
Variable embedA:{rmorphism A->B}.
Variable variableA:B.
Variable source:B->nat->A.
Variable embedC:{rmorphism C->D}.
Variable variableC:D.
Variable target:D->nat->C.
Hypothesis hSource:is_commutative_polynomial_ring embedA variableA source.
Hypothesis hTarget:is_commutative_polynomial_ring embedC variableC target.
Variable phi:{rmorphism A->C}.

(** Source for [polynomial_mapped_coefficients_exist]: mapped
    finite coefficients still specify an actual polynomial,
    supporting 3.4.7, p. 325. *)
Lemma polynomial_mapped_coefficients_exist (P:B):
  exists Q:D,forall i,target Q i = phi (source P i).
Proof.
have [N hN]:=@polynomial_coefficients_finite A B embedA variableA source hSource P.
apply:(@polynomial_interpolation_exists C D embedC variableC target hTarget).
exists N=>i hi;by rewrite hN // rmorph0.
Qed.

(** Source for [polynomial_coefficient_map_witness]: a local
    choice from proved interpolation, supporting 3.4.7, p. 325. *)
Definition polynomial_coefficient_map_witness (P:B):D:=
  projT1 (cid (polynomial_mapped_coefficients_exist P)).

(** Source for [polynomial_coefficient_map_witness_laws]: the
    selected witness has exactly the prescribed coefficients,
    supporting 3.4.7, p. 325. *)
Lemma polynomial_coefficient_map_witness_laws:
  is_polynomial_coefficient_map source target phi polynomial_coefficient_map_witness.
Proof. move=>P;exact:(projT2 (cid (polynomial_mapped_coefficients_exist P))). Qed.

(** Source for [polynomial_coefficient_map_additive]: coefficient
    extension preserves addition and zero, supporting 3.4.7, p. 325. *)
Lemma polynomial_coefficient_map_additive:nmod_morphism polynomial_coefficient_map_witness.
Proof.
pose M:=polynomial_coefficient_map_witness.
have hM:=polynomial_coefficient_map_witness_laws.
split.
- apply:(@polynomial_coefficients_unique C D embedC variableC target hTarget)=>i.
  by rewrite hM (@polynomial_coefficient_zero A B embedA variableA source hSource)
    rmorph0 (@polynomial_coefficient_zero C D embedC variableC target hTarget).
- move=>P Q;apply:(@polynomial_coefficients_unique C D embedC variableC target hTarget)=>i.
  by rewrite hM (@polynomial_coefficient_add A B embedA variableA source hSource)
    rmorphD (@polynomial_coefficient_add C D embedC variableC target hTarget) !hM.
Qed.
#[local] HB.instance Definition _:=GRing.isNmodMorphism.Build B D
  polynomial_coefficient_map_witness polynomial_coefficient_map_additive.

(** Source for [polynomial_coefficient_map_multiplicative]: coefficient
    extension preserves products and one, supporting 3.4.7, p. 325. *)
Lemma polynomial_coefficient_map_multiplicative:monoid_morphism polynomial_coefficient_map_witness.
Proof.
have hM:=polynomial_coefficient_map_witness_laws.
split.
- apply:(@polynomial_coefficients_unique C D embedC variableC target hTarget)=>i.
  rewrite hM (@polynomial_coefficient_one A B embedA variableA source hSource)
    (@polynomial_coefficient_one C D embedC variableC target hTarget).
  by case:(i==0%N);rewrite ?rmorph0 ?rmorph1.
- move=>P Q;apply:(@polynomial_coefficients_unique C D embedC variableC target hTarget)=>i.
  rewrite hM (@polynomial_coefficient_multiply A B embedA variableA source hSource)
    rmorph_sum (@polynomial_coefficient_multiply C D embedC variableC target hTarget).
  apply:eq_bigr=>j _;by rewrite rmorphM !hM.
Qed.
#[local] HB.instance Definition _:=GRing.isMonoidMorphism.Build B D
  polynomial_coefficient_map_witness polynomial_coefficient_map_multiplicative.

(** Source for [polynomial_coefficient_map_exists]: the original
    coefficient homomorphism extends to a polynomial ring
    homomorphism, supporting 3.4.7, p. 325. *)
Theorem polynomial_coefficient_map_exists:
  exists map:{rmorphism B->D},is_polynomial_coefficient_map source target phi map.
Proof.
exists (GRing.RMorphism.clone B D polynomial_coefficient_map_witness _).
exact:polynomial_coefficient_map_witness_laws.
Qed.
End Map.
