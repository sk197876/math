(** Federer (1969), 3.4.7, p. 325: coefficient
    extension is unique and preserves the original constants,
    variable and degree. Faithful coefficients give a faithful
    polynomial map. Only the independent laws are used. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialBasicLaws
  CommutativePolynomialDegreeUP PolynomialCoefficientMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Laws.
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

(** Source for [polynomial_coefficient_map_unique]: mapped
    coefficients uniquely determine the extension, supporting
    3.4.7, p. 325. *)
Lemma polynomial_coefficient_map_unique (M N:B->D):
  is_polynomial_coefficient_map source target phi M ->
  is_polynomial_coefficient_map source target phi N ->M = N.
Proof.
move=>hM hN;apply:funext=>P.
apply:(@polynomial_coefficients_unique C D embedC variableC target hTarget)=>i.
by rewrite hM hN.
Qed.

(** Source for [polynomial_coefficient_map_injective]: faithful
    extension of original coefficients preserves polynomial equality,
    supporting the Gauss argument in 3.4.7, p. 325. *)
Lemma polynomial_coefficient_map_injective (M:B->D):
  is_polynomial_coefficient_map source target phi M ->injective phi ->injective M.
Proof.
move=>hM hPhi P Q hEqual.
apply:(@polynomial_coefficients_unique A B embedA variableA source hSource)=>i.
apply:hPhi;rewrite -(hM P i) -(hM Q i);by rewrite hEqual.
Qed.

(** Source for [polynomial_coefficient_map_constant]: original
    constants map to their extended constants, supporting
    3.4.7, p. 325. *)
Lemma polynomial_coefficient_map_constant (M:B->D):
  is_polynomial_coefficient_map source target phi M ->
  forall a,M (embedA a) = embedC (phi a).
Proof.
move=>hM a;apply:(@polynomial_coefficients_unique C D embedC variableC target hTarget)=>i.
rewrite hM (@polynomial_coefficient_constant A B embedA variableA source hSource)
  (@polynomial_coefficient_constant C D embedC variableC target hTarget).
by case:(i==0%N);rewrite ?rmorph0.
Qed.

(** Source for [polynomial_coefficient_map_variable]: the variable
    remains the same independent variable after coefficient
    extension, supporting 3.4.7, p. 325. *)
Lemma polynomial_coefficient_map_variable (M:B->D):
  is_polynomial_coefficient_map source target phi M ->M variableA = variableC.
Proof.
move=>hM;apply:(@polynomial_coefficients_unique C D embedC variableC target hTarget)=>i.
rewrite hM (@polynomial_coefficient_variable A B embedA variableA source hSource)
  (@polynomial_coefficient_variable C D embedC variableC target hTarget).
by case:(i==1%N);rewrite ?rmorph0 ?rmorph1.
Qed.

(** Source for [polynomial_coefficient_map_degree]: faithful
    coefficient extension preserves the actual nonzero leading
    coefficient and degree, supporting 3.4.7, p. 325. *)
Lemma polynomial_coefficient_map_degree (M:B->D) (P:B) n:
  is_polynomial_coefficient_map source target phi M ->injective phi ->
  is_polynomial_degree source P n ->is_polynomial_degree target (M P) n.
Proof.
move=>hM hPhi [hLeading hHigher];split.
- rewrite hM=>hZero;apply:hLeading;apply:hPhi;by rewrite rmorph0.
- move=>i hi;by rewrite hM hHigher // rmorph0.
Qed.
End Laws.
