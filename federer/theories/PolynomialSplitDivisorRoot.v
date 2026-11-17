(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: a nonconstant divisor of the
    original split polynomial has one of its
    listed roots. Apply the already proved root
    adjunction and universal split criterion directly.
    Source: Bourbaki, Algebra II (1990), Chapter V,
    section 4, no. 2, pp. V.21–22. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativeFactorizationUP CommutativePolynomialUP
  CommutativePolynomialDegreeUP CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationLaws
  PolynomialCoefficientMapUP PolynomialCoefficientMapLaws PolynomialRootExtension
  PolynomialLinearSplitUP PolynomialLinearSplitLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_split_divisor_has_listed_root]:
    each original nonconstant factor has a root
    in the containing field, the elementary divisor
    consequence of the cited splitting-factorisation
    definition. A further root adjunction and the
    already proved complete root list descend it
    to the original field; factorisation is reused. *)
Theorem polynomial_split_divisor_has_listed_root (K:fieldType) (B:comNzRingType)
  (embedK:{rmorphism K->B}) (variableK P:B) (source:B->nat->K) n
  (hB:is_commutative_polynomial_ring embedK variableK source)
  (L:fieldType) (phi:{rmorphism K->L}) (c:L) (roots:seq L)
  (hSplit:is_linear_polynomial_split embedK variableK P n phi c roots)
  (D:comNzRingType) (embedL:{rmorphism L->D}) (variableL:D) (target:D->nat->L)
  (hD:is_commutative_polynomial_ring embedL variableL target)
  (M:{rmorphism B->D}) (hM:is_polynomial_coefficient_map source target phi M) (Q:D) d:
  is_polynomial_degree target Q d ->(0<d)%N ->commutative_divides Q (M P) ->
  exists r:L,r \in roots /\forall F:{rmorphism D->L},
    (forall a:L,F (embedL a) = a) ->F variableL = r ->F Q = 0.
Proof.
move=>hDegree hPositive [U hDivides].
have [T [psi [z [E [hE hRoot]]]]]:=@polynomial_root_extension_exists L D
  embedL variableL target hD Q d hDegree hPositive.
pose chi:{rmorphism K->T}:=GRing.RMorphism.clone K T (psi \o phi) _.
pose EM:{rmorphism B->T}:=GRing.RMorphism.clone B T (E \o M) _.
have hEM:is_commutative_polynomial_evaluation embedK variableK chi z EM.
  constructor.
  - move=>a;change (E (M (embedK a)) = chi a).
    rewrite (@polynomial_coefficient_map_constant K B L D embedK variableK source
      embedL variableL target hB hD phi M hM) (polynomial_evaluation_constants hE).
    by [].
  - change (E (M variableK) = z).
    rewrite (@polynomial_coefficient_map_variable K B L D embedK variableK source
      embedL variableL target hB hD phi M hM).
    exact:polynomial_evaluation_variable hE.
have hOriginal:EM P = 0.
  change (E (M P) = 0);by rewrite hDivides rmorphM hRoot mulr0.
have [r [hR hZ]]:=(@linear_polynomial_split_root_criterion K B embedK variableK P n L phi c roots hSplit
  T psi chi z EM (fun a=>erefl (chi a)) hEM).1 hOriginal.
exists r;split;first exact:hR.
move=>F hConstants hVariable.
pose psiF:{rmorphism D->T}:=GRing.RMorphism.clone D T (psi \o F) _.
have hPsiF:is_commutative_polynomial_evaluation embedL variableL psi z psiF.
  constructor.
  - move=>a;change (psi (F (embedL a)) = psi a);by rewrite hConstants.
  - change (psi (F variableL) = z);by rewrite hVariable -hZ.
have hEqual:=@polynomial_evaluation_unique L D T embedL variableL target hD psi z E psiF hE hPsiF Q.
have hZero:psi (F Q) = 0.
  change (psiF Q = 0);by rewrite -hEqual.
apply:(fmorph_inj psi);by rewrite hZero rmorph0.
Qed.
