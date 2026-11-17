(** Federer (1969), 3.4.12, p. 339, extending 3.4.7,
    p. 324: a nonzero complex-valued homogeneous polynomial
    has a nonzero real or imaginary homogeneous part.
    The complex zero set lies in its scalar zero set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexScalarLaws ComplexCoefficientAlgebra
  SymmetricForms SymmetricFormSum SymmetricFormPostcompose HomogeneousPolynomialFunctions
  PolynomialFunctions PolynomialDiagonalNorm SymmetricPolynomialEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_homogeneous_scalarisation]: the scalar
    homogeneous polynomial needed for the two null exceptional
    direction sets, 3.4.12, p. 339. The original
    degree and every complex zero remain. *)
Theorem complex_homogeneous_scalarisation (R:realType) (X:lmodType R) k
    (P:X->restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o):
  is_homogeneous_polynomial k P ->(exists v,P v<>0) ->
  exists Q:PolynomialFunction X R^o,is_homogeneous_polynomial k Q /\
    (exists v,Q v<>0) /\forall x,P x=0 ->Q x=0.
Proof.
move=>[F hF] [v hv].
pose CR:=restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o.
have hCoordinate:exists L:{linear CR->R^o},L (P v)<>0.
  case hRe:(ComplexScalars.re (P v)==0).
  - exists (GRing.Linear.clone R CR R^o *:%R (@complex_imaginary_part R) _)=>hIm.
    apply:hv;apply:ComplexScalarTheory.coordinates_injective.
    + change (complex_real_part (P v)=complex_real_part (0:CR)).
      by rewrite linear0;exact/eqP.
    + change (complex_imaginary_part (P v)=complex_imaginary_part (0:CR)).
      by rewrite linear0;exact:hIm.
  - exists (GRing.Linear.clone R CR R^o *:%R (@complex_real_part R) _).
    change (ComplexScalars.re (P v)<>0).
    move=>hz;have hn:ComplexScalars.re (P v)!=0 by rewrite hRe.
    by rewrite hz eqxx in hn.
have [L hL]:=hCoordinate.
pose G:=symmetric_form_postcompose L F.
pose Q:=polynomial_from_forms (sform_include G).
have hQ x:Q x=L (P x).
  rewrite /Q polynomial_from_formsE symmetric_polynomial_value_include
    !sform_polynomial_diagonal_value /G symmetric_form_postcomposeE hF
    sform_polynomial_diagonal_value linearZ.
  reflexivity.
exists Q;split.
- exists G=>x;by rewrite /Q polynomial_from_formsE symmetric_polynomial_value_include.
- split;first by exists v;rewrite hQ.
  by move=>x hx;rewrite hQ hx linear0.
Qed.
