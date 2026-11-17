(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: an intermediate subring of
    the original finite field extension is a
    subfield. Apply existing algebraicity and
    polynomial inverse-closure results. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingScalarRestriction RingSubmoduleUP CommutativeSubringUP
  CommutativeSubfieldUP CommutativePolynomialSealed CommutativePolynomialEvaluationUP
  CommutativePolynomialEvaluationSealed PolynomialEvaluationImage FiniteFieldModuleAlgebraic
  AlgebraicPolynomialSubfield.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_field_intermediate_ring_subfield]:
    in the original finite algebraic extension,
    adjoining the coordinate classes as a ring
    already supplies their inverses. This supports
    the ring-generation assertion in 3.4.8(8),
    p. 330. No inverse closure is assumed. *)
Theorem finite_field_intermediate_ring_subfield (K L:fieldType) (phi:{rmorphism K->L}) (S:set L):
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType K of ring_restricted_space phi L^o]) ->
  is_commutative_subring S ->(forall a:K,S (phi a)) ->is_commutative_subfield S.
Proof.
move=>hFinite hS hScalars;constructor;first exact:hS.
move=>x hX.
pose B:=CommutativePolynomial.space K.
pose embed:=CommutativePolynomial.embed K.
pose variable:=CommutativePolynomial.variable K.
pose coefficient:=@CommutativePolynomial.coefficient K.
have hB:=CommutativePolynomial.laws K.
pose E:=@CommutativePolynomialEvaluation.map K B L embed variable coefficient hB phi x.
have hE:=@CommutativePolynomialEvaluation.laws K B L embed variable coefficient hB phi x.
have hAlgebraic:=@finite_field_module_annihilating_polynomial K B L embed variable coefficient hB phi hFinite x E hE.
have hField:=@algebraic_polynomial_image_subfield K B L embed variable coefficient hB phi x E hE hAlgebraic.
have hImage:=@polynomial_evaluation_image_generated K B L embed variable coefficient hB phi x E hE.
have hGenerators:(fun y:L=>y = x \/exists a:K,y = phi a) `<=` S.
  move=>y [->|[a ->]];[exact:hX|exact:hScalars a].
have hContained:=generated_commutative_subring_minimal hImage hS hGenerators.
apply:hContained;apply:(@commutative_subfield_inverse L (fun y:L=>exists P:B,y = E P) hField).
exists variable;exact:esym (polynomial_evaluation_variable hE).
Qed.
