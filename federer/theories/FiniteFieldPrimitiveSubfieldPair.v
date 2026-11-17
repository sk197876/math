(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: choose the primitive-element slope
    in the original characteristic-zero subfield,
    in particular in the original real scalars. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingScalarRestriction RingSubmoduleUP CommutativePolynomialUP
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationSealed
  PrimitiveElementSlopeSeparation FiniteFieldPrimitivePair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_field_primitive_subfield_pair]: the
    finite excluded slope list may be avoided
    in the original infinite scalar subfield,
    retaining real coefficients for 3.4.8(8), p. 330.
    Apply the binary theorem and the existing
    finite-list avoidance result directly. *)
Theorem finite_field_primitive_subfield_pair (U K L:fieldType) (B:comNzRingType)
  (eta:{rmorphism U->K}) (embed:{rmorphism K->B}) (variable:B) (coefficient:B->nat->K)
  (hP:is_commutative_polynomial_ring embed variable coefficient) (phi:{rmorphism K->L}):
  [pchar U] =i pred0 ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType K of ring_restricted_space phi L^o]) ->
  forall a b:L,exists (t:U) (Ez:{rmorphism B->L}) (PA PB:B),
    is_commutative_polynomial_evaluation embed variable phi (a+phi (eta t)*b) Ez /\
    a = Ez PA /\b = Ez PB.
Proof.
move=>hCharacteristic hFinite a b.
have hK:[pchar K] =i pred0 by move=>p;rewrite (fmorph_pchar eta) hCharacteristic.
have [T [psi [bad hGood]]]:=@finite_field_primitive_pair_except_finite_slopes K L B
  embed variable coefficient hP phi hK hFinite a b.
pose kappa:{rmorphism U->T}:=GRing.RMorphism.clone U T ((psi \o phi) \o eta) _.
have [t hT]:=@characteristic_zero_scalar_avoids_list U T kappa bad hCharacteristic.
pose Ez:=@CommutativePolynomialEvaluation.map K B L embed variable coefficient hP phi (a+phi (eta t)*b).
have hEz:=@CommutativePolynomialEvaluation.laws K B L embed variable coefficient hP phi (a+phi (eta t)*b).
have [PA [PB hValues]]:=hGood (eta t) hT Ez hEz.
exists t,Ez,PA,PB;by split.
Qed.
