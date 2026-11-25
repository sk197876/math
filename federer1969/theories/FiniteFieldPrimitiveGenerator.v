(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: if the original finite family
    generates the extension as a ring, its
    primitive combination has the whole extension
    as its original polynomial image. Reuse
    the existing least-subring laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingScalarRestriction RingSubmoduleUP CommutativeSubringUP
  CommutativePolynomialUP CommutativePolynomialEvaluationUP PolynomialEvaluationImage
  FiniteFieldPrimitiveFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_field_primitive_subfield_generator]:
    the original extension is the ring generated
    by M and one real linear combination,
    the existence part of the simplicity assertion
    invoked in 3.4.8(8), p. 330. This
    theorem retains an arbitrary characteristic-zero
    scalar subfield; no image conclusion is assumed. *)
Theorem finite_field_primitive_subfield_generator (U K L:fieldType) (B:comNzRingType)
  (eta:{rmorphism U->K}) (embed:{rmorphism K->B}) (variable:B) (coefficient:B->nat->K)
  (hP:is_commutative_polynomial_ring embed variable coefficient) (phi:{rmorphism K->L}) n (x:'I_n->L):
  [pchar U] =i pred0 ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType K of ring_restricted_space phi L^o]) ->
  is_generated_commutative_subring
    (fun y:L=>(exists i:'I_n,y = x i) \/exists a:K,y = phi a) setT ->
  exists (c:'I_n->U) (E:{rmorphism B->L}),
    is_commutative_polynomial_evaluation embed variable phi
      (\sum_i phi (eta (c i))*x i) E /\(forall y:L,exists P:B,E P = y).
Proof.
move=>hCharacteristic hFinite hGenerated.
have [c [E [hE hFamily]]]:=@finite_field_primitive_subfield_family U K L B eta embed variable coefficient hP phi
  hCharacteristic hFinite n x.
have hImage:=@polynomial_evaluation_image_generated K B L embed variable coefficient hP phi
  (\sum_i phi (eta (c i))*x i) E hE.
have hGenerators:(fun y:L=>(exists i:'I_n,y = x i) \/exists a:K,y = phi a) `<=`
    (fun y:L=>exists P:B,y = E P).
  move=>y [[i ->]|[a ->]];first exact:hFamily i.
  exists (embed a);exact:esym (polynomial_evaluation_constants hE a).
have hAll:=generated_commutative_subring_minimal hGenerated
  (generated_commutative_subring_laws hImage) hGenerators.
exists c,E;split;first exact:hE.
move=>y;have [P hP0]:=hAll y I;exists P;exact:esym hP0.
Qed.
