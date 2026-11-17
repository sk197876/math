(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: a finite family has a
    primitive linear combination with coefficients in
    the original characteristic-zero scalar subfield.
    Apply the binary theorem and the existing
    least-subring characterisation of polynomial images. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import InfiniteSequence RingScalarRestriction RingSubmoduleUP
  CommutativePolynomialUP CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationSealed
  PolynomialEvaluationImageContainment FiniteFieldPrimitiveSubfieldPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_field_primitive_subfield_family]:
    the finite-generator form of the classical
    primitive-element theorem invoked in 3.4.8(8),
    p. 330; compare Bourbaki (1990), Chapter V,
    section 7, no. 4, Theorem 1,
    pp. V.40–41. The selected coefficients remain
    in the original scalar subfield; the empty
    family gives the original zero element. *)
Theorem finite_field_primitive_subfield_family (U K L:fieldType) (B:comNzRingType)
  (eta:{rmorphism U->K}) (embed:{rmorphism K->B}) (variable:B) (coefficient:B->nat->K)
  (hP:is_commutative_polynomial_ring embed variable coefficient) (phi:{rmorphism K->L}):
  [pchar U] =i pred0 ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType K of ring_restricted_space phi L^o]) ->
  forall n (x:'I_n->L),exists (c:'I_n->U) (E:{rmorphism B->L}),
    is_commutative_polynomial_evaluation embed variable phi
      (\sum_i phi (eta (c i))*x i) E /\
    forall i:'I_n,exists P:B,x i = E P.
Proof.
move=>hCharacteristic hFinite;elim=>[|n ih] x.
- pose c:=fun _: 'I_0=>(0:U).
  pose E:=@CommutativePolynomialEvaluation.map K B L embed variable coefficient hP phi 0.
  have hE:=@CommutativePolynomialEvaluation.laws K B L embed variable coefficient hP phi 0.
  exists c,E;split;first by rewrite big_ord0.
  move=>i;by have h:=ltn_ord i;rewrite ltn0 in h.
- pose prefix:=fun i:'I_n=>x (widen_ord (leqnSn n) i).
  have [c0 [E0 [hE0 hOld]]]:=ih prefix.
  pose z0:=\sum_i phi (eta (c0 i))*prefix i.
  have [t [E [PA [PB [hE [hA hB]]]]]]:=
    @finite_field_primitive_subfield_pair U K L B eta embed variable coefficient hP phi
      hCharacteristic hFinite z0 (x ord_max).
  pose c:=ordinal_snoc c0 t.
  have hSum:(\sum_i phi (eta (c i))*x i) = z0+phi (eta t)*x ord_max.
    rewrite big_ord_recr /c ordinal_snoc_last.
    congr (_+_);apply:eq_bigr=>i _;by rewrite ordinal_snoc_before.
  exists c,E;split;first by rewrite hSum.
  move=>i;case:(unliftP ord_max i)=>[j ->|->];last by exists PB.
  have hLift:widen_ord (leqnSn n) j = lift ord_max j.
    by apply:val_inj;exact:esym (lift_max j).
  rewrite -hLift;have [P hP0]:=hOld j.
  have [Q hQ]:=@polynomial_evaluation_image_containment K B L embed variable coefficient hP phi
    z0 (z0+phi (eta t)*x ord_max) E0 E hE0 hE (ex_intro _ PA hA) P.
  exists Q;exact:etrans hP0 hQ.
Qed.
