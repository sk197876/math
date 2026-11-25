(** Federer (1969), 3.4.8(10), p. 331:
    all required original quotient fractions
    have bounded polynomial representatives with
    one original denominator. Reuse the
    pointwise representative theorem and uniform
    denominator theorem in the actual field. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeDomainUP CommutativeIdealUP CommutativeFieldKernel
  CommutativeSubringUP FractionFieldUP CoefficientFractionFieldUP CommutativePolynomialUP
  CommutativePolynomialMonicUP CommutativePolynomialEvaluationUP PrimitiveFieldBoundedRepresentative
  UniformOriginalPolynomialDenominator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [primitive_field_uniform_original_representatives]:
    the common delta and original coefficient
    module in 3.4.8(10), p. 331.
    The field family may include the
    inverse of the original polynomial derivative
    and the remaining coordinate classes.
    No individual denominator or numerator is
    fixed in the theorem's hypotheses. *)
Theorem primitive_field_uniform_original_representatives (A B:comNzRingType) (L M:fieldType)
  (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (hDomain:is_commutative_integral_domain A)
  (chi:{rmorphism A->L}) (eta:{rmorphism A->M}) (phi:{rmorphism M->L})
  (z:L) (E:{rmorphism B->L}) (W:B) k:
  is_coefficient_fraction_field chi eta phi ->is_commutative_fraction_field eta ->
  is_commutative_polynomial_evaluation embed variable chi z E ->
  is_generated_commutative_subring (fun y:L=>y = z \/exists a:M,y = phi a) setT ->
  is_monic_polynomial coefficient W k ->E W = 0 ->forall N (x:'I_N->L),
  exists delta:A,eta delta<>0 /\forall i:'I_N,exists P:B,
    (forall j,(k<=j)%N ->coefficient P j = 0) /\chi delta*x i = E P.
Proof.
move=>hCoefficient hField hE hGenerated hW hZero N x.
have hEach i:=@primitive_field_original_bounded_representative A B L M embed variable coefficient
  hP hDomain chi eta phi z E W k hCoefficient hE hGenerated hW hZero (x i).
have [d hD]:=choice hEach.
have [T hT]:=choice hD.
pose zero:set L:=fun a:L=>a = 0.
pose identity:{rmorphism L->L}:=GRing.RMorphism.clone L L idfun _.
have hZeroIdeal:is_commutative_ideal zero:=commutative_ring_kernel_ideal identity.
have hNonzero i:eta (d i)<>0:=(hT i).1.
have hSupport i j (hJ:(k<=j)%N):coefficient (T i) j = 0:=(hT i).2.1 j hJ.
have hRelations i:zero (chi (d i)*x i-E (T i)).
  by rewrite /zero (hT i).2.2 subrr.
have [delta [hDelta hRepresentatives]]:=@uniform_original_polynomial_denominator A B L M
  embed variable coefficient hP chi z E eta hField hDomain zero N k d T x
  hZeroIdeal hE hNonzero hSupport hRelations.
exists delta;split;first exact:hDelta.
move=>i;have [P [hBound hRelation]]:=hRepresentatives i.
exists P;split;first exact:hBound.
exact:subr0_eq hRelation.
Qed.
