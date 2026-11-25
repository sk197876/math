(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: original coefficient extension through
    the simple field agrees with extension through
    the ambient field. Reuse coefficient uniqueness,
    field-map injectivity and derivative extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativeFactorizationUP CommutativePolynomialUP
  PolynomialCoefficientMapUP PolynomialCoefficientMapLaws FormalPolynomialDerivativeUP
  FormalPolynomialDerivativeExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Square.
Variables K L F T:fieldType.
Variable phi:{rmorphism K->L}.
Variable inclusion:{rmorphism F->L}.
Variable scalar:{rmorphism K->F}.
Variable psi:{rmorphism L->T}.
Hypothesis hTriangle:forall a:K,inclusion (scalar a) = phi a.
Local Notation rho:=(GRing.RMorphism.clone F T (psi \o inclusion) _).
Variables B C O D:comNzRingType.
Variable embedK:{rmorphism K->B}.
Variable variableK:B.
Variable source:B->nat->K.
Hypothesis hB:is_commutative_polynomial_ring embedK variableK source.
Variable embedF:{rmorphism F->C}.
Variable variableF:C.
Variable middle:C->nat->F.
Hypothesis hC:is_commutative_polynomial_ring embedF variableF middle.
Variable embedL:{rmorphism L->O}.
Variable variableL:O.
Variable original:O->nat->L.
Hypothesis hO:is_commutative_polynomial_ring embedL variableL original.
Variable embedT:{rmorphism T->D}.
Variable variableT:D.
Variable target:D->nat->T.
Hypothesis hD:is_commutative_polynomial_ring embedT variableT target.
Variable MF:{rmorphism B->C}.
Hypothesis hMF:is_polynomial_coefficient_map source middle scalar MF.
Variable N:{rmorphism C->D}.
Hypothesis hN:is_polynomial_coefficient_map middle target rho N.
Variable M0:{rmorphism B->O}.
Hypothesis hM0:is_polynomial_coefficient_map source original phi M0.
Variable M1:{rmorphism O->D}.
Hypothesis hM1:is_polynomial_coefficient_map original target psi M1.

(** Source for [primitive_pair_coefficient_square]: the
    original coefficient square commutes, supporting
    the primitive-element comparison in 3.4.8(8),
    p. 330. Apply existing polynomial coefficient
    uniqueness to the original scalar triangle. *)
Theorem primitive_pair_coefficient_square (P:B):N (MF P) = M1 (M0 P).
Proof.
apply:(@polynomial_coefficients_unique T D embedT variableT target hD)=>i.
rewrite hN hMF hM1 hM0.
change (psi (inclusion (scalar (source P i))) = psi (phi (source P i))).
by rewrite hTriangle.
Qed.

(** Source for [primitive_pair_second_divides_split_product]:
    the original second polynomial divides the
    split product of the original pair,
    supporting the root comparison in 3.4.8(8), p. 330. *)
Lemma primitive_pair_second_divides_split_product (f g:B):
  commutative_divides (N (MF g)) (M1 (M0 (f*g))).
Proof.
exists (N (MF f)).
by rewrite -primitive_pair_coefficient_square !rmorphM.
Qed.

(** Source for [primitive_pair_second_nonzero]: the
    original nonzero polynomial remains nonzero
    in the containing field, supporting the
    gcd comparison in 3.4.8(8), p. 330. *)
Lemma primitive_pair_second_nonzero (g:B):g<>0 ->N (MF g)<>0.
Proof.
move=>hG hZero.
have hMFInjective:=@polynomial_coefficient_map_injective K B F C embedK variableK source middle
  hB scalar MF hMF (fmorph_inj scalar).
have hNInjective:=@polynomial_coefficient_map_injective F C T D embedF variableF middle target
  hC rho N hN (fmorph_inj rho).
apply:hG;apply:hMFInjective;apply:hNInjective;by rewrite hZero !rmorph0.
Qed.

(** Source for [primitive_pair_second_derivative_extension]:
    the original formal derivative is unchanged
    by the two coefficient extensions, supporting
    the simple-root comparison in 3.4.8(8), p. 330. *)
Lemma primitive_pair_second_derivative_extension (g dg:B):
  is_formal_polynomial_derivative source g dg ->
  is_formal_polynomial_derivative target (N (MF g)) (N (MF dg)).
Proof.
move=>hDerivative.
apply:(@formal_polynomial_derivative_coefficient_extension F T C D middle target rho N hN).
exact:(@formal_polynomial_derivative_coefficient_extension K F B C source middle scalar MF hMF g dg hDerivative).
Qed.
End Square.
