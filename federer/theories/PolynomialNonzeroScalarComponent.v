(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: a nonzero vector-valued polynomial
    has a nonzero scalar polynomial component.
    Apply the separating functional of 1.5.1
    and polynomial postcomposition of 1.10.4. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom PairingSeparation PolynomialFunctions PolynomialLinearComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_nonzero_scalar_component]: extract
    a scalar equation from a nonzero
    power determinant for 3.4.8(8), p. 330.
    Its target may have arbitrary dimension;
    the functional is an existence witness. *)
Theorem polynomial_nonzero_scalar_component (K:fieldType) (X Y:lmodType K)
  (P:PolynomialFunction X Y) (w:X):
  P w<>0 ->exists Q:PolynomialFunction X K^o,
    Q w = 1 /\forall v:X,P v = 0 ->Q v = 0.
Proof.
move=>hNonzero.
have hN:P w!=0 by apply/eqP;exact:hNonzero.
have [f hF]:=@nonzero_functional K Y (P w) hN.
have hPolynomial:=elimT (asboolP _) (polynomial_function_proof P).
have hQ:=@polynomial_linear_postcompose K X Y K^o (hom_as_linear f) P hPolynomial.
exists (@PolynomialMap K X K^o _ (introT (asboolP _) hQ));split;first exact:hF.
move=>v hZero;change (hom_as_linear f (P v) = 0);by rewrite hZero linear0.
Qed.
