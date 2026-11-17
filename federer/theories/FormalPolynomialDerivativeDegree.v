(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: in characteristic zero the formal
    derivative lowers positive degree by exactly one.
    Use its independent coefficients and existing field
    arithmetic. Source: Bourbaki, Algebra II (1990),
    Chapter IV, section 2, no. 2, pp. IV.17–18. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativePolynomialDegreeUP FormalPolynomialDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [formal_polynomial_derivative_degree]: the
    original positive-degree derivative is nonzero
    in characteristic zero, supporting the separability
    criterion of Bourbaki (1990), Chapter V,
    section 7, no. 2, Proposition 3,
    pp. V.37–38, used for 3.4.8(8), pp. 329–330. *)
Theorem formal_polynomial_derivative_degree (K:fieldType) (B:Type)
  (coefficient:B->nat->K) (P D:B) d:
  [pchar K] =i pred0 ->is_polynomial_degree coefficient P d.+1 ->
  is_formal_polynomial_derivative coefficient P D ->is_polynomial_degree coefficient D d.
Proof.
move=>/pcharf0P hCharacteristic hDegree hDerivative;split.
- have hNat:(d.+1%:R:K)!=0 by rewrite hCharacteristic.
  apply/eqP;rewrite hDerivative mulf_eq0 negb_or hNat /=.
  by apply/eqP;exact:hDegree.1.
- move=>i hi;rewrite hDerivative.
  have hHigher:(d.+1<i.+1)%N by rewrite ltnS.
  by rewrite hDegree.2 // mulr0.
Qed.
