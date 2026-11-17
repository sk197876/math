(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: extending original coefficients
    commutes with formal differentiation. Reuse the
    independent coefficient-map and derivative equations.
    Source: Bourbaki, Algebra II (1990), Chapter V,
    section 7, no. 2, Proposition 3, pp. V.37–38. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import PolynomialCoefficientMapUP FormalPolynomialDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [formal_polynomial_derivative_coefficient_extension]:
    the original formal derivative is preserved by
    coefficient extension, supporting the simple-root
    criterion in the cited Proposition 3 and
    the simplicity argument of 3.4.8(8), pp. 329–330. *)
Theorem formal_polynomial_derivative_coefficient_extension (A C:comNzRingType)
  (B D:Type) (source:B->nat->A) (target:D->nat->C)
  (phi:{rmorphism A->C}) (M:B->D):
  is_polynomial_coefficient_map source target phi M ->forall P DP:B,
  is_formal_polynomial_derivative source P DP ->
  is_formal_polynomial_derivative target (M P) (M DP).
Proof.
move=>hM P DP hDerivative i.
by rewrite hM hDerivative rmorphM rmorph_nat -hM.
Qed.
