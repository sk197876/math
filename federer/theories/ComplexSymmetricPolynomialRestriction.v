(** Federer (1969), 3.4.12, pp. 338–339:
    the polynomial of an original complex symmetric form
    equals the polynomial of its real restriction.
    This exposes the value connection for supplied forms,
    preserving the exact factorial normalization of 1.10.4, p. 46. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import ScalarRestriction ComplexScalarSealed SymmetricForms
  HomogeneousPolynomialFunctions PolynomialDiagonalNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_symmetric_polynomial_real_value]: the
    original homogeneous function is independent of real
    or complex presentation of the same symmetric coefficient,
    supporting 3.4.12, pp. 338–339. *)
Theorem complex_symmetric_polynomial_real_value (R:realFieldType)
    (X Y:lmodType (ComplexScalars.C R)) m (F:S_m X Y m)
    (G:S_m (restricted_space (ComplexScalars.embed R) X)
      (restricted_space (ComplexScalars.embed R) Y) m):
  (forall t,G t=F t) ->forall x,
    @sform_polynomial_value R (restricted_space (ComplexScalars.embed R) X)
      (restricted_space (ComplexScalars.embed R) Y) m G x=
    @sform_polynomial_value (ComplexScalars.C R) X Y m F x.
Proof.
move=>hValues x;rewrite !sform_polynomial_diagonal_value hValues.
change (ComplexScalars.embed R (((m`!)%:R:R)^-1)*:F [tuple x | i<m]=
  ((m`!)%:R:ComplexScalars.C R)^-1*:F [tuple x | i<m]).
by rewrite fmorphV rmorph_nat.
Qed.
