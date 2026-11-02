(** Federer (1969), 1.10.2, p. 45: the divided monomial basis dual to
    products of one-forms. This file proves the divided vector basis;
    identifying its dual with actual products is a separate step. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP GradedComponents LinearBasis BasisRescaling
  SymmetricAlgebra SymmetricGrading SymmetricMultiIndices SymmetricIndexBounds
  SymmetricMonomials SymmetricMonomialBasis SymmetricDividedMonomials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section DividedBasis.
Variable K : fieldType.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.

(** Source for [symmetric_divided_basis_vector]: Federer 1.10.2,
    p. 45, the vector e^alpha/alpha! in the m-th symmetric power,
    with alpha indexed by Xi(n,m). *)
Definition symmetric_divided_basis_vector m (a : symmetric_indices n m) : symmetric_power V m :=
  ((symmetric_multi_factorial (symmetric_indices_unbound a))%:R : K)^-1 *:
    symmetric_finite_monomial e a.

(** Source for [symmetric_divided_basis_vectorE]: Federer 1.10.2,
    p. 45, inclusion in the full algebra gives the divided monomial. *)
Lemma symmetric_divided_basis_vectorE m (a : symmetric_indices n m) :
  component_val (symmetric_divided_basis_vector a) =
    symmetric_divided_monomial e (symmetric_indices_unbound a).
Proof.
rewrite /symmetric_divided_basis_vector linearZ.
change (((symmetric_multi_factorial (symmetric_indices_unbound a))%:R : K)^-1 *:
  component_val (symmetric_finite_monomial e a) =
  symmetric_divided_monomial e (symmetric_indices_unbound a)).
by rewrite /symmetric_finite_monomial symmetric_monomial_componentE.
Qed.

(** Source for [symmetric_divided_basis]: Federer 1.10.2,
    p. 45, the divided monomials form a basis. The factorial
    scalars are nonzero in characteristic zero; n=0 and m=0 are included. *)
Theorem symmetric_divided_basis (h0 : [pchar K] =i pred0) (he : is_basis e) m :
  is_basis (@symmetric_divided_basis_vector m).
Proof.
apply: (@basis_rescaling K (Choice.clone (symmetric_indices n m) _)
  (symmetric_power V m) (@symmetric_finite_monomial K V n e m)
  (symmetric_finite_monomial_basis he m)).
move=> a; rewrite invr_eq0.
exact: (@symmetric_multi_factorial_nonzero K h0).
Qed.
End DividedBasis.
