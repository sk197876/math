(** Federer (1969), 1.10.2, p. 45: the stated dual monomial basis theorem.
    The one-form products here use the symmetric multiplication itself; the
    supporting coordinate results identify, rather than replace, them. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Graded LinearBasis SymmetricAlgebra SymmetricGrading
  SymmetricLowPowers SymmetricMultiIndices SymmetricIndexBounds SymmetricDividedBasis
  SymmetricForms SymmetricFormSum SymmetricPairing SymmetricMonomialCoordinates
  SymmetricCoordinateDualBasis SymmetricDualMonomialProducts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section DualMonomials.
Variable K : fieldType.
Variable V : lmodType K.
Variable n : nat.
Variable omega : 'I_n -> S_m V K^o 1.

(** Source for [symmetric_dual_monomial]: Federer 1.10.2,
    p. 45, the actual product omega^alpha in the fixed degree m,
    for alpha in Xi(n,m). *)
Definition symmetric_dual_monomial m (a : symmetric_indices n m) : S_m V K^o m :=
  sform_component m (symmetric_one_form_monomial omega (symmetric_indices_unbound a)).

Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Hypothesis h0 : [pchar K] =i pred0.
Hypothesis hd : forall i j,
  symmetric_pairing (symmetric_first_inclusion V (e j)) (omega i) = if j == i then 1 else 0.

(** Source for [symmetric_dual_monomial_include]: Federer 1.10.2,
    p. 45, its inclusion in the full graded algebra is precisely
    the iterated product, since its exponent sum is m. *)
Lemma symmetric_dual_monomial_include m (a : symmetric_indices n m) :
  sform_include (symmetric_dual_monomial a) =
    symmetric_one_form_monomial omega (symmetric_indices_unbound a).
Proof.
rewrite /symmetric_dual_monomial sform_componentK.
have h := symmetric_one_form_monomial_graded he h0 hd (symmetric_indices_unbound a).
by rewrite symmetric_indices_unbound_degree in h.
Qed.

(** Source for [symmetric_dual_monomial_coordinate]: Federer
    1.10.2, p. 45, the product agrees with the normalized
    coordinate form at the same finite exponent index. *)
Lemma symmetric_dual_monomial_coordinate m (a : symmetric_indices n m) :
  symmetric_dual_monomial a = symmetric_coordinate_basis_form he m a.
Proof.
by rewrite /symmetric_dual_monomial (symmetric_one_form_monomial_coordinate he h0 hd).
Qed.

(** Source for [symmetric_dual_monomial_pairing]: Federer 1.10.2,
    p. 45, the displayed dual-basis assertion: the pairing of
    e^beta/beta! with omega^alpha is one for beta=alpha and zero otherwise. *)
Theorem symmetric_dual_monomial_pairing m (a b : symmetric_indices n m) :
  symmetric_pairing (symmetric_divided_basis_vector e b) (symmetric_dual_monomial a) =
    if b == a then 1 else 0.
Proof. rewrite symmetric_dual_monomial_coordinate; exact (@symmetric_coordinate_basis_pairing K h0 V n e he m a b). Qed.

(** Source for [symmetric_dual_monomial_basis]: Federer 1.10.2,
    p. 45, the products omega^alpha, alpha in Xi(n,m), form
    a basis of scalar-valued symmetric m-forms dual to the divided
    monomial vector basis. Zero ambient dimension and degree zero are included. *)
Theorem symmetric_dual_monomial_basis m : is_basis (@symmetric_dual_monomial m).
Proof.
apply: basis_congr _ (symmetric_coordinate_basis h0 he m)=> a.
symmetry; exact: symmetric_dual_monomial_coordinate.
Qed.
End DualMonomials.
