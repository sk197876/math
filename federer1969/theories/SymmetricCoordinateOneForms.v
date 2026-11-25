(** Federer (1969), 1.10.2, p. 45: identify the degree-one monomial
    coordinates with the given dual one-forms. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP GradedAlgebra GradedComponents Hom LinearBasis
  SymmetricAlgebra SymmetricGrading SymmetricLowPowers SymmetricMultiIndices
  SymmetricIndexBounds SymmetricDividedMonomials SymmetricDividedBasis
  SymmetricUnitMultiIndices SymmetricForms SymmetricFormIsomorphism SymmetricFormSum
  SymmetricPairing SymmetricMonomialCoordinates SymmetricCoordinateDualBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_unit_index_injective]: Federer 1.10.2,
    p. 45, supporting distinctness of the degree-one coordinate indices. *)
Lemma symmetric_unit_index_injective n : injective (@symmetric_unit_index n).
Proof.
move=> i j h; apply: symmetric_multi_unit_injective.
have hh := congr1 (@symmetric_indices_unbound n 1) h.
by rewrite !symmetric_unit_indexE in hh.
Qed.

(** Source for [symmetric_unit_basis_vector]: Federer 1.10.2,
    p. 45, the divided unit-exponent basis vector is the original
    basis vector under the degree-one identification of 1.9.1. *)
Lemma symmetric_unit_basis_vector (K : fieldType) (V : lmodType K)
    n (e : 'I_n -> V) i :
  symmetric_divided_basis_vector e (symmetric_unit_index i) = symmetric_first_inclusion V (e i).
Proof.
apply: val_inj.
change (component_val (symmetric_divided_basis_vector e (symmetric_unit_index i)) =
  component_val (symmetric_first_inclusion V (e i))).
rewrite symmetric_divided_basis_vectorE symmetric_unit_indexE
  /symmetric_divided_monomial symmetric_multi_unit_factorial invr1 scale1r symmetric_monomial_unit.
symmetry; change (grade (symmetric_grading V) 1 (symmetric_generator (e i)) = symmetric_generator (e i)).
exact: symmetric_generator_homogeneous.
Qed.

Section DualOneForms.
Variable K : fieldType.
Hypothesis h0 : [pchar K] =i pred0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable omega : 'I_n -> S_m V K^o 1.
Hypothesis hd : forall i j,
  symmetric_pairing (symmetric_first_inclusion V (e j)) (omega i) = if j == i then 1 else 0.

(** Source for [symmetric_coordinate_one_form]: Federer 1.10.2,
    p. 45, the normalized coordinate at the i-th unit exponent equals
    the given dual one-form omega_i, not merely an unspecified dual map. *)
Lemma symmetric_coordinate_one_form i :
  symmetric_coordinate_basis_form he 1 (symmetric_unit_index i) = omega i.
Proof.
apply: (can_inj (@sform_to_homK K V K^o 1)); apply: hom_ext=> x.
have hb := basis_transport (@symmetric_first_inclusionK K V)
  (@symmetric_first_inverseK K V) he.
apply: (basis_linear_ext hb
  (hom_as_linear (sform_to_hom (symmetric_coordinate_basis_form he 1 (symmetric_unit_index i))))
  (hom_as_linear (sform_to_hom (omega i)))) x=> j.
change (symmetric_pairing (symmetric_first_inclusion V (e j))
  (symmetric_coordinate_basis_form he 1 (symmetric_unit_index i)) =
  symmetric_pairing (symmetric_first_inclusion V (e j)) (omega i)).
by rewrite hd -(symmetric_unit_basis_vector e j)
  (symmetric_coordinate_basis_pairing h0) (inj_eq (@symmetric_unit_index_injective n)).
Qed.

(** Source for [symmetric_coordinate_one_form_include]: Federer
    1.10.2, p. 45, the full normalized coordinate is precisely the
    inclusion of the given one-form into the graded algebra. *)
Lemma symmetric_coordinate_one_form_include i :
  sform_include (omega i) = symmetric_coordinate_full_form he (symmetric_multi_unit i).
Proof.
rewrite -(symmetric_coordinate_one_form i) symmetric_coordinate_basis_include.
by rewrite symmetric_unit_indexE.
Qed.
End DualOneForms.
