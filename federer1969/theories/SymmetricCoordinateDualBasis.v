(** Federer (1969), 1.10.2, p. 45: the dual basis to e^alpha/alpha!. This
    file establishes the normalized coordinate basis; its identification
    with the actual products omega^alpha is separate. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP GradedAlgebra GradedComponents Hom HomogeneousHom
  BoundedHom LinearBasis FiniteDualDimension SymmetricAlgebra SymmetricGrading
  SymmetricMultiIndices SymmetricIndexBounds SymmetricMonomialBasis SymmetricDividedBasis
  SymmetricForms SymmetricFormExtension SymmetricFormIsomorphism SymmetricFormSum
  SymmetricPairing SymmetricMonomialCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_indices_unbound_injective]: Federer
    1.10.2, p. 45, supporting identification of the finite Xi(n,m)
    indices: forgetting redundant coordinate bounds remains injective. *)
Lemma symmetric_indices_unbound_injective n m : injective (@symmetric_indices_unbound n m).
Proof.
move=> a b hab; apply: (can_inj (@symmetric_indices_forgetK n m)).
apply: val_inj; exact: hab.
Qed.

Section DualBasis.
Variable K : fieldType.
Hypothesis h0 : [pchar K] =i pred0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable m : nat.
Local Notation I := (Finite.clone (symmetric_indices n m) _).
Local Notation P := (symmetric_power V m).
Local Notation M := (symmetric_coordinate_full_form he).
Local Notation d := (@symmetric_divided_basis_vector K V n e m).
Local Notation hd := (symmetric_divided_basis h0 he m).

(** Source for [symmetric_coordinate_basis_form]: Federer
    1.10.2, p. 45, normalized dual coordinates indexed by Xi(n,m),
    now regarded as forms of the fixed degree m. *)
Definition symmetric_coordinate_basis_form (a : symmetric_indices n m) : S_m V K^o m :=
  sform_component m (M (symmetric_indices_unbound a)).

(** Source for [symmetric_coordinate_basis_include]: Federer
    1.10.2, p. 45, inclusion of the fixed-degree coordinate recovers
    its full homogeneous map because its exponent sum is m. *)
Lemma symmetric_coordinate_basis_include a :
  sform_include (symmetric_coordinate_basis_form a) = M (symmetric_indices_unbound a).
Proof.
rewrite /symmetric_coordinate_basis_form sform_componentK.
have h := symmetric_coordinate_full_form_graded he (symmetric_indices_unbound a).
by rewrite symmetric_indices_unbound_degree in h.
Qed.

(** Source for [symmetric_coordinate_basis_pairing]: Federer
    1.10.2, p. 45, the normalized coordinate forms and divided
    monomial vectors have the Kronecker pairing. *)
Lemma symmetric_coordinate_basis_pairing a b :
  symmetric_pairing (d b) (symmetric_coordinate_basis_form a) = if b == a then 1 else 0.
Proof.
change (sform_include (symmetric_coordinate_basis_form a) (component_val (d b)) =
  if b == a then 1 else 0).
rewrite symmetric_coordinate_basis_include symmetric_divided_basis_vectorE
  (@symmetric_coordinate_divided_monomial K V n e he h0).
by rewrite (inj_eq (@symmetric_indices_unbound_injective n m)).
Qed.

(** Source for [symmetric_coordinate_basis_to_hom]: Federer
    1.10.2, p. 45, the forms correspond exactly to the dual
    linear basis of the divided monomial basis under 1.10.1's isomorphism. *)
Lemma symmetric_coordinate_basis_to_hom a :
  sform_to_hom (symmetric_coordinate_basis_form a) = @dual_basis K I P d hd a.
Proof.
apply: hom_ext=> x.
apply: (basis_linear_ext hd
  (hom_as_linear (sform_to_hom (symmetric_coordinate_basis_form a)))
  (hom_as_linear (@dual_basis K I P d hd a))) x=> b.
change (symmetric_pairing (d b) (symmetric_coordinate_basis_form a) =
  dual_basis hd a (d b)).
by rewrite symmetric_coordinate_basis_pairing dual_basisE.
Qed.

(** Source for [symmetric_coordinate_basis]: Federer 1.10.2,
    p. 45, supporting basis result: the normalized coordinate forms
    constitute a basis, by the dual-basis theorem and the proved linear
    form-Hom isomorphism. Actual products are identified separately. *)
Theorem symmetric_coordinate_basis : is_basis symmetric_coordinate_basis_form.
Proof.
have hb := basis_transport (@hom_to_sformK K V K^o m)
  (@sform_to_homK K V K^o m) (@dual_basisP K I P d hd).
apply: basis_congr _ hb=> a.
change (hom_to_sform (@dual_basis K I P d hd a) = symmetric_coordinate_basis_form a).
by rewrite -symmetric_coordinate_basis_to_hom sform_to_homK.
Qed.
End DualBasis.

Arguments symmetric_coordinate_basis_form {K V n e} he m a.
