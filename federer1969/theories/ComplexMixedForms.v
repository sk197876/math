(** Federer (1969), 1.6.6, p. 27: the mixed complex basis and its purely
    complex part. An increasing selection from the ordered family
    alpha_1,...,alpha_n,bar(alpha_1),...,bar(alpha_n) indexes exactly one
    mixed product, with all unbarred factors first. Source context are
    recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates ScalarRestriction ComplexScalarSealed
  ComplexCharacteristic ComplexValuedForms ComplexFormSubspace ComplexProductBasis
  ComplexOrderedBases ComplexOneFormBasis ComplexFormWords CovectorProducts
  GrassmannCoordinates FiniteBasisComparison FiniteIndependence Annihilator
  OneFormIdentification FiniteExteriorPowers FiniteBasisCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Mixed.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation hR := (real_two_nonzero R).
Local Notation hC := (complex_two_nonzero R).
Variable V : lmodType C.
Local Notation VR := (restricted_space embed V).
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.

(** Source for [mixed_complex_form]: Federer 1.6.6, p. 27,
    alpha_lambda wedge bar(alpha_mu), for all p+q=m. A single
    increasing selection in 2n indices records the same two blocks. *)
Definition mixed_complex_form m (l : Lambda (n+n) m) :=
  complex_values_lambda hR (ordered_mixed_one_form he) l.

(** Source for [mixed_complex_form_basis]: Federer 1.6.6,
    p. 27, mixed basis of A^m(V,C). Every degree has the asserted
    complex basis, with the empty selection furnishing degree zero. *)
Theorem mixed_complex_form_basis m : is_basis (@mixed_complex_form m).
Proof.
exact: (@complex_product_basis R hR VR (n+n) (ordered_real_basis e)
  (ordered_real_basisP he) (ordered_mixed_one_form he) (ordered_mixed_one_form_basisP he) m).
Qed.

(** Source for [holomorphic_basis_form]: Federer 1.6.6,
    p. 27, the special case p=m and q=0. The complex alternating
    products of the complex dual basis, before inclusion in real forms. *)
Definition holomorphic_basis_form m (l : Lambda n m) : A_m V C^o m :=
  omega_lambda hC (fun j => one_form (dual_basis he j)) l.

(** Source for [holomorphic_basis_formP]: Federer 1.6.6,
    p. 27, basis of A_C^m V. This is the ordinary exterior dual basis
    over C, with all degrees covered. *)
Lemma holomorphic_basis_formP m : is_basis (@holomorphic_basis_form m).
Proof.
apply: (@omega_lambda_basis C hC V n m e (fun j => one_form (dual_basis he j)) he).
by move=> i j; rewrite one_formE dual_basisE eq_sym.
Qed.

(** Source for [unbarred_complex_form]: Federer 1.6.6,
    p. 27, p=m and q=0. The unbarred product viewed as a
    complex-valued real form. *)
Definition unbarred_complex_form m (l : Lambda n m) :=
  complex_form_inclusion embed (holomorphic_basis_form l).

(** Source for [unbarred_complex_form_independent]: Federer
    1.6.6, p. 27, complex basis of A_C^m V. Its unbarred
    products are independent over C in the ambient real form space. *)
Lemma unbarred_complex_form_independent m : finite_independent (@unbarred_complex_form m).
Proof.
exact: (finite_independent_map (@complex_form_inclusion_injective R C embed V C^o m)
  (finite_basis_independent (holomorphic_basis_formP m))).
Qed.

(** Source for [unbarred_complex_form_spanning]: Federer
    1.6.6, p. 27, complex basis of A_C^m V. Precisely the
    complex-multilinear real forms are spanned by the unbarred products. *)
Theorem unbarred_complex_form_spanning m (a : complex_valued_form embed VR C^o m) :
  complex_form_subspace embed V C^o m a ->
  exists c : Lambda n m -> C, a = \sum_l c l *: unbarred_complex_form l.
Proof.
move=> /complex_form_subspace_image [b <-].
exists (fun l => dual_basis (holomorphic_basis_formP m) l b).
have hb : b = \sum_l (dual_basis (holomorphic_basis_formP m) l b : C) *: holomorphic_basis_form l.
  rewrite -{1}(basis_coordinatesK (holomorphic_basis_formP m) b) basis_synthesis_finiteE.
  apply: eq_bigr => l _; by [].
rewrite {1}hb linear_sum.
apply: eq_bigr => l _; exact: linearZ.
Qed.
End Mixed.
