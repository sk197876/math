(** Federer (1969), 1.6.6, p. 27: the orientation of a complex plane is
    independent of its complex basis. Nonzero paired products spanning the
    same plane differ by a positive scalar, proved by the complex
    change-of-basis automorphism and its real determinant. Source context
    are recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors SubspaceCarrier BasisInSubspace
  ComplexScalarSealed ScalarRestriction ComplexSubspaces ComplexPairedVectors
  ComplexPairedPlanes ComplexPairedNaturality FiniteSpans.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Orientation.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Variable V : lmodType C.
Local Notation VR := (restricted_space embed V).
Variable p : nat.
Variables v w : 'I_p -> V.
Hypothesis hv : paired_complex_vector v != 0.
Hypothesis hw : paired_complex_vector w != 0.
Hypothesis heq : forall z,
  FedererSimple.T (paired_complex_vector v) z <-> FedererSimple.T (paired_complex_vector w) z.
Local Notation hS := (paired_vector_complex hv).
Local Notation S := (stable_complex_subspace hS).
Local Notation U := (GRing.Lmodule.clone C (subspace_space S) _).

(** Source for [paired_plane_first_span]: Federer 1.6.6,
    p. 27, two complex bases of the associated space. The first
    family's complex span equals the common plane. *)
Lemma paired_plane_first_span z : in_finite_span v z <-> S z.
Proof. exact: iff_sym (paired_vector_complex_span hv z). Qed.

(** Source for [paired_plane_second_span]: Federer 1.6.6,
    p. 27, two complex bases of the associated space. The second
    family's complex span equals the same specified plane. *)
Lemma paired_plane_second_span z : in_finite_span w z <-> S z.
Proof.
have h := heq z.
rewrite (paired_vector_complex_span hw) in h.
exact: iff_sym h.
Qed.

(** Source for [paired_planes_positive_multiple]: Federer
    1.6.6, p. 27, displayed change-of-basis formula. Every two
    nonzero paired products with the same associated plane differ
    by a strictly positive real scalar, even in an infinite ambient space. *)
Theorem paired_planes_positive_multiple :
  exists d : R, 0 < d /\ paired_complex_vector w = d *: paired_complex_vector v.
Proof.
pose a : 'I_p -> U := basis_in_subspace paired_plane_first_span.
pose b : 'I_p -> U := basis_in_subspace paired_plane_second_span.
have ha : is_basis a := basis_in_subspaceP (paired_vector_independent hv) paired_plane_first_span.
have hb : is_basis b := basis_in_subspaceP (paired_vector_independent hw) paired_plane_second_span.
have [d [hd h]] := paired_complex_bases_positive_multiple ha hb.
exists d; split=> //.
pose f := restrict_linear embed (subspace_inclusion S).
have ht := congr1 (exterior_power_map f (p+p)) h.
rewrite [RHS]linearZ in ht.
change (exterior_power_map f (p+p) (paired_complex_vector b) =
  d *: exterior_power_map f (p+p) (paired_complex_vector a)) in ht.
rewrite /f !paired_complex_vector_natural in ht.
exact ht.
Qed.
End Orientation.

(** Source for [nonzero_vector_scalar_injective]: Federer
    1.6.6, p. 27, uniqueness of the scalar sign. Supporting fact:
    scalar multiples of a nonzero vector determine their scalar. *)
Lemma nonzero_vector_scalar_injective (K : fieldType) (U : lmodType K) (x : U) :
  x != 0 -> injective (fun c : K => c *: x).
Proof.
move=> hx c d h.
have hz : (c-d) *: x = 0 by rewrite scalerBl h subrr.
have /eqP hc : c-d == 0 by move/eqP: hz; rewrite scaler_eq0 (negbTE hx) orbF.
exact: subr0_eq hc.
Qed.
