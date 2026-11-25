(** Federer (1969), 1.7.1, p. 28: orthonormalisation with every initial span
    preserved, and existence of an orthonormal basis in finite dimension.
    Only the abstract sealed specification is used in this public interface.
    Source context are recorded in InnerProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP OrthonormalFamilies
  OrthonormalisationUP OrthonormalisationSealed FiniteIndependence
  FiniteBasisCriterion FiniteBasisComparison Annihilator FiniteSpans LinearBasis FiniteDualDimension Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section GramSchmidt.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.

(** Source for [gram_schmidt_family]: Federer 1.7.1,
    p. 28, the orthonormalising family provided by the sealed
    specification, without exposing its existence construction. *)
Definition gram_schmidt_family n (u : 'I_n -> V) (hu : finite_independent u) :=
  @Orthonormalisation.family R V B hB n u hu.

(** Source for [gram_schmidtP]: Federer 1.7.1, p. 28,
    the chosen family is orthonormal and preserves every prefix span. *)
Theorem gram_schmidtP n (u : 'I_n -> V) (hu : finite_independent u) :
  is_orthonormalisation B u (gram_schmidt_family hu).
Proof. exact: Orthonormalisation.laws. Qed.

(** Source for [gram_schmidt_exists]: Federer 1.7.1,
    p. 28, existence in the book's full prefix-preserving form.
    The ambient space may have arbitrary dimension; n=0 is included. *)
Theorem gram_schmidt_exists n (u : 'I_n -> V) :
  finite_independent u -> exists v, is_orthonormalisation B u v.
Proof. move=> hu; exists (gram_schmidt_family hu); exact: gram_schmidtP. Qed.

(** Source for [orthonormal_basis_exists]: Federer 1.7.1,
    p. 28, finite-dimensional corollary. An arbitrary given finite
    basis can be replaced by an orthonormal basis with the same prefix spans. *)
Theorem orthonormal_basis_exists n (u : 'I_n -> V) :
  is_basis u -> exists v, is_basis v /\ is_orthonormalisation B u v.
Proof.
move=> hu.
have [v hv] := gram_schmidt_exists (finite_basis_independent hu).
exists v; split=> //.
apply: finite_basis_criterion.
- exact (@orthonormal_independent R V B hB (Finite.clone 'I_n _) v
    (orthonormalisation_orthonormal hv)).
- move=> x; apply: (proj1 (@orthonormalisation_span R V B n u v hv x)).
  exists (fun i => dual_basis hu i x); exact: basis_vector_expansion.
Qed.
End GramSchmidt.
