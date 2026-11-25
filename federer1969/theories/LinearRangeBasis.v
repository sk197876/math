(** Federer (1969), 1.7.4, p. 31, final paragraph: dimensions of the images
    of orthogonal adjoints. Supporting basis transfer for an injective
    linear map. editions: InnerProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient SubspaceCarrier SubspaceSums
  SubspaceFamilies SpanningDimension FiniteBasisCriterion FiniteBasisComparison
  FiniteIndependence FiniteSpans LinearBasis FiniteDualDimension Annihilator Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [injective_range_basis_exists]: Federer 1.7.4,
    p. 31, supporting equality dim im f*=dim W1 for an orthogonal
    injection f*. The images of a basis give a basis of its range. *)
Theorem injective_range_basis_exists (R : fieldType) (V U : lmodType R)
    (f : {linear V -> U}) (hf : injective f)
    n (e : 'I_n -> V) (he : is_basis e) :
  exists a : 'I_n -> subspace_space (range_subspace f), is_basis a.
Proof.
have hin i : range_subspace f (f (e i)) by exists (e i).
exists (subspace_family hin); apply: finite_basis_criterion.
- apply: subspace_family_independent.
  exact: finite_independent_map hf (finite_basis_independent he).
- apply: subspace_family_spans => y [x ->].
  exists (fun i => dual_basis he i x).
  rewrite {1}(basis_vector_expansion he x) linear_sum.
  apply: eq_bigr => i _; exact: linearZ.
Qed.
