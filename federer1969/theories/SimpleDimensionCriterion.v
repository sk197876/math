(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import AssociatedSubspace SubspaceCarrier SubspaceFamilies
  SimpleElementary SimpleAssociatedBasis AssociatedDimension FiniteBasisComparison
  FullDegreeFactor BasisSizeTransport.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, first corollary: a nonzero simple m-vector is the
    product of a suitable basis of its associated space. This implication
    includes degree zero under the literal empty-product convention. *)
Section Criterion.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable m : nat.
Variable xi : exterior_power V m.
Hypothesis hxi : xi != 0.
Local Notation T := (FedererSimple.T xi).
Local Notation U := (GRing.Lmodule.clone K (subspace_space T) _).
(** Source for [simple_is_basis_product]: Federer (1969), 1.6.1, p. 24,
    first of the four corollaries. In words: The printed corollary
    identifies nonzero simple m-vectors with those whose associated space
    has dimension m, and represents them as products of a suitable basis.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. For the literal empty-product definition the reverse
    implication requires m>0. *)
Theorem simple_is_basis_product : simple xi ->
  exists e : 'I_m -> U, is_basis e /\
    xi = e_lambda (fun i => subspace_val (e i)) (ord_tuple m).
Proof.
move=> [t hx]; rewrite tuple_product in hx; subst xi.
exists (product_basis (tnth t)); split; last by [].
exact (@product_basisP K h2 V m (tnth t) hxi).
Qed.
(** Source for [simple_dimension]: Federer (1969), 1.6.1, p. 24, first of
    the four corollaries. In words: The printed corollary identifies nonzero
    simple m-vectors with those whose associated space has dimension m, and
    represents them as products of a suitable basis. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. For the literal empty-product definition the reverse implication
    requires m>0. *)
Theorem simple_dimension : simple xi -> dim (associated_space h2 hxi) = m.
Proof.
move/simple_is_basis_product=> [e [he hx]].
exact: associated_basis_dimension he.
Qed.
(** Source for [dimension_simple]: Federer (1969), 1.6.1, p. 24, first of
    the four corollaries. In words: The printed corollary identifies nonzero
    simple m-vectors with those whose associated space has dimension m, and
    represents them as products of a suitable basis. Supporting lemma for
    this passage; not separately stated in the book. For the literal
    empty-product definition the reverse implication requires m>0. *)
Theorem dimension_simple : (0 < m)%N ->
  dim (associated_space h2 hxi) = m -> simple xi.
Proof.
move=> hm hd.
have hkm : associated_k h2 hxi = m.
  by move: hd; rewrite /associated_space finite_basis_dimension card_ord.
pose e : 'I_m -> U := fun i => @associated_e K h2 V m xi hxi (cast_ord (esym hkm) i).
have he : is_basis e := basis_cast_size hkm (@associated_e_basis K h2 V m xi hxi).
have hi : finite_independent (fun i => subspace_inclusion T (e i)).
  exact: finite_independent_map (@subspace_val_injective K V T) (finite_basis_independent he).
have ht i : T (subspace_inclusion T (e i)) := subspace_valP (e i).
have [c [hc hx]] := @full_degree_factor K h2 V m xi _ hi ht hxi.
rewrite hx; exact: simple_scale hm (product_simple _).
Qed.
(** Source for [simple_iff_dimension]: Federer (1969), 1.6.1, p. 24, first
    of the four corollaries. In words: The printed corollary identifies
    nonzero simple m-vectors with those whose associated space has dimension
    m, and represents them as products of a suitable basis. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. For the literal empty-product definition the reverse implication
    requires m>0. *)
Theorem simple_iff_dimension : (0 < m)%N ->
  (simple xi <-> dim (associated_space h2 hxi) = m).
Proof. move=> hm; split; [exact: simple_dimension|exact: dimension_simple hm]. Qed.
(** Source for [full_dimension_basis_product]: Federer (1969), 1.6.1, p. 24,
    first of the four corollaries. In words: The printed corollary
    identifies nonzero simple m-vectors with those whose associated space
    has dimension m, and represents them as products of a suitable basis.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. For the literal empty-product definition the reverse
    implication requires m>0. *)
Theorem full_dimension_basis_product : (0 < m)%N ->
  dim (associated_space h2 hxi) = m ->
  exists e : 'I_m -> U, is_basis e /\
    xi = e_lambda (fun i => subspace_val (e i)) (ord_tuple m).
Proof. move=> hm hd; exact: simple_is_basis_product (dimension_simple hm hd). Qed.
End Criterion.
