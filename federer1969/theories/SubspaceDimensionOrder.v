(** Federer (1969), 1.7.3, p. 29: supporting dimension induction for the
    minimal invariant decomposition. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient SubspaceCarrier SubspaceFamilies
  FiniteIndependence FiniteBasisComparison FiniteDimension LinearBasis
  FiniteSpans InvariantFiniteSpan InfiniteSequence InteriorDecomposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [proper_subspace_dimension_lt]: Federer 1.7.3,
    p. 29, supporting strict decrease: a proper subspace has
    smaller finite dimension. Both dimensions are specified by bases. *)
Theorem proper_subspace_dimension_lt (R : fieldType) (V : lmodType R)
    (S W : subspace V) (hSW : forall x, S x -> W x)
    k (a : 'I_k -> subspace_space S) (ha : is_basis a)
    n (b : 'I_n -> subspace_space W) (hb : is_basis b) :
  (exists x, W x /\ ~ S x) -> (k < n)%N.
Proof.
move=> [x [hx hnx]].
pose e := fun i => subspace_val (a i).
have he : finite_independent e.
  exact: finite_independent_map (@subspace_val_injective R V S)
    (finite_basis_independent ha).
have hmiss c : x != \sum_i c i *: e i.
  apply/eqP=> h; apply: hnx.
  apply: (@finite_span_subspace_contained R V k e S).
  - move=> i; exact: subspace_valP.
  - by exists c.
have hei := finite_independent_snoc he hmiss.
pose d := ordinal_snoc e x.
have hd i : W (d i).
  case: (unliftP ord_max i) => [j ->|->].
  - rewrite /d ordinal_snoc_lift; apply: hSW; exact: subspace_valP.
  - by rewrite /d ordinal_snoc_last.
have hdi := @subspace_family_independent R V W (Finite.clone 'I_k.+1 _) d hd hei.
have hdim := @finite_independent_dimension R
  (finite_basis_vect hb) k.+1 (subspace_family hd) hdi.
by rewrite finite_basis_dimension card_ord in hdim.
Qed.
