(** Federer (1969), 1.7.4, p. 31, last paragraph: the intersection of the
    two adjoint images has dimension at least dim W1 + dim W2 - dim V.
    Supporting dimension argument proved from bases and orthogonal
    splitting. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient SubspaceCarrier LinearBasis
  InnerProductUP OrthogonalComplement InvariantOrthogonalSplit
  AnnihilatorIntersection AnnihilatorDimension SubspaceSumDimension
  SubspaceBasisProduct FiniteIndependence FiniteBasisComparison
  FiniteDimension FiniteSpans IndependentConcatenation ConcatenatedFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [intersection_dimension_bound]: Federer 1.7.4,
    p. 31, final paragraph, dimension estimate for the intersection.
    Written without truncated natural subtraction: dim S + dim T
    is at most dim V + dim (S intersect T). *)
Theorem intersection_dimension_bound (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (b : 'I_n -> V) (hb : is_basis b)
    (S T : subspace V)
    m1 (a1 : 'I_m1 -> subspace_space S) (ha1 : is_basis a1)
    m2 (a2 : 'I_m2 -> subspace_space T) (ha2 : is_basis a2)
    k (a : 'I_k -> subspace_space (subspace_intersection S T))
    (ha : is_basis a) : (m1+m2 <= n+k)%N.
Proof.
pose I := subspace_intersection S T.
pose Q := @relative_orthogonal_complement R V B hB T I.
have [l [c [hc hl]]] := @finite_subspace_basis_exists R V n b hb Q.
have hIT x : I x -> T x by case.
have hsplit x : T x <-> exists y z, I y /\ Q z /\ x=y+z.
  split.
  - exact: (@relative_orthogonal_split R V B hB T I hIT k a ha x).
  - move=> [y [z [hy [[hz _] ->]]]]; exact (@subspace_add R V T y z (@hIT y hy) hz).
have hdis x : I x -> Q x -> x=0.
  move=> hi [_ ho]; exact: (@orthogonal_complement_intersection_zero R V B hB I x hi ho).
have heq : (k+l=m2)%N := proj2
  (@sum_dimension_iff_disjoint R V I Q T hsplit k l m2 a c a2 ha hc ha2) hdis.
pose av := fun i => subspace_val (a1 i).
pose cv := fun i => subspace_val (c i).
have hai : finite_independent av := finite_independent_map
  (@subspace_val_injective R V S) (finite_basis_independent ha1).
have hci : finite_independent cv := finite_independent_map
  (@subspace_val_injective R V Q) (finite_basis_independent hc).
have hd x : in_finite_span av x -> in_finite_span cv x -> x=0.
  move=> hs hq.
  have hs' := proj1 (@subspace_basis_span R V S m1 a1 ha1 x) hs.
  have hq' := proj1 (@subspace_basis_span R V Q l c hc x) hq.
  have [ht ho] := hq'.
  exact: hdis (conj hs' ht) hq'.
have hind := disjoint_concatenation_independent hai hci hd.
have hdim := @finite_independent_dimension R (finite_basis_vect hb)
  (m1+l) (concatenate_family av cv) hind.
rewrite finite_basis_dimension card_ord in hdim.
have hh := leq_add hdim (leqnn k).
by rewrite addnAC -addnA heq in hh.
Qed.
