(** Finite-dimensional linear algebra supporting Federer (1969), 2.10.5(2),
    p. 173, and its forward reference to compact convex projection
    continuity in 3.2.36, p. 272. A subset of a finite- dimensional vector
    space is spanned by finitely many independent members of that same
    subset. This is a supporting basis-selection lemma, using the dimension
    and independence background of 1.6.1, p. 23; it is not a separate claim
    attributed to either measure passage. Neither item states this
    particular maximum-length selection lemma. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import LinearBasis FiniteIndependence InfiniteSequence FiniteSpans
  FiniteDimension FiniteBasisComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_subset_independent_span]: supporting
    selection of finitely many source differences
    for the convex geometry behind Federer
    2.10.5(2), p. 173, and 3.2.36, p. 272.
    The independent spanning vectors belong to
    the given subset, which may be empty. *)
Theorem finite_subset_independent_span (K : fieldType) (V : lmodType K)
    n (b : 'I_n -> V) (hb : is_basis b) (D : set V) :
  exists k (e : 'I_k -> V), (k<=n)%N /\ finite_independent e /\
    (forall i, D (e i)) /\ (forall v, D v -> in_finite_span e v).
Proof.
pose P k := `[< exists e : 'I_k -> V, finite_independent e /\ forall i, D (e i) >].
have hex : exists k, P k.
  exists 0%N; apply/asboolP; exists (fun _ : 'I_0 => (0 : V)); split.
  - move=> c hc i; by have := ltn_ord i; rewrite ltn0.
  - move=> i; by have := ltn_ord i; rewrite ltn0.
have hbound k : P k -> (k<=n)%N.
  move/asboolP=> [e [hi _]].
  have hd := @finite_independent_dimension K (finite_basis_vect hb) k e hi.
  by rewrite finite_basis_dimension card_ord in hd.
have [k /asboolP [e [hi heD]] hmax] := @ex_maxnP P n hex hbound.
exists k,e; split; first by apply: hbound; apply/asboolP; exists e.
split=> //; split=> // v hv.
case: (pselect (in_finite_span e v))=> hspan //.
have hnot c : v!=\sum_i c i *: e i.
  apply/eqP=> he; apply: hspan; by exists c.
have hsnoc := finite_independent_snoc hi hnot.
have hDsnoc i : D (ordinal_snoc e v i).
  case: (unliftP ord_max i)=> [j ->|->]; last by rewrite ordinal_snoc_last.
  rewrite ordinal_snoc_lift; exact: heD.
have hnext : P k.+1 by apply/asboolP; exists (ordinal_snoc e v); by split.
by have := hmax k.+1 hnext; rewrite ltnn.
Qed.
