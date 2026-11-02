(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDuality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.3, the direct sum: subspaces are the actual ranges of
    the two linear operations. The predicate states spanning and zero
    intersection, and the following lemma gives uniqueness of summands. *)
Section Subspaces.
Variable K : fieldType.
Variables X Y : lmodType K.
Variable f : {linear X -> Y}.
(** Source for [linear_range]: Federer (1969), 1.5.3, p. 23, two
    equivalences and the following direct-sum display. In words: The kernels
    of the two square-zero operations are the corresponding images, and the
    space of positive-degree forms splits into the two displayed image
    subspaces. Definition or construction used to formalise this passage. *)
Definition linear_range (y : Y) := exists x, y = f x.
(** Source for [linear_range_zero]: Federer (1969), 1.5.3, p. 23, two
    equivalences and the following direct-sum display. In words: The kernels
    of the two square-zero operations are the corresponding images, and the
    space of positive-degree forms splits into the two displayed image
    subspaces. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma linear_range_zero : linear_range 0.
Proof. exists 0; symmetry; exact: linear0. Qed.
(** Source for [linear_range_add]: Federer (1969), 1.5.3, p. 23, two
    equivalences and the following direct-sum display. In words: The kernels
    of the two square-zero operations are the corresponding images, and the
    space of positive-degree forms splits into the two displayed image
    subspaces. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma linear_range_add y z : linear_range y -> linear_range z -> linear_range (y+z).
Proof. move=> [x ->] [w ->]; exists (x+w); symmetry; exact: linearD. Qed.
(** Source for [linear_range_scale]: Federer (1969), 1.5.3, p. 23, two
    equivalences and the following direct-sum display. In words: The kernels
    of the two square-zero operations are the corresponding images, and the
    space of positive-degree forms splits into the two displayed image
    subspaces. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma linear_range_scale c y : linear_range y -> linear_range (c *: y).
Proof. move=> [x ->]; exists (c *: x); symmetry; exact: linearZ. Qed.
(** Source for [range_subspace]: Federer (1969), 1.5.3, p. 23, two
    equivalences and the following direct-sum display. In words: The kernels
    of the two square-zero operations are the corresponding images, and the
    space of positive-degree forms splits into the two displayed image
    subspaces. Definition or construction used to formalise this passage. *)
Definition range_subspace : subspace Y :=
  @Subspace K Y linear_range linear_range_zero linear_range_add linear_range_scale.
End Subspaces.
Section DirectSum.
Variable K : fieldType.
Variable X : lmodType K.
Variables P Q : subspace X.
(** Source for [is_internal_direct_sum]: Federer (1969), 1.5.3, p. 23, two
    equivalences and the following direct-sum display. In words: The kernels
    of the two square-zero operations are the corresponding images, and the
    space of positive-degree forms splits into the two displayed image
    subspaces. Definition or construction used to formalise this passage. *)
Definition is_internal_direct_sum : Prop :=
  (forall x : X, exists p q, P p /\ Q q /\ x=p+q) /\
  (forall x, P x -> Q x -> x=0).
(** Source for [internal_sum_unique]: Federer (1969), 1.5.3, p. 23, two
    equivalences and the following direct-sum display. In words: The kernels
    of the two square-zero operations are the corresponding images, and the
    space of positive-degree forms splits into the two displayed image
    subspaces. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma internal_sum_unique : is_internal_direct_sum ->
  forall p q p' q', P p -> Q q -> P p' -> Q q' ->
    p+q=p'+q' -> p=p' /\ q=q'.
Proof.
move=> [_ hinter] p q p' q' hp hq hp' hq' h.
have he : p-p' = q'-q.
  apply: (@addIr _ q).
  by rewrite subrK addrAC h addrAC subrr add0r.
have hz : p-p'=0.
  apply: hinter; first exact: subspace_sub hp hp'.
  rewrite he; exact: subspace_sub hq' hq.
have hpp : p=p' by apply/eqP; rewrite -subr_eq0 hz.
split; first exact: hpp.
by move: h; rewrite hpp => /addrI.
Qed.
End DirectSum.
