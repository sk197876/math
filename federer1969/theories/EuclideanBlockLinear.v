(** Supporting stacked normal coordinates for Federer (1969), 2.10.16, p.
    178, using the actual block isomorphism of 2.6.5, p. 120. Prove its
    linear and inner-product laws from the public coordinate evaluations;
    its empty blocks remain valid. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanBlockCoordinates ConcatenatedFamilies TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_block_vectors_ext]: supporting coordinate
    extensionality for the block isomorphism of 2.6.5, p. 120,
    used in the normal-coordinate stacking of 2.10.16, p. 178. *)
Lemma euclidean_block_vectors_ext (R : realType) (a r : nat)
    (u v : R_n R (a+r)) :
  (forall i, u (lshift r i)=v (lshift r i)) ->
  (forall i, u (rshift a i)=v (rshift a i)) -> u=v.
Proof.
move=> hl hr; apply/ffunP=> i.
rewrite -(splitK i); case: (split i)=> j; [exact: hl|exact: hr].
Qed.

(** Source for [euclidean_block_join_linear]: supporting linear
    law of the actual block isomorphism in 2.6.5, p. 120,
    used to define stacked linear normal maps in 2.10.16,
    p. 178. This includes zero-dimensional coordinate blocks. *)
Lemma euclidean_block_join_linear (R : realType) (a r : nat) :
  linear (@euclidean_block_join R a r).
Proof.
move=> t u v; apply: euclidean_block_vectors_ext.
- move=> i; by rewrite euclidean_block_join_left !ffunE !concatenate_family_l.
- move=> i; by rewrite euclidean_block_join_right !ffunE !concatenate_family_r.
Qed.

(** Source for [euclidean_block_join_inner]: supporting isometric
    law of the block isomorphism of 2.6.5, p. 120.
    The Euclidean dot product splits into the sum of the
    two block dot products, as needed for the normal
    Jacobian in 2.10.16, p. 178. *)
Lemma euclidean_block_join_inner (R : realType) (a r : nat)
    (u v : R_n R a * R_n R r) :
  euclidean_inner_product (euclidean_block_join u) (euclidean_block_join v)=
    euclidean_inner_product u.1 v.1+euclidean_inner_product u.2 v.2.
Proof.
rewrite /euclidean_inner_product big_split_ord.
congr (_+_); apply: eq_bigr=> i _;
  by rewrite ?euclidean_block_join_left ?euclidean_block_join_right.
Qed.
