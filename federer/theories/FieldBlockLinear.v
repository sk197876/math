(** Federer (1969), 3.4.12, p. 339: original complex
    coordinate block maps are linear. Extend only the scalar-field
    interface of the existing finite block identities. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import FiniteCoordinates FieldBlockCoordinates ConcatenatedFamilies TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [field_block_vectors_ext]: supporting coordinate
    extensionality for the block isomorphism of 2.6.5, p. 120,
    used in the normal-coordinate stacking of 2.10.16, p. 178. *)
Lemma field_block_vectors_ext (R : fieldType) (a r : nat)
    (u v : coordinate_space R (a+r)) :
  (forall i, u (lshift r i)=v (lshift r i)) ->
  (forall i, u (rshift a i)=v (rshift a i)) -> u=v.
Proof.
move=> hl hr; apply/ffunP=> i.
rewrite -(splitK i); case: (split i)=> j; [exact: hl|exact: hr].
Qed.

(** Source for [field_block_join_linear]: supporting linear
    law of the actual block isomorphism in 2.6.5, p. 120,
    used to define stacked linear normal maps in 2.10.16,
    p. 178. This includes zero-dimensional coordinate blocks. *)
Lemma field_block_join_linear (R : fieldType) (a r : nat) :
  linear (@field_block_join R a r).
Proof.
move=> t u v; apply: field_block_vectors_ext.
- move=> i; by rewrite field_block_join_left !ffunE !concatenate_family_l.
- move=> i; by rewrite field_block_join_right !ffunE !concatenate_family_r.
Qed.
