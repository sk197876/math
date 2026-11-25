(** Federer (1969), 3.4.12, p. 339: the original complex
    coordinate blocks use the finite concatenation laws already proved
    for 2.6.5, p. 120. This supplies their field-generic carrier
    connection, including empty blocks; topology is proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import FiniteCoordinates ConcatenatedFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Blocks.
Variable R : fieldType.
Variables m n : nat.
Local Notation E k := (coordinate_space R k).

(** Source for [field_block_join]: inverse of the
    usual block isomorphism in Federer 2.6.5, p. 120,
    concatenating the two ordered coordinate families. *)
Definition field_block_join (p : E m * E n) : E (m+n) :=
  [ffun i => concatenate_family p.1 p.2 i].

(** Source for [field_block_split]: the usual
    isomorphism in Federer 2.6.5, p. 120, with
    first m and final n coordinates as its two factors. *)
Definition field_block_split (x : E (m+n)) : E m * E n :=
  ([ffun i => x (lshift n i)], [ffun j => x (rshift m j)]).

(** Source for [field_block_join_left]: first block
    of the inverse identification, Federer 2.6.5, p. 120. *)
Lemma field_block_join_left p i : field_block_join p (lshift n i) = p.1 i.
Proof. by rewrite /field_block_join ffunE concatenate_family_l. Qed.

(** Source for [field_block_join_right]: second block
    of the inverse identification, Federer 2.6.5, p. 120. *)
Lemma field_block_join_right p j : field_block_join p (rshift m j) = p.2 j.
Proof. by rewrite /field_block_join ffunE concatenate_family_r. Qed.

(** Source for [field_block_joinK]: first inverse
    identity for the usual isomorphism of Federer 2.6.5,
    p. 120, including empty blocks. *)
Lemma field_block_joinK : cancel field_block_join field_block_split.
Proof.
move=> [u v]; rewrite /field_block_split; congr (_,_); apply/ffunP=> i;
  by rewrite ffunE ?field_block_join_left ?field_block_join_right.
Qed.

(** Source for [field_block_splitK]: second inverse
    identity for the usual isomorphism of Federer 2.6.5,
    p. 120. *)
Lemma field_block_splitK : cancel field_block_split field_block_join.
Proof.
move=> x; apply/ffunP=> i; rewrite /field_block_join ffunE /concatenate_family.
case: (splitP i)=> j hij; rewrite /field_block_split /= ffunE;
  congr (x _); apply: val_inj; exact: esym hij.
Qed.

End Blocks.
