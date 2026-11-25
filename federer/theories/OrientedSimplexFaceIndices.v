(** Federer (1969), 4.1.11, p. 365: ordered face
    bookkeeping in the original alternating boundary sum.
    Use the preceding ordered deletion and the ordinary
    finite-ordinal lift laws. No permutation theorem for
    currents is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import OrientedSimplexCurrentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [current_simplex_face_head_positive]: every
    face except the first retains the original first
    vertex, supporting the recursive boundary computation
    in Federer 4.1.11, p. 365. *)
Lemma current_simplex_face_head_positive (X:Type) m
    (v:'I_(m.+3)->X) (k:'I_(m.+2)):
  current_simplex_face v (lift ord0 k) ord0=v ord0.
Proof.
congr (v _);apply:val_inj.
change (bump (lift ord0 k) 0%N=0%N).
by rewrite lift0 /bump /=.
Qed.

(** Source for [current_simplex_tail_face_positive]: the
    tail of a nonfirst face is the corresponding face
    of the original tail, supporting the boundary sum
    in Federer 4.1.11, p. 365. *)
Lemma current_simplex_tail_face_positive (X:Type) m
    (v:'I_(m.+3)->X) (k:'I_(m.+2)):
  current_simplex_tail (current_simplex_face v (lift ord0 k))=
    current_simplex_face (current_simplex_tail v) k.
Proof.
apply:funext=>i;congr (v _);apply:val_inj.
change (bump (lift ord0 k) (lift ord0 i)=bump 0%N (lift k i)).
by rewrite !lift0 bumpS /bump /=.
Qed.

(** Source for [current_simplex_pair_last_face]: deleting
    the last vertex of the original one-simplex leaves
    its first point, supporting the first boundary-sum
    endpoint in Federer 4.1.11, p. 365. *)
Lemma current_simplex_pair_last_face (X:Type) (v:'I_2->X):
  current_simplex_face v ord_max ord0=v ord0.
Proof. congr (v _);apply:val_inj;reflexivity. Qed.
