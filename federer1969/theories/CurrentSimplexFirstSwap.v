(** Federer (1969), 4.1.11, p. 366: exchange the
    first two vertices in the original boundary argument.
    These are ordered-family identities only. They use
    the ordinary finite transposition and ordinal lift
    laws already used in Chapters 1 and 3. *)
From mathcomp Require Import all_boot all_order all_algebra boolp fingroup perm.
From Federer Require Import OrientedSimplexCurrentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [current_simplex_first_swap]: the original
    vertex family (u_1,u_0,u_2,...), supporting the
    orientation argument in Federer 4.1.11, p. 366.
    This is precomposition by the existing transposition. *)
Definition current_simplex_first_swap (X:Type) m (v:'I_(m.+2)->X):'I_(m.+2)->X:=
  fun k=>v (tperm ord0 (lift ord0 ord0) k).

(** Source for [current_simplex_first_swap_head]: the
    exchanged first vertex is u_1, supporting Federer
    4.1.11, p. 366. *)
Lemma current_simplex_first_swap_head (X:Type) m (v:'I_(m.+2)->X):
  current_simplex_first_swap v ord0=v (lift ord0 ord0).
Proof. by rewrite /current_simplex_first_swap tpermL. Qed.

(** Source for [current_simplex_first_swap_second]: the
    exchanged second vertex is u_0, supporting Federer
    4.1.11, p. 366. *)
Lemma current_simplex_first_swap_second (X:Type) m (v:'I_(m.+2)->X):
  current_simplex_first_swap v (lift ord0 ord0)=v ord0.
Proof. by rewrite /current_simplex_first_swap tpermR. Qed.

(** Source for [current_simplex_first_swap_rest]: all
    later vertices retain their order, supporting the
    boundary cancellation in Federer 4.1.11, p. 366. *)
Lemma current_simplex_first_swap_rest (X:Type) m (v:'I_(m.+2)->X) (k:'I_m):
  current_simplex_first_swap v (lift ord0 (lift ord0 k))=v (lift ord0 (lift ord0 k)).
Proof.
have hFirst:(ord0:'I_(m.+2))!=lift ord0 (lift ord0 k) by exact:neq_lift.
have hSecond:(lift ord0 (ord0:'I_(m.+1)))!=lift ord0 (lift ord0 k).
  by rewrite (inj_eq (@lift_inj (m.+2) ord0)) neq_lift.
by rewrite /current_simplex_first_swap (tpermD hFirst hSecond).
Qed.

(** Source for [current_simplex_first_swap_involution]:
    exchanging the original first pair twice restores the
    family, supporting Federer 4.1.11, p. 366. *)
Lemma current_simplex_first_swap_involution (X:Type) m (v:'I_(m.+2)->X):
  current_simplex_first_swap (current_simplex_first_swap v)=v.
Proof. apply:funext=>k;by rewrite /current_simplex_first_swap tpermK. Qed.

(** Source for [current_simplex_first_swap_lift]: the
    ordered indices after deleting the exchanged first
    vertex are exactly those after deleting the original
    second vertex, supporting Federer 4.1.11, p. 366. *)
Lemma current_simplex_first_swap_lift m (i:'I_(m.+1)):
  tperm (ord0:'I_(m.+2)) (lift ord0 ord0) (lift ord0 i)=lift (lift ord0 ord0) i.
Proof.
case:(unliftP ord0 i)=>[k ->|->].
- have hFirst:(ord0:'I_(m.+2))!=lift ord0 (lift ord0 k) by exact:neq_lift.
  have hSecond:(lift ord0 (ord0:'I_(m.+1)))!=lift ord0 (lift ord0 k).
    by rewrite (inj_eq (@lift_inj (m.+2) ord0)) neq_lift.
  rewrite (tpermD hFirst hSecond);apply:val_inj.
  change (bump 0%N (bump 0%N (k:nat))=bump 1%N (bump 0%N (k:nat))).
  by rewrite /bump /=.
- rewrite tpermR;apply:val_inj;reflexivity.
Qed.

(** Source for [current_simplex_first_swap_face_zero]:
    the first face of the exchanged simplex is the
    original second face, supporting Federer 4.1.11,
    p. 366. *)
Lemma current_simplex_first_swap_face_zero (X:Type) m (v:'I_(m.+2)->X):
  current_simplex_face (current_simplex_first_swap v) ord0=
    current_simplex_face v (lift ord0 ord0).
Proof.
apply:funext=>i;change (v (tperm ord0 (lift ord0 ord0) (lift ord0 i))=v (lift (lift ord0 ord0) i)).
by rewrite current_simplex_first_swap_lift.
Qed.

(** Source for [current_simplex_first_swap_face_one]: the
    second face of the exchanged simplex is the original
    first face, supporting Federer 4.1.11, p. 366. *)
Lemma current_simplex_first_swap_face_one (X:Type) m (v:'I_(m.+2)->X):
  current_simplex_face (current_simplex_first_swap v) (lift ord0 ord0)=current_simplex_tail v.
Proof.
have h:=@current_simplex_first_swap_face_zero X m (current_simplex_first_swap v).
rewrite current_simplex_first_swap_involution in h;exact:esym h.
Qed.

(** Source for [current_simplex_first_swap_later_face]:
    every later face of the exchanged simplex is the
    first-pair exchange of its original face, supporting
    the induction in Federer 4.1.11, p. 366. *)
Lemma current_simplex_first_swap_later_face (X:Type) m (v:'I_(m.+3)->X) (k:'I_(m.+1)):
  current_simplex_face (current_simplex_first_swap v) (lift ord0 (lift ord0 k))=
    current_simplex_first_swap (current_simplex_face v (lift ord0 (lift ord0 k))).
Proof.
pose h:=lift (ord0:'I_(m.+3)) (lift ord0 k).
have hZero:lift h (ord0:'I_(m.+2))=(ord0:'I_(m.+3)).
  apply:val_inj;change (bump (lift ord0 (lift ord0 k)) 0%N=0%N).
  by rewrite !lift0 /bump /=.
have hOne:lift h (lift ord0 (ord0:'I_(m.+1)))=lift ord0 (ord0:'I_(m.+2)).
  apply:val_inj;change (bump (lift ord0 (lift ord0 k)) (lift ord0 (ord0:'I_(m.+1)))=
    (lift ord0 (ord0:'I_(m.+2)):nat)).
  by rewrite !lift0 /bump /=.
apply:funext=>i.
have hPerm:=@inj_tperm (Finite.clone 'I_(m.+2) _) (Finite.clone 'I_(m.+3) _)
  (lift h) ord0 (lift ord0 ord0) i (@lift_inj (m.+3) h).
rewrite hZero hOne in hPerm.
change (v (tperm ord0 (lift ord0 ord0) (lift h i))=v (lift h (tperm ord0 (lift ord0 ord0) i))).
by rewrite -hPerm.
Qed.
