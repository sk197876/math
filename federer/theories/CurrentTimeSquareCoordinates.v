(** Federer (1969), 4.1.11, p. 366: the
    two original scalar coordinates of the unit-square
    domain under the preceding Cartesian identification. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations EuclideanOneCoordinate EuclideanBlockCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_time_square_first]: the first
    original coordinate is s, supporting the printed
    f and g formulas in Federer 4.1.11, p. 366. *)
Lemma current_time_square_first (R:realType) (s t:R):
  @euclidean_block_join R 1%N 1%N (@euclidean_one_embed R s,@euclidean_one_embed R t) ord0=s.
Proof.
have hZero:(ord0:'I_2)=lshift 1%N (ord0:'I_1) by apply:val_inj.
by rewrite hZero euclidean_block_join_left /euclidean_one_embed ffunE.
Qed.

(** Source for [current_time_square_last]: the second
    original coordinate is t, supporting the printed
    f and g formulas in Federer 4.1.11, p. 366. *)
Lemma current_time_square_last (R:realType) (s t:R):
  @euclidean_block_join R 1%N 1%N (@euclidean_one_embed R s,@euclidean_one_embed R t)
    (lift ord0 ord0)=t.
Proof.
have hOne:(lift ord0 (ord0:'I_1):'I_2)=rshift 1%N (ord0:'I_1) by apply:val_inj.
by rewrite hOne euclidean_block_join_right /euclidean_one_embed ffunE.
Qed.
