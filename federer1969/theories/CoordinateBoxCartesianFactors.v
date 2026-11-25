(** Federer (1969), 4.1.23, p. 380:
    split the original closed coordinate box
    into its first and transverse blocks.
    This is the existing Euclidean block
    identification, with no change of set
    and no assumption that either block is nonempty. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockCoordinates EuclideanCartesianMap ClosedCoordinateBoxConvex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_coordinate_box_cartesian_factors]:
    the exact A=D times B
    used in the final construction
    of Federer 4.1.23, p. 380.
    Unordered endpoints and zero-dimensional
    blocks are retained by the set identity. *)
Theorem closed_coordinate_box_cartesian_factors (R : realType) m n
    (a b : R_n R (m+n)) :
  @closed_coordinate_box R (m+n) a b=
    @euclidean_cartesian_set R m n
      (@closed_coordinate_box R m (euclidean_block_split a).1 (euclidean_block_split b).1)
      (@closed_coordinate_box R n (euclidean_block_split a).2 (euclidean_block_split b).2).
Proof.
apply: funext=> x; apply: propext; split.
- move=> hx; split=> i.
  + rewrite /euclidean_block_split /= !ffunE; exact: hx.
  + rewrite /euclidean_block_split /= !ffunE; exact: hx.
- move=> [hFirst hLast] i; case: (split_ordP i)=> j ->.
  + by move: (hFirst j); rewrite /euclidean_block_split /= !ffunE.
  + by move: (hLast j); rewrite /euclidean_block_split /= !ffunE.
Qed.

(** Source for [closed_coordinate_box_block_join]:
    assembling the two endpoint blocks
    gives the same original product box,
    supporting A=D times B in
    Federer 4.1.23, p. 380. *)
Lemma closed_coordinate_box_block_join (R : realType) m n
    (a b : R_n R m) (c d : R_n R n) :
  @closed_coordinate_box R (m+n) (euclidean_block_join (a,c)) (euclidean_block_join (b,d))=
    @euclidean_cartesian_set R m n (@closed_coordinate_box R m a b)
      (@closed_coordinate_box R n c d).
Proof.
by rewrite closed_coordinate_box_cartesian_factors !euclidean_block_joinK.
Qed.
