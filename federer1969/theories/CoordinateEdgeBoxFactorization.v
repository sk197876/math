(** Federer (1969), 3.2.36, p. 273: the actual
    coordinate box is the Cartesian product of its first edge and tail. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  EuclideanCartesianMap EuclideanBlockVolumes CoordinateEdgeBoxGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_edge_box_factorization]: the successive
    Cartesian edge decomposition proving the rectangular-box consequence
    in Federer 3.2.36, p. 273. The first factor is the
    actual interval in R^1 and the second the remaining coordinate
    box. Both block inverse formulas give equality of the original
    carriers, with zero or negative edge values allowed. *)
Lemma coordinate_edge_box_factorization (R:realType) n (c:'I_n.+1->R):
  coordinate_edge_box c=euclidean_cartesian_set
    (coordinate_edge_box (fun _:'I_1=>c ord0))
    (coordinate_edge_box (fun i:'I_n=>c (rshift 1 i))).
Proof.
have hHead:lshift n (ord0:'I_1)=(ord0:'I_n.+1) by apply:val_inj.
apply/seteqP; split=>z.
- move=>hz; split.
  + move=>i; rewrite (ord1 i).
    change (is_true (0<=((@euclidean_block_split R 1 n z).1) ord0<=c ord0)).
    rewrite /euclidean_block_split ffunE hHead; exact:hz.
  + move=>i.
    change (is_true (0<=((@euclidean_block_split R 1 n z).2) i<=c (rshift 1 i))).
    rewrite /euclidean_block_split ffunE; exact:hz.
- move=>[hFirst hTail] i; case:(@split_ordP 1 n i)=>[j ->|j ->].
  + rewrite (ord1 j) hHead.
    have h:=hFirst ord0.
    move:h; by rewrite /euclidean_block_split ffunE hHead.
  + have h:=hTail j.
    move:h; by rewrite /euclidean_block_split ffunE.
Qed.

(** Source for [coordinate_edge_linear_factor_product]: the first
    edge times the tail generating product in the elementary symmetric
    consequence of Federer 3.2.36, p. 273. Finite block
    partition and the actual one-coordinate ordinal identify the product,
    including an empty tail. *)
Lemma coordinate_edge_linear_factor_product (R:realType) n (c:'I_n.+1->R) (t:R):
  \prod_(i:'I_n.+1) (1+c i*t)=
    (1+c ord0*t)*(\prod_(j:'I_n) (1+c (rshift 1 j)*t)).
Proof.
change (\prod_(i:'I_(1+n)) (1+c i*t)=
  (1+c ord0*t)*(\prod_(j:'I_n) (1+c (rshift 1 j)*t))).
rewrite big_split_ord big_ord1.
have hHead:lshift n (ord0:'I_1)=(ord0:'I_n.+1) by apply:val_inj.
by rewrite hHead.
Qed.
