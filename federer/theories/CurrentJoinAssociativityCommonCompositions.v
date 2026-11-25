(** Federer (1969), 4.1.11, p. 366: identify
    both literal iterated join maps after the common
    source reordering with the two printed H compositions.
    Reuse the exact original coordinate identities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanBlockCoordinates CurrentJoinAssociatorMapsSealed CurrentJoinAssociatorMapsLaws
  CurrentJoinAssociativityRegroup CurrentJoinAssociativitySquareSlot CurrentJoinAssociativityCommonMap
  CurrentJoinAssociativityIteratedMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinAssociativityCommonCompositions.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Point := (fun (x y z:X) (s t:R)=>@euclidean_block_join R n (n+(2+n))%N
  (x,@euclidean_block_join R n (2+n)%N
    (y,@euclidean_block_join R 2%N n
      (@euclidean_block_join R 1%N 1%N (@euclidean_one_embed R s,@euclidean_one_embed R t),z)))).
Local Notation L := (@current_join_assoc_common_regroup R n).
Local Notation H := (@current_join_assoc_weighted_map R n).
Local Notation Slot := (@current_join_assoc_square_slot R n).
Local Notation f := (@CurrentJoinAssociatorMaps.left_triangle R).
Local Notation g := (@CurrentJoinAssociatorMaps.right_triangle R).

(** Source for [current_join_assoc_common_point_cover]: every
    original common-source point has its original spatial
    and two real time coordinates, supporting the
    composition argument in Federer 4.1.11, p. 366. *)
Lemma current_join_assoc_common_point_cover (p:R_n R (n+(n+(2+n)))%N):
  exists (x y z:X) (s t:R),Point x y z s t=p.
Proof.
pose a:=@euclidean_block_split R n (n+(2+n))%N p.
pose b:=@euclidean_block_split R n (2+n)%N a.2.
pose c:=@euclidean_block_split R 2%N n b.2.
pose d:=@euclidean_block_split R 1%N 1%N c.1.
exists a.1;exists b.1;exists c.2;exists (@euclidean_one_project R d.1);exists (@euclidean_one_project R d.2).
have hTime:@euclidean_block_join R 1%N 1%N
    (@euclidean_one_embed R (@euclidean_one_project R d.1),
     @euclidean_one_embed R (@euclidean_one_project R d.2))=c.1.
  by rewrite !euclidean_one_projectK /d euclidean_block_splitK.
rewrite hTime.
by rewrite /c euclidean_block_splitK /b euclidean_block_splitK /a euclidean_block_splitK.
Qed.

(** Source for [current_join_assoc_left_common_composition]: the
    original left iterated F map composed with the
    common source map is exactly H after f in the
    square slot, Federer 4.1.11, p. 366. *)
Lemma current_join_assoc_left_common_composition (p:R_n R (n+(n+(2+n)))%N):
  @current_join_assoc_left_map R n (L p)=H (Slot f p).
Proof.
have[x [y [z [s [t hPoint]]]]]:=current_join_assoc_common_point_cover p.
rewrite -hPoint current_join_assoc_common_coordinates current_join_assoc_left_map_coordinates
  current_join_assoc_square_slot_coordinates current_join_assoc_weighted_map_coordinates.
exact:(@current_join_left_composition R n x y z s t).
Qed.

(** Source for [current_join_assoc_right_common_composition]: the
    original right iterated F map composed with the
    same source map is exactly H after g in the
    square slot, Federer 4.1.11, p. 366. *)
Lemma current_join_assoc_right_common_composition (p:R_n R (n+(n+(2+n)))%N):
  @current_join_assoc_right_map R n (L p)=H (Slot g p).
Proof.
have[x [y [z [s [t hPoint]]]]]:=current_join_assoc_common_point_cover p.
rewrite -hPoint current_join_assoc_common_coordinates current_join_assoc_right_map_coordinates
  current_join_assoc_square_slot_coordinates current_join_assoc_weighted_map_coordinates.
exact:(@current_join_right_composition R n x y z s t).
Qed.
End CurrentJoinAssociativityCommonCompositions.
