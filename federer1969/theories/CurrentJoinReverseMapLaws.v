(** Federer (1969), 4.1.11, p. 365: the original
    reversing map p(x,t,y)=(y,1-t,x) preserves the join map F.
    Use only both maps' opaque coordinate laws and the earlier
    Euclidean block inverses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanBlockCoordinates CurrentJoinMapSealed CurrentJoinDomain
  CurrentJoinReverseMapUP CurrentJoinReverseMapSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinReverseMapLaws.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Z := (R_n R (n+(1+n))%N).
Local Notation point := (fun (x:X) (t:R) (y:X)=>
  @euclidean_block_join R n (1+n)%N
    (x,@euclidean_block_join R 1%N n (@euclidean_one_embed R t,y))).
Local Notation p := (@CurrentJoinReverseMap.value R n).
Local Notation F := (@CurrentJoinMap.value R n).

(** Source for [current_join_reverse_map_coordinates]: the
    original reversing values at every Euclidean point,
    supporting the swap calculation of Federer 4.1.11, p. 365. *)
Theorem current_join_reverse_map_coordinates z:
  p z=point
    (@euclidean_block_split R 1%N n (@euclidean_block_split R n (1+n)%N z).2).2
    (1- @euclidean_one_project R
      (@euclidean_block_split R 1%N n (@euclidean_block_split R n (1+n)%N z).2).1)
    (@euclidean_block_split R n (1+n)%N z).1.
Proof.
pose a:=@euclidean_block_split R n (1+n)%N z.
pose b:=@euclidean_block_split R 1%N n a.2.
have hz:point a.1 (@euclidean_one_project R b.1) b.2=z.
  by rewrite euclidean_one_projectK /b euclidean_block_splitK /a euclidean_block_splitK.
by rewrite -{1}hz CurrentJoinReverseMap.laws.
Qed.

(** Source for [current_join_reverse_map_involution]: the
    original p reverses the order and parameter twice to restore
    every point, supporting Federer 4.1.11, p. 365. *)
Theorem current_join_reverse_map_involution:involutive p.
Proof.
move=>z.
pose a:=@euclidean_block_split R n (1+n)%N z.
pose b:=@euclidean_block_split R 1%N n a.2.
have hz:point a.1 (@euclidean_one_project R b.1) b.2=z.
  by rewrite euclidean_one_projectK /b euclidean_block_splitK /a euclidean_block_splitK.
rewrite -hz !CurrentJoinReverseMap.laws.
have ht:1-(1- @euclidean_one_project R b.1)=@euclidean_one_project R b.1 by ring.
by rewrite ht.
Qed.

(** Source for [current_join_reverse_preserves_join_map]:
    F composed with p equals F, the identity used for
    anticommutativity in Federer 4.1.11, p. 365, immediately
    before the displayed reversing pushforward. *)
Theorem current_join_reverse_preserves_join_map z:F (p z)=F z.
Proof.
pose a:=@euclidean_block_split R n (1+n)%N z.
pose b:=@euclidean_block_split R 1%N n a.2.
have hz:point a.1 (@euclidean_one_project R b.1) b.2=z.
  by rewrite euclidean_one_projectK /b euclidean_block_splitK /a euclidean_block_splitK.
rewrite -hz CurrentJoinReverseMap.laws !CurrentJoinMap.laws.
have ht:1-(1- @euclidean_one_project R b.1)=@euclidean_one_project R b.1 by ring.
by rewrite ht addrC.
Qed.

(** Source for [current_join_reverse_domain_image]: p maps
    the original full x,t,y source into itself, supporting the
    reversing pushforward of Federer 4.1.11, p. 365. *)
Definition current_join_reverse_domain_image:
  forall z,@current_join_domain R n z->@current_join_domain R n (p z):=
  fun _ _=>conj Logic.I (conj Logic.I Logic.I).
End CurrentJoinReverseMapLaws.
