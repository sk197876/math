(** Federer (1969), 4.1.11, p. 366: the
    original barycentric and triangle coordinate formulas
    determine actual maps. Constructions serve only as
    existence proofs and will be hidden by the seal. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanOneCoordinate
  EuclideanBlockCoordinates CurrentJoinAssociatorMapsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_join_barycentre_exists]: existence
    of the original printed H, supporting Federer
    4.1.11, p. 366. No algebraic current conclusion
    is part of its independent specification. *)
Lemma current_join_barycentre_exists (R:realType) n:
  exists H:R_n R (n+(n+(n+3)))%N->R_n R n,
    @is_current_join_barycentre R n H.
Proof.
exists (fun p=>
  let a:=euclidean_block_split p in
  let b:=euclidean_block_split a.2 in
  let c:=euclidean_block_split b.2 in
  c.2 ord0*:a.1+c.2 (lift ord0 ord0)*:b.1+
    c.2 (lift ord0 (lift ord0 ord0))*:c.1).
move=>x y z w.
rewrite euclidean_block_joinK;cbn beta iota zeta.
rewrite euclidean_block_joinK;cbn beta iota zeta.
by rewrite euclidean_block_joinK.
Qed.

(** Source for [current_join_left_triangle_map_exists]: existence
    of the original printed f, supporting Federer
    4.1.11, p. 366. *)
Lemma current_join_left_triangle_map_exists (R:realType):
  exists f:R_n R 2%N->R_n R 3%N,@is_current_join_left_triangle_map R f.
Proof.
exists (fun t:R_n R 2%N=>((1-t ord0)*(1-t (lift ord0 ord0)))*:@coordinate_basis R 3%N ord0+
  (t ord0*(1-t (lift ord0 ord0)))*:@coordinate_basis R 3%N (lift ord0 ord0)+
  t (lift ord0 ord0)*:@coordinate_basis R 3%N (lift ord0 (lift ord0 ord0))).
by [].
Qed.

(** Source for [current_join_right_triangle_map_exists]: existence
    of the original printed g, supporting Federer
    4.1.11, p. 366. *)
Lemma current_join_right_triangle_map_exists (R:realType):
  exists g:R_n R 2%N->R_n R 3%N,@is_current_join_right_triangle_map R g.
Proof.
exists (fun t:R_n R 2%N=>(1-t ord0)*:@coordinate_basis R 3%N ord0+
  (t ord0*(1-t (lift ord0 ord0)))*:@coordinate_basis R 3%N (lift ord0 ord0)+
  (t ord0*t (lift ord0 ord0))*:@coordinate_basis R 3%N (lift ord0 (lift ord0 ord0))).
by [].
Qed.
