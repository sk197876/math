(** Federer (1969), 4.1.27, p. 384:
    the prefix-product map is the original
    cone over the corresponding tail parametrisation.
    This is the map identity behind
    the induction from the ordered cube
    product to the original simplex current
    of 4.1.11, p. 365. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanCartesianMap
  CurrentConeHomotopySealed OrientedSimplexCurrentUP
  SimplexCubeParametrisationUP SimplexCubeParametrisationSealed
  SimplexCubeBarycentricCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [simplex_cube_prefix_first_block]: the leading
    cube coordinate factors from every nonempty
    prefix in the map of 4.1.27,
    p. 384. No coordinate or vertex
    is assumed nonzero. *)
Lemma simplex_cube_prefix_first_block (R:realType) m
    (t:R_n R 1%N) (x:R_n R m) k:
  (k<=m)%N->
  simplex_cube_prefix_product (@euclidean_block_join R 1%N m (t,x)) k.+1=
    t ord0*simplex_cube_prefix_product x k.
Proof.
move=>hK;rewrite /simplex_cube_prefix_product big_mkcond big_ord_recl /=.
have hFirst:@euclidean_block_join R 1%N m (t,x) ord0=t ord0.
  have->:(ord0:'I_(1+m))=lshift m (ord0:'I_1) by apply:val_inj.
  exact:(@euclidean_block_join_left R 1%N m (t,x) ord0).
rewrite hFirst;congr (t ord0*_).
rewrite [RHS]big_mkcond;apply:eq_bigr=>i _.
have hIndex:lift ord0 i=rshift 1%N i by apply:val_inj.
by rewrite /bump leq0n /= ltnS hIndex euclidean_block_join_right.
Qed.

(** Source for [simplex_cube_parametrisation_cone_values]: the original
    prefix-product map sends (t,x) to
    u_0+t(f_tail(x)-u_0), supporting the current-image
    calculation in 4.1.27, p. 384.
    This polynomial identity holds on the
    entire source, including the boundary and
    all degenerate vertex families. *)
Theorem simplex_cube_parametrisation_cone_values (R:realType) n m
    (v:'I_(m.+2)->R_n R n) (t:R_n R 1%N) (x:R_n R m):
  @SimplexCubeParametrisation.value R n m.+1 v
    (@euclidean_block_join R 1%N m (t,x))=
      v ord0+(t ord0)*:
        (@SimplexCubeParametrisation.value R n m (current_simplex_tail v) x-v ord0).
Proof.
pose z:=@euclidean_block_join R 1%N m (t,x).
pose tail:=current_simplex_tail v.
have hEdges (i:'I_m):simplex_consecutive_edge_family v (lift ord0 i)=
    simplex_consecutive_edge_family tail i.
  rewrite /simplex_consecutive_edge_family /tail /current_simplex_tail /current_simplex_face.
  congr (v _-v _);apply:val_inj;by rewrite ?lift0.
have hTail:(\sum_(i:'I_m) simplex_cube_prefix_product z (val (lift ord0 i)).+1*:
      simplex_consecutive_edge_family v (lift ord0 i))=
    (t ord0)*:\sum_(i:'I_m) simplex_cube_prefix_product x (val i).+1*:
      simplex_consecutive_edge_family tail i.
  rewrite scaler_sumr;apply:eq_bigr=>i _.
  rewrite /z (@simplex_cube_prefix_first_block R m t x (val i).+1 (ltn_ord i)) hEdges.
  by rewrite scalerA.
rewrite (@SimplexCubeParametrisation.laws R n m.+1 v z) big_ord_recl /= hTail
  /z (@simplex_cube_prefix_first_block R m t x 0%N (leq0n m))
  simplex_cube_prefix_zero mulr1 (@SimplexCubeParametrisation.laws R n m tail x).
rewrite /simplex_consecutive_edge_family /= /tail /current_simplex_tail /current_simplex_face.
have->:widen_ord (leqnSn m.+1) (ord0:'I_m.+1)=ord0 by apply:val_inj.
by rewrite -scalerDr addrAC.
Qed.

(** Source for [simplex_cube_parametrisation_cone_composite]: the original
    map equals the already opaque contraction
    composed with identity times the tail
    map, supporting 4.1.27, p. 384.
    This is equality on the whole
    source, not only on a support. *)
Theorem simplex_cube_parametrisation_cone_composite (R:realType) n m
    (v:'I_(m.+2)->R_n R n):
  @SimplexCubeParametrisation.value R n m.+1 v=
    (fun z=>@CurrentConeHomotopy.value R n (v ord0)
      (@euclidean_cartesian_map R 1%N m 1%N n (fun t=>t)
        (@SimplexCubeParametrisation.value R n m (current_simplex_tail v)) z)).
Proof.
apply:funext=>z.
pose p:=@euclidean_block_split R 1%N m z.
have hPoint:@euclidean_block_join R 1%N m
    (@euclidean_one_embed R (@euclidean_one_project R p.1),p.2)=z.
  by rewrite euclidean_one_projectK /p euclidean_block_splitK.
rewrite -{1 2}hPoint simplex_cube_parametrisation_cone_values
  /euclidean_cartesian_map !euclidean_block_joinK /= CurrentConeHomotopy.laws.
rewrite /euclidean_one_embed ffunE.
by rewrite scalerBr scalerBl scale1r addrA addrAC.
Qed.
