(** Federer (1969), 3.2.38, p. 274: finite equal cubes cover the
    enclosing coordinate box, and each is an actual cube of side h. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanCoordinateCubeUP EqualCoordinateCubeGridUP
  ScalarIntervalPartition ScalarIntervalPartitionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Grid.
Variable R:realType.
Variables n k:nat.
Variable a:R_n R n.
Variable h:R.
Variable Q:coordinate_cube_grid_indices n k->
  set (inner_metric_space (@euclidean_inner_productP R n)).
Hypothesis hQ:is_equal_coordinate_cube_grid k a h Q.

(** Source for [equal_coordinate_grid_cell_cube]: each grid member
    has exactly the prescribed side h, Federer 3.2.38, p. 274. *)
Lemma equal_coordinate_grid_cell_cube (s:coordinate_cube_grid_indices n k):
  is_euclidean_coordinate_cube ([ffun i=>a i+(s i)%:R*h]:R_n R n) h (Q s).
Proof.
split; first exact:hQ.2.1.
move=>x; split=>hx.
- move=>i; have hi:=(hQ.2.2 s x).1 hx i; rewrite ffunE.
  by rewrite -addn1 natrD mulrDl mul1r addrA in hi.
- apply:(hQ.2.2 s x).2=>j.
  have hi:=hx j; rewrite ffunE in hi.
  by rewrite -addn1 natrD mulrDl mul1r addrA.
Qed.

(** Source for [equal_coordinate_grid_within_box]: all subcubes lie
    in the original enclosing cube, Federer 3.2.38, p. 274. *)
Lemma equal_coordinate_grid_within_box (s:coordinate_cube_grid_indices n k) x:Q s x ->
  forall i,a i<=x i<=a i+k%:R*h.
Proof.
move=>hx i; have /andP[hl hu]:=(hQ.2.2 s x).1 hx i.
have hLow:0<=(s i)%:R*h by apply:mulr_ge0; [exact:ler0n|exact:hQ.2.1].
have hHigh:((s i).+1)%:R*h<=k%:R*h.
  apply:ler_wpM2r; first exact:hQ.2.1; by rewrite ler_nat; exact:ltn_ord.
apply/andP; split; lra.
Qed.

(** Source for [equal_coordinate_grid_covers_box]: the finite closed
    cubes cover their original box, including every boundary point,
    Federer 3.2.38, p. 274. The already opaque equal scalar
    partition supplies each cell index; no floor is imported. *)
Lemma equal_coordinate_grid_covers_box (x:inner_metric_space (@euclidean_inner_productP R n)):
  (forall i,a i<=x i<=a i+k%:R*h) ->exists s,Q s x.
Proof.
move=>hx.
have hk:(0<k)%N:=hQ.1.
have hkR:(0<(k%:R:R))%R by rewrite ltr0n.
have hk0:(k%:R:R)!=0:=lt0r_neq0 hkR.
have hc:0<=k%:R*h by apply:mulr_ge0; [exact:ler0n|exact:hQ.2.1].
pose node:=@equal_interval_partition R (k%:R*h) k hc hk.
have hp:=@equal_interval_partition_specification R (k%:R*h) k hc hk.
have hWidth:(k%:R*h)/k%:R=h by rewrite mulrAC mulfV // mul1r.
have hCell i:exists j:'I_k,a i+j%:R*h<=x i<=a i+(j.+1)%:R*h.
  have /andP[hl hu]:=hx i.
  have hi:0<=x i-a i<=k%:R*h by apply/andP; split; lra.
  have [j /andP[hlo hhi]]:=equal_interval_cell_cover hp hi.
  rewrite (equal_interval_node_expansion hp (ltnW (ltn_ord j))) hWidth in hlo.
  rewrite (equal_interval_node_expansion hp (ltn_ord j)) hWidth in hhi.
  exists j; apply/andP; split; lra.
pose s i:=projT1 (cid (hCell i)).
exists [ffun i=>s i]; apply:(hQ.2.2 _ x).2=>i; rewrite ffunE.
exact:(projT2 (cid (hCell i))).
Qed.

(** Source for [equal_coordinate_grid_distinct_overlap]: distinct
    cubes meet in a coordinate hyperplane, giving disjoint interiors
    and null overlaps in Federer 3.2.38, p. 274. Dimension zero
    is retained: its one-element index family has no distinct pair. *)
Lemma equal_coordinate_grid_distinct_overlap (s t:coordinate_cube_grid_indices n k):s!=t ->exists (i:'I_n) b,
  (Q s `&` Q t) `<=` [set x|x i=b].
Proof.
move=>hst.
have [i hi]:exists i,s i!=t i.
  apply:contrapT=>hn; apply:(elimN eqP hst); apply/ffunP=>i.
  case:(eqVneq (s i) (t i))=>// hne; exfalso; apply:hn; by exists i.
have hval:(s i:nat)!=(t i:nat).
  apply/eqP=>he; apply:(elimN eqP hi); exact:val_inj he.
case:(ltngtP (s i:nat) (t i:nat))=>[hlt|hgt|heq].
- exists i,(a i+((s i).+1)%:R*h)=>x [hs ht].
  have /andP[hsl hsu]:=(hQ.2.2 s x).1 hs i.
  have /andP[htl htu]:=(hQ.2.2 t x).1 ht i.
  have hSep:((s i).+1)%:R*h<=(t i)%:R*h.
    apply:ler_wpM2r; first exact:hQ.2.1; by rewrite ler_nat.
  apply/eqP; rewrite eq_le; apply/andP; split; lra.
- exists i,(a i+(s i)%:R*h)=>x [hs ht].
  have /andP[hsl hsu]:=(hQ.2.2 s x).1 hs i.
  have /andP[htl htu]:=(hQ.2.2 t x).1 ht i.
  have hSep:((t i).+1)%:R*h<=(s i)%:R*h.
    apply:ler_wpM2r; first exact:hQ.2.1; by rewrite ler_nat.
  apply/eqP; rewrite eq_le; apply/andP; split; lra.
- by move:hval; rewrite heq eqxx.
Qed.
End Grid.
