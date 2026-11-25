(** Federer (1969), 4.1.11, p. 366: the
    original H, f and g coordinate identities, including
    both printed compositions with the join map F.
    Use only the sealed coordinate formulas. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import Hom ConcatenatedFamilies GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps CurrentJoinMapSealed
  CurrentJoinAssociatorMapsUP CurrentJoinAssociatorMapsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinAssociatorMapsLaws.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Z := (R_n R (n+(n+(n+3)))%N).
Local Notation H := (@CurrentJoinAssociatorMaps.barycentre R n).
Local Notation f := (@CurrentJoinAssociatorMaps.left_triangle R).
Local Notation g := (@CurrentJoinAssociatorMaps.right_triangle R).
Local Notation F := (@CurrentJoinMap.value R n).
Local Notation point := (fun (x:X) (t:R) (y:X)=>@euclidean_block_join R n (1+n)%N
  (x,@euclidean_block_join R 1%N n (@euclidean_one_embed R t,y))).
Local Notation four := (fun (x y z:X) (w:R_n R 3%N)=>@euclidean_block_join R n (n+(n+3))%N
  (x,@euclidean_block_join R n (n+3)%N (y,@euclidean_block_join R n 3%N (z,w)))).
Local Notation times := (fun (s t:R)=>@euclidean_block_join R 1%N 1%N
  (@euclidean_one_embed R s,@euclidean_one_embed R t)).
Local Notation first := (@euclidean_first_block_map R n (n+(n+3))%N).
Local Notation rest := (@euclidean_last_block_map R n (n+(n+3))%N).
Local Notation second := (hom_comp (@euclidean_first_block_map R n (n+3)%N) rest).
Local Notation thirdrest := (hom_comp (@euclidean_last_block_map R n (n+3)%N) rest).
Local Notation third := (hom_comp (@euclidean_first_block_map R n 3%N) thirdrest).
Local Notation weights := (hom_comp (@euclidean_last_block_map R n 3%N) thirdrest).

(** Source for [current_join_barycentre_coordinates]: the
    original H formula holds at every point in its
    Euclidean domain, supporting Federer 4.1.11, p. 366. *)
Lemma current_join_barycentre_coordinates (p:Z):
  H p=weights p ord0*:first p+weights p (lift ord0 ord0)*:second p+
    weights p (lift ord0 (lift ord0 ord0))*:third p.
Proof.
have hThird:@euclidean_block_join R n 3%N (third p,weights p)=thirdrest p.
  exact:euclidean_block_splitK.
have hSecond:@euclidean_block_join R n (n+3)%N (second p,thirdrest p)=rest p.
  exact:euclidean_block_splitK.
have hFirst:four (first p) (second p) (third p) (weights p)=p.
  rewrite hThird hSecond;exact:euclidean_block_splitK.
by rewrite -{1}hFirst CurrentJoinAssociatorMaps.barycentre_laws.
Qed.

(** Source for [current_join_left_composition]: the literal
    F(F(x,t_1,y),t_2,z)=H(x,y,z,f(t_1,t_2)),
    Federer 4.1.11, p. 366, including dimension zero
    and unrestricted real time coordinates. *)
Lemma current_join_left_composition (x y z:X) s t:
  F (point (F (point x s y)) t z)=H (four x y z (f (times s t))).
Proof.
rewrite !CurrentJoinMap.laws CurrentJoinAssociatorMaps.barycentre_laws
  CurrentJoinAssociatorMaps.left_triangle_laws.
apply/ffunP=>k.
rewrite /times /euclidean_block_join /euclidean_one_embed /coordinate_basis !ffunE /=.
have hZero:(ord0:'I_2)=lshift 1%N (ord0:'I_1) by apply:val_inj.
have hOne:(lift ord0 (ord0:'I_1):'I_2)=rshift 1%N (ord0:'I_1) by apply:val_inj.
have hFirst:concatenate_family [ffun _:'I_1=>s] [ffun _:'I_1=>t] (ord0:'I_2)=s.
  by rewrite hZero concatenate_family_l ffunE.
have hLast:concatenate_family [ffun _:'I_1=>s] [ffun _:'I_1=>t] (lift ord0 (ord0:'I_1))=t.
  by rewrite hOne concatenate_family_r ffunE.
rewrite hFirst hLast !scaler0 !addr0 !add0r.
change ((1-t)*((1-s)*(x k)+s*(y k))+t*(z k)=
  (((1-s)*(1-t))*1)*(x k)+((s*(1-t))*1)*(y k)+(t*1)*(z k)).
ring.
Qed.

(** Source for [current_join_right_composition]: the literal
    F(x,t_1,F(y,t_2,z))=H(x,y,z,g(t_1,t_2)),
    Federer 4.1.11, p. 366. This coordinate identity
    assumes no associativity of currents. *)
Lemma current_join_right_composition (x y z:X) s t:
  F (point x s (F (point y t z)))=H (four x y z (g (times s t))).
Proof.
rewrite !CurrentJoinMap.laws CurrentJoinAssociatorMaps.barycentre_laws
  CurrentJoinAssociatorMaps.right_triangle_laws.
apply/ffunP=>k.
rewrite /times /euclidean_block_join /euclidean_one_embed /coordinate_basis !ffunE /=.
have hZero:(ord0:'I_2)=lshift 1%N (ord0:'I_1) by apply:val_inj.
have hOne:(lift ord0 (ord0:'I_1):'I_2)=rshift 1%N (ord0:'I_1) by apply:val_inj.
have hFirst:concatenate_family [ffun _:'I_1=>s] [ffun _:'I_1=>t] (ord0:'I_2)=s.
  by rewrite hZero concatenate_family_l ffunE.
have hLast:concatenate_family [ffun _:'I_1=>s] [ffun _:'I_1=>t] (lift ord0 (ord0:'I_1))=t.
  by rewrite hOne concatenate_family_r ffunE.
rewrite hFirst hLast !scaler0 !addr0 !add0r.
change ((1-s)*(x k)+s*((1-t)*(y k)+t*(z k))=
  ((1-s)*1)*(x k)+((s*(1-t))*1)*(y k)+((s*t)*1)*(z k)).
ring.
Qed.
End CurrentJoinAssociatorMapsLaws.
