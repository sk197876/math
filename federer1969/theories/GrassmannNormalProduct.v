(** Federer (1969), 3.1.21, p. 234: the product of
    a plane with its perpendicular complement has ambient dimension.
    Reuse only the earlier abstract orthogonal-projection laws;
    no projection implementation or new choice object is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear ModuleQuotient SubspaceSums SubspaceCarrier LinearBasis
  GrassmannSubspaces GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerProductUP InnerProductLaws
  GrassmannHomogeneousSpace EuclideanBlockLinearMaps LinearRankUP LinearInjectiveRank.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [grassmann_normal_product_exists]: supporting
    the n-dimensional normal bundle assertion in Federer 3.1.21,
    p. 234. An orthogonal projection maps x to
    (P x,x-P x), a linear isomorphism onto Z times Z-perp.
    Its actual range basis has n vectors, including n=0. *)
Theorem grassmann_normal_product_exists (R:realType) n mu
    (Z:G (R_n R n) mu) : exists H:G (R_n R (n+n)) n,forall x,
    grassmann_val H x <-> grassmann_val Z (@euclidean_first_block_map R n n x) /\
      forall w,grassmann_val Z w ->
        @euclidean_inner_product R n (@euclidean_last_block_map R n n x) w=0.
Proof.
pose X:= R_n R n.
pose Y:= R_n R (n+n).
pose B:=@euclidean_inner_product R n.
pose hB:=@euclidean_inner_productP R n.
have [P [hP1 hP2]]:=@grassmann_projection_exists R (R_n R mu) X
  (@euclidean_inner_product R mu) B (@euclidean_inner_productP R mu) hB mu
  (@coordinate_basis R mu) (@coordinate_basisP R mu) Z.
pose p:=@euclidean_first_block_map R n n.
pose q:=@euclidean_last_block_map R n n.
pose i:=@euclidean_first_injection_map R n n.
pose j:=@euclidean_last_injection_map R n n.
pose I:= hom_of_linear (linear_id X).
pose L:= hom_comp i P+hom_comp j (I-P).
have hpi y:p (i y)= y:=@euclidean_first_block_injectionK R n n y.
have hpj y:p (j y)=0:=@euclidean_first_block_last_injection R n n y.
have hqi y:q (i y)=0:=@euclidean_last_block_first_injection R n n y.
have hqj y:q (j y)= y:=@euclidean_last_block_injectionK R n n y.
have hLe x:L x= i (P x)+j (x-P x) by [].
have hLp x:p (L x)= P x by rewrite hLe (linD (hom_linear p)) hpi hpj addr0.
have hLq x:q (L x)= x-P x by rewrite hLe (linD (hom_linear q)) hqi hqj add0r.
have hK:cancel L (fun z=>p z+q z).
  move=>x; by rewrite hLp hLq addrC subrK.
have hLi:injective L:= can_inj hK.
have hr:=@linear_injective_rank R X Y n (@coordinate_basis R n) (@coordinate_basisP R n)
  (n+n) (@coordinate_basis R (n+n)) (@coordinate_basisP R (n+n)) L hLi.
pose H:=@GrassmannSubspace R Y n (range_subspace (hom_as_linear L)) hr.
exists H=>y; split.
- move=>[x he]; change (y= L x) in he; rewrite he hLp hLq.
  split; first exact: hP1.
  exact: hP2.
- move=>[hyZ hyperp].
  pose x:= p y+q y.
  have hz:grassmann_val Z (p y-P x):= subspace_sub hyZ (hP1 x).
  have hperp:forall w,grassmann_val Z w -> B (p y-P x) w=0.
    move=>w hw.
    have heq:p y-P x=(x-P x)-q y.
      by rewrite /x addrAC addrK.
    have hlin:B ((x-P x)-q y) w=B (x-P x) w-B (q y) w.
      exact (@bilBl R X X R^o B (inner_bilinear hB) (x-P x) (q y) w).
    have hw0:B (q y) w=0:=hyperp w hw.
    by rewrite heq hlin (hP2 x w hw) hw0 subrr.
  have hs:B (p y-P x) (p y-P x)=0:= hperp _ hz.
  have hd:p y-P x=0.
    apply/eqP; rewrite -(inner_self_eq0 hB); apply/eqP; exact hs.
  have hPx:P x= p y.
    apply/eqP; by rewrite eq_sym -subr_eq0 hd eqxx.
  have hres:x-P x= q y by rewrite /x hPx addrAC subrr add0r.
  exists x; change (y= L x).
  rewrite hLe hres hPx.
  exact (@euclidean_block_linear_decomposition R n n y).
Qed.
