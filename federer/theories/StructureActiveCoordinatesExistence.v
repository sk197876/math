(** Federer (1969), 3.3.4, p. 290:
    prove local existence of the active
    coordinate inclusion from the existing
    linear Cartesian block laws. No frame
    or inclusion is selected globally. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanBlockCoordinates EuclideanBlockLinear EuclideanBlockLinearMaps StructureActiveCoordinatesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [structure_active_inclusion_exists]:
    existence of the actual active X
    coordinates in Federer 3.3.4, p. 290.
    The direct Cartesian coordinate witness
    serves only this proof of the prior
    independent inclusion laws. *)
Theorem structure_active_inclusion_exists (R:realType) m k (j:'I_k):
  exists w:Hom (R_n R (1+m)) (R_n R (m+k)),is_structure_active_inclusion j w.
Proof.
pose U:=R_n R (1+m).
pose V:=R_n R (m+k).
pose e:=@coordinate_basis R k j.
pose i0:=lshift m (ord0:'I_1).
pose w (u:U):V:=@euclidean_block_join R m k
  (@euclidean_last_block R 1 m u,(u i0)*:e).
have hLinear:linear w.
  move=>c u v; rewrite /w.
  have hPair:(@euclidean_last_block R 1 m (c*:u+v),(c*:u+v) i0*:e)=
      c*:(@euclidean_last_block R 1 m u,u i0*:e)+
        (@euclidean_last_block R 1 m v,v i0*:e).
    change ((@euclidean_last_block R 1 m (c*:u+v),(c*:u+v) i0*:e)=
      (c*:@euclidean_last_block R 1 m u+@euclidean_last_block R 1 m v,
       c*:(u i0*:e)+v i0*:e)).
    by rewrite euclidean_last_block_linear !ffunE scalerDl scalerA.
  rewrite hPair; exact:euclidean_block_join_linear.
pose W:Hom U V:=@HomMap R U V w (introT (asboolP _) hLinear).
exists W=>u; split.
- change (@euclidean_first_block R m k (w u)=@euclidean_last_block R 1 m u).
  exact:(congr1 fst (@euclidean_block_joinK R m k
    (@euclidean_last_block R 1 m u,u i0*:e))).
- move=>l.
  have hLast:@euclidean_last_block R m k (W u)=u i0*:e.
    exact:(congr1 snd (@euclidean_block_joinK R m k
      (@euclidean_last_block R 1 m u,u i0*:e))).
  rewrite hLast /e /coordinate_basis !ffunE.
  change (u i0*(if l==j then 1 else 0)=
    (if l==j then u (lshift m (ord0:'I_1)) else 0)).
  by case:(l==j); rewrite ?mulr1 ?mulr0.
Qed.
