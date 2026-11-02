(** Federer (1969), 3.2.28(3), pp. 265–266:
    orthonormality of the displayed skew and normal
    tangent directions, in the Hilbert Hom product.
    Their normalization is an independently proved scalar law. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerProductLaws OrthogonalMaps OrthonormalFamilies EuclideanRectangularAdjoint
  EuclideanRankOneInner EuclideanRankOneMixedInner EuclideanHomInnerCharts
  EuclideanSkewIndexCardinality EuclideanStiefelAdaptedDirections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_stiefel_skew_family_orthonormal]:
    the a_ij family with i<j in Federer 3.2.28(3),
    p. 265. Strict ordering removes the reversed-pair
    term; 2c^2=1 gives precisely the printed unit length. *)
Theorem euclidean_stiefel_skew_family_orthonormal (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)) (e:'I_m->R_n R m) c:
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (hom_as_linear g) ->orthonormal_family (@euclidean_inner_product R m) e ->
  2*c*c= 1 ->
  orthonormal_family (@euclidean_hom_inner_product R m n)
    (fun p:euclidean_skew_indices m=>euclidean_stiefel_skew_direction g e c (val p).1 (val p).2).
Proof.
move=>hG hE hC p q.
rewrite (@euclidean_stiefel_skew_direction_pairing R m n g e c
  (val p).1 (val p).2 (val q).1 (val q).2 hG) hC mul1r !hE.
have hDelta (i j k l:'I_m):
    (if i==j then 1:R else 0)*(if k==l then 1 else 0)=
    if (i==j)&&(k==l) then 1 else 0.
  by case:(i==j); case:(k==l); rewrite ?mul0r ?mul1r.
rewrite !hDelta.
have hCross:((val p).1==(val q).2)&&((val p).2==(val q).1)=false.
  apply/negP=>/andP [/eqP hI /eqP hJ].
  have hP:=valP p; have hQ:=valP q.
  change (is_true ((val p).1<(val p).2)%N) in hP.
  change (is_true ((val q).1<(val q).2)%N) in hQ.
  rewrite hI hJ ltnNge in hP.
  by move/negP:hP; apply; exact:ltnW hQ.
rewrite hCross subr0.
have hSame:(((val p).1==(val q).1)&&((val p).2==(val q).2))=(p==q).
  apply/andP/eqP.
  - move=>[/eqP hI /eqP hJ]; apply:val_inj.
    have hEta (z:('I_m*'I_m)%type):z=(z.1,z.2) by case:z.
    by rewrite (hEta (val p)) (hEta (val q)) hI hJ.
  - move=>->; by split; apply/eqP.
by rewrite hSame.
Qed.

(** Source for [euclidean_stiefel_normal_family_orthonormal]:
    the b_ij family of Federer 3.2.28(3), p. 265.
    The source and normal target frames are orthonormal;
    their rank-one pairings are the product of Kronecker
    pairings, as prescribed by 1.7.9, p. 35. *)
Theorem euclidean_stiefel_normal_family_orthonormal (R:realType) m n r
    (e:'I_m->R_n R m) (v:'I_r->R_n R n):
  orthonormal_family (@euclidean_inner_product R m) e ->
  orthonormal_family (@euclidean_inner_product R n) v ->
  orthonormal_family (@euclidean_hom_inner_product R m n)
    (fun p:('I_m*'I_r)%type=>euclidean_rank_one_hom (e p.1) (v p.2)).
Proof.
move=>hE hV [i j] [k l].
rewrite euclidean_rank_one_mixed_inner_pairing hE hV /= xpair_eqE.
by case:(i==k); case:(j==l); rewrite ?mul0r ?mul1r.
Qed.

(** Source for [euclidean_stiefel_skew_normal_orthogonal]:
    every a_ij is perpendicular to every b_kl,
    Federer 3.2.28(3), p. 265. The normal
    target vector is specified by its actual adjoint
    equation, independently of a coordinate choice. *)
Theorem euclidean_stiefel_skew_normal_orthogonal (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)) (e:'I_m->R_n R m) c i j w v:
  euclidean_rectangular_adjoint g v=0 ->
  euclidean_hom_inner_product (euclidean_stiefel_skew_direction g e c i j)
    (euclidean_rank_one_hom w v)=0.
Proof.
move=>hV.
have hPerp x:euclidean_inner_product (g x) v=0.
  rewrite -euclidean_rectangular_adjoint_pairing hV.
  by rewrite (bil0r (inner_bilinear (@euclidean_inner_productP R m))).
rewrite /euclidean_stiefel_skew_direction
  (bilZl (inner_bilinear (@euclidean_hom_inner_productP R m n)))
  (bilBl (inner_bilinear (@euclidean_hom_inner_productP R m n)))
  !euclidean_rank_one_mixed_inner_pairing !hPerp !mulr0 subrr scaler0.
reflexivity.
Qed.
