(** Federer (1969), 3.2.28(3), p. 266:
    the four displayed images under DS(h)=h alpha.
    Rank-one precomposition and the adapted hyperplane
    laws prove these identities for the actual Hom maps. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP OrthogonalMaps EuclideanRectangularAdjoint
  EuclideanHyperplaneNormalUP EuclideanRankOneInner EuclideanFrameRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_rank_one_precomposition]: the
    tensor action N alpha tensor I in Federer
    3.2.28(3), pp. 265–266, evaluated on
    an actual rank-one Hom map. *)
Lemma euclidean_rank_one_precomposition (R:realType) k m n
    (alpha:Hom (R_n R k) (R_n R m)) w (v:R_n R n):
  hom_comp (euclidean_rank_one_hom w v) alpha=
    euclidean_rank_one_hom (euclidean_rectangular_adjoint alpha w) v.
Proof.
apply:hom_ext=>x.
change (euclidean_inner_product (alpha x) w*:v=
  euclidean_inner_product x (euclidean_rectangular_adjoint alpha w)*:v).
by rewrite euclidean_rectangular_adjoint_pairing.
Qed.

(** Source for [euclidean_rank_one_zero_source]: a
    vanishing restricted covector gives the zero rank-one
    map, supporting the fourth differential formula
    in Federer 3.2.28(3), p. 266. *)
Lemma euclidean_rank_one_zero_source (R:realType) m n (v:R_n R n):
  @euclidean_rank_one_hom R m n 0 v=0.
Proof.
apply:hom_ext=>x.
change (euclidean_inner_product x 0*:v=0).
by rewrite (bil0r (inner_bilinear (@euclidean_inner_productP R m))) scale0r.
Qed.

(** Source for [euclidean_forgetful_skew_image]:
    DS(a_ij)=c_ij when both source directions
    lie in im alpha, Federer 3.2.28(3), p. 266.
    The scalar c retains the exact displayed normalization. *)
Theorem euclidean_forgetful_skew_image (R:realType) k m n
    (alpha:Hom (R_n R k) (R_n R m)) (g:Hom (R_n R m) (R_n R n)) c u z:
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R m)
    (hom_as_linear alpha) ->
  hom_comp (c*:(euclidean_rank_one_hom (alpha u) (g (alpha z))-
    euclidean_rank_one_hom (alpha z) (g (alpha u)))) alpha=
  c*:(euclidean_rank_one_hom u ((hom_comp g alpha) z)-
    euclidean_rank_one_hom z ((hom_comp g alpha) u)).
Proof.
move=>hA.
apply:hom_ext=>x.
change (c*:(euclidean_inner_product (alpha x) (alpha u)*:g (alpha z)-
  euclidean_inner_product (alpha x) (alpha z)*:g (alpha u))=
  c*:(euclidean_inner_product x u*:g (alpha z)-euclidean_inner_product x z*:g (alpha u))).
by rewrite !hA.
Qed.

(** Source for [euclidean_forgetful_cross_image]:
    DS(a_i,m)=2^(-1/2)d_i,m, Federer
    3.2.28(3), p. 266. The vanishing
    second term follows from the actual normal law. *)
Theorem euclidean_forgetful_cross_image (R:realType) k n
    (alpha:Hom (R_n R k) (R_n R k.+1)) w
    (g:Hom (R_n R k.+1) (R_n R n)) c u:
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R k.+1)
    (hom_as_linear alpha) ->is_euclidean_hyperplane_normal alpha w ->
  hom_comp (c*:(euclidean_rank_one_hom (alpha u) (g w)-
    euclidean_rank_one_hom w (g (alpha u)))) alpha=
    c*:euclidean_rank_one_hom u (g w).
Proof.
move=>hA hW; apply:hom_ext=>x.
change (c*:(euclidean_inner_product (alpha x) (alpha u)*:g w-
  euclidean_inner_product (alpha x) w*:g (alpha u))=
  c*:(euclidean_inner_product x u*:g w)).
rewrite hA -euclidean_rectangular_adjoint_pairing
  (hyperplane_normal_perpendicular hW)
  (bil0r (inner_bilinear (@euclidean_inner_productP R k))) scale0r subr0.
reflexivity.
Qed.

(** Source for [euclidean_forgetful_normal_image]:
    DS(b_ij)=d_ij for i<m<j, Federer
    3.2.28(3), p. 266. The formula
    holds for every target vector before normality is used. *)
Theorem euclidean_forgetful_normal_image (R:realType) k m n
    (alpha:Hom (R_n R k) (R_n R m)) u (v:R_n R n):
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R m)
    (hom_as_linear alpha) ->
  hom_comp (euclidean_rank_one_hom (alpha u) v) alpha=euclidean_rank_one_hom u v.
Proof.
move=>hA; apply:hom_ext=>x.
change (euclidean_inner_product (alpha x) (alpha u)*:v=euclidean_inner_product x u*:v).
by rewrite hA.
Qed.

(** Source for [euclidean_forgetful_normal_kernel]:
    DS(b_m,j)=0 for m<j, Federer 3.2.28(3),
    p. 266. The actual covector restriction
    vanishes on im alpha, including k=0. *)
Theorem euclidean_forgetful_normal_kernel (R:realType) k n
    (alpha:Hom (R_n R k) (R_n R k.+1)) w (v:R_n R n):
  is_euclidean_hyperplane_normal alpha w ->
  hom_comp (euclidean_rank_one_hom w v) alpha=0.
Proof.
move=>hW; rewrite euclidean_rank_one_precomposition
  (hyperplane_normal_perpendicular hW).
exact:euclidean_rank_one_zero_source.
Qed.
