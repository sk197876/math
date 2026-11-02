(** Federer (1969), 3.2.28(3), printed p. 266:
    a forgetful-map fibre is parametrised exactly by
    unit normal vectors to the restricted target frame.
    The orthogonality condition is derived from the
    abstract extension laws and the adapted splitting. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerProductLaws OrthogonalMaps AdjointLaws EuclideanRectangularAdjoint
  EuclideanHyperplaneNormalUP EuclideanHyperplaneSplitting EuclideanFrameExtensionUP
  EuclideanFrameExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_frame_normal_pairing]: orthogonality
    of the target adapted frame and its last vector,
    supporting the sphere-fibre identification of Federer
    3.2.28(3), p. 266. *)
Lemma euclidean_frame_normal_pairing (R:realType) k n
    (beta:Hom (R_n R k) (R_n R n)) v:
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R n)
    (hom_as_linear beta) ->euclidean_rectangular_adjoint beta v=0 ->
  euclidean_inner_product v v= 1 ->forall u z (c d:R),
    euclidean_inner_product (beta u+c*:v) (beta z+d*:v)=
      euclidean_inner_product u z+c*d.
Proof.
move=>hB hV hUnit u z c d.
have hCross a:euclidean_inner_product (beta a) v=0.
  rewrite -euclidean_rectangular_adjoint_pairing hV.
  by rewrite (bil0r (inner_bilinear (@euclidean_inner_productP R k))).
have hOther a:euclidean_inner_product v (beta a)=0.
  by rewrite (inner_symmetric (@euclidean_inner_productP R n)) hCross.
rewrite (bilDl (inner_bilinear (@euclidean_inner_productP R n)))
  !(bilDr (inner_bilinear (@euclidean_inner_productP R n)))
  !(bilZl (inner_bilinear (@euclidean_inner_productP R n)))
  !(bilZr (inner_bilinear (@euclidean_inner_productP R n))).
rewrite hB hCross hOther hUnit.
change (euclidean_inner_product u z+d*0+(c*0+c*(d*1))=
  euclidean_inner_product u z+c*d).
by rewrite !mulr0 mulr1 !addr0 !add0r.
Qed.

(** Source for [euclidean_frame_extension_orthogonal_iff]:
    the actual fibre consists exactly of unit vectors in
    the orthogonal complement of the restricted frame,
    Federer 3.2.28(3), p. 266. Source and target
    orthogonality are proved from their inner products;
    the conclusion is valid also for k=0. *)
Theorem euclidean_frame_extension_orthogonal_iff (R:realType) k n
    (alpha:Hom (R_n R k) (R_n R k.+1)) w
    (beta:Hom (R_n R k) (R_n R n)) v
    (h:Hom (R_n R k.+1) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R k.+1)
    (hom_as_linear alpha) ->is_euclidean_hyperplane_normal alpha w ->
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R n)
    (hom_as_linear beta) ->is_euclidean_frame_extension alpha w beta v h ->
  (is_orthogonal_map (@euclidean_inner_product R k.+1) (@euclidean_inner_product R n)
    (hom_as_linear h) <->euclidean_rectangular_adjoint beta v=0 /\
      euclidean_inner_product v v= 1).
Proof.
move=>hA hW hB hExt; split.
- move=>hH; split.
  + apply:(inner_vectors_ext (@euclidean_inner_productP R k))=>x.
    rewrite (bil0r (inner_bilinear (@euclidean_inner_productP R k)))
      euclidean_rectangular_adjoint_pairing.
    have hAlpha:=congr1 (fun F:Hom (R_n R k) (R_n R n)=>F x)
      (frame_extension_restriction hExt).
    change (h (alpha x)=beta x) in hAlpha.
    rewrite -hAlpha -(frame_extension_normal_value hExt) hH
      -euclidean_rectangular_adjoint_pairing (hyperplane_normal_perpendicular hW).
    by rewrite (bil0r (inner_bilinear (@euclidean_inner_productP R k))).
  + rewrite -(frame_extension_normal_value hExt) hH.
    exact:hyperplane_normal_unit hW.
- move=>[hNormal hUnit] x y.
  change (euclidean_inner_product (h x) (h y)=euclidean_inner_product x y).
  rewrite (@euclidean_frame_extension_evaluation R k n alpha w beta v h hA hW hExt x)
    (@euclidean_frame_extension_evaluation R k n alpha w beta v h hA hW hExt y).
  rewrite (euclidean_frame_normal_pairing hB hNormal hUnit).
  symmetry; exact:euclidean_hyperplane_inner_decomposition hA hW x y.
Qed.
