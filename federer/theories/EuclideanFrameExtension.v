(** Federer (1969), 3.2.28(3), printed pp. 265–266:
    existence and uniqueness of a linear extension with
    the prescribed frame restriction and normal value.
    Later arguments use the abstract extension laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerProductLaws OrthogonalMaps AdjointCriteria EuclideanRectangularAdjoint
  EuclideanHyperplaneNormalUP EuclideanHyperplaneSplitting EuclideanFrameExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_frame_extension_evaluation]: the
    value of a fibre element in its adapted source
    decomposition, supporting Federer 3.2.28(3),
    pp. 265–266. It is derived from the abstract
    extension laws, independently of an implementation. *)
Theorem euclidean_frame_extension_evaluation (R:realType) k n
    (alpha:Hom (R_n R k) (R_n R k.+1)) w
    (beta:Hom (R_n R k) (R_n R n)) v (h:Hom (R_n R k.+1) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R k.+1)
    (hom_as_linear alpha) ->is_euclidean_hyperplane_normal alpha w ->
  is_euclidean_frame_extension alpha w beta v h ->forall x,
    h x=beta (euclidean_rectangular_adjoint alpha x)+euclidean_inner_product x w*:v.
Proof.
move=>hA hW hExt x.
have hSplit:=euclidean_hyperplane_decomposition hA hW x.
have hV:=congr1 h hSplit; rewrite linearD linearZ in hV.
change (h x=h (alpha (euclidean_rectangular_adjoint alpha x))+euclidean_inner_product x w*:h w) in hV.
rewrite (frame_extension_normal_value hExt) in hV.
have hAlpha:=congr1 (fun f:Hom (R_n R k) (R_n R n)=>f (euclidean_rectangular_adjoint alpha x))
  (frame_extension_restriction hExt).
change (h (alpha (euclidean_rectangular_adjoint alpha x))=beta (euclidean_rectangular_adjoint alpha x)) in hAlpha.
by rewrite hAlpha in hV.
Qed.

(** Source for [euclidean_frame_extension_exists_unique]:
    the unique fibre extension with prescribed last vector,
    Federer 3.2.28(3), pp. 265–266. The displayed
    direct-sum formula is used only to prove existence;
    its abstract restriction and value laws determine it. *)
Theorem euclidean_frame_extension_exists_unique (R:realType) k n
    (alpha:Hom (R_n R k) (R_n R k.+1)) w
    (beta:Hom (R_n R k) (R_n R n)) v:
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R k.+1)
    (hom_as_linear alpha) ->is_euclidean_hyperplane_normal alpha w ->
  exists h,is_euclidean_frame_extension alpha w beta v h /\
    forall H,is_euclidean_frame_extension alpha w beta v H ->H=h.
Proof.
move=>hA hW.
pose p:=euclidean_rectangular_adjoint alpha.
pose F:=fun x:R_n R k.+1=>beta (p x)+euclidean_inner_product x w*:v.
have hLin:linear F.
  move=>c x y; rewrite /F !linearP /=.
  rewrite (bilDl (inner_bilinear (@euclidean_inner_productP R k.+1)))
    (bilZl (inner_bilinear (@euclidean_inner_productP R k.+1))) scalerDl -scalerA.
  rewrite scalerDr; exact:addrACA.
pose h:=@HomMap R (R_n R k.+1) (R_n R n) F (introT (asboolP _) hLin).
have hCan:cancel alpha p:=(orthogonal_iff_adjoint_left_inverse
  (@euclidean_inner_productP R k) (euclidean_rectangular_adjoint_pairing alpha)).1 hA.
have hExt:is_euclidean_frame_extension alpha w beta v h.
  constructor.
  - apply:hom_ext=>x.
    change (beta (p (alpha x))+euclidean_inner_product (alpha x) w*:v=beta x).
    rewrite hCan -euclidean_rectangular_adjoint_pairing
      (hyperplane_normal_perpendicular hW)
      (bil0r (inner_bilinear (@euclidean_inner_productP R k))) scale0r addr0.
    reflexivity.
  - change (beta (p w)+euclidean_inner_product w w*:v=v).
    by rewrite (hyperplane_normal_perpendicular hW) linear0
      (hyperplane_normal_unit hW) scale1r add0r.
exists h; split; first exact hExt.
move=>H hH; apply:hom_ext=>x.
rewrite (@euclidean_frame_extension_evaluation R k n alpha w beta v H hA hW hH x).
reflexivity.
Qed.
