(** Federer (1969), 3.2.28(3), printed p. 266:
    every fibre of S(g)=g alpha is isometric to
    the unit sphere in R^(n-m+1). Source-normal and
    target-normal choices occur only inside existence. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerNorm InnerMetric OrthogonalMaps EuclideanRectangularAdjoint EuclideanHomInnerCharts
  EuclideanFrameComplementUP EuclideanFrameComplementExistence EuclideanHyperplaneNormalUP
  EuclideanHyperplaneNormalExistence EuclideanFrameExtensionUP EuclideanFrameExtension
  EuclideanFrameExtensionIsometry EuclideanFrameFibreIsometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_forgetful_fibre_isometric_parametrisation]:
    the actual spherical fibre in Federer 3.2.28(3),
    p. 266. For m=k+1 the sphere ambient dimension
    is n-k=n-m+1. Both inverse and full distance
    laws are proved, rather than added as fibre axioms. *)
Theorem euclidean_forgetful_fibre_isometric_parametrisation (R:realType) k n
    (alpha:Hom (R_n R k) (R_n R k.+1))
    (beta:Hom (R_n R k) (R_n R n)):
  (k<=n)%N ->
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R k.+1)
    (hom_as_linear alpha) ->
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R n)
    (hom_as_linear beta) ->
  exists (F:R_n R (n-k)->Hom (R_n R k.+1) (R_n R n))
    (G:Hom (R_n R k.+1) (R_n R n)->R_n R (n-k)),
    cancel F G /\
    (forall x y,mdist (F x:inner_metric_space (@euclidean_hom_inner_productP R k.+1 n)) (F y)=
      mdist (x:inner_metric_space (@euclidean_inner_productP R (n-k))) y) /\
    F @` [set z|inner_norm (@euclidean_inner_productP R (n-k)) z= 1]=
      [set h|is_orthogonal_map (@euclidean_inner_product R k.+1)
        (@euclidean_inner_product R n) (hom_as_linear h) /\hom_comp h alpha=beta].
Proof.
move=>hkn hA hB.
have [w hW]:=euclidean_hyperplane_normal_exists hA.
have [a [p hComp]]:=euclidean_frame_complement_exists hkn hB.
have hExists z:exists h,is_euclidean_frame_extension alpha w beta (a z) h.
  have [h [hH _]]:=@euclidean_frame_extension_exists_unique R k n alpha w beta (a z) hA hW.
  by exists h.
have [F hF]:=choice hExists.
pose G:=fun h:Hom (R_n R k.+1) (R_n R n)=>p (h w).
have hCan:cancel F G.
  move=>z; rewrite /G (frame_extension_normal_value (hF z)).
  exact:frame_complement_cancel hComp z.
have hNorm z:inner_norm (@euclidean_inner_productP R n) (a z)=
    inner_norm (@euclidean_inner_productP R (n-k)) z.
  exact:(orthogonal_map_norm (@euclidean_inner_productP R (n-k))
    (@euclidean_inner_productP R n) (frame_complement_orthogonal hComp) z).
have hDist x y:
    mdist (F x:inner_metric_space (@euclidean_hom_inner_productP R k.+1 n)) (F y)=
    mdist (x:inner_metric_space (@euclidean_inner_productP R (n-k))) y.
  rewrite (@euclidean_frame_fibre_distance_isometry R k n alpha w beta (a x) (a y)
    (F x) (F y) hA hW (hF x) (hF y)) !inner_metric_distanceE.
  rewrite -linearB; exact:hNorm.
exists F,G; split; first exact hCan.
split; first exact hDist.
apply/seteqP; split=>h.
- move=>[z hz <-]; split; last exact:frame_extension_restriction (hF z).
  apply:(euclidean_frame_extension_orthogonal_iff hA hW hB (hF z)).2.
  split; first exact:frame_complement_normal hComp z.
  have hu:inner_norm (@euclidean_inner_productP R n) (a z)= 1 by rewrite hNorm.
  by rewrite -(inner_norm_sqr (@euclidean_inner_productP R n)) hu expr1n.
- move=>[hH hRestriction].
  pose v:=h w.
  have hExt:is_euclidean_frame_extension alpha w beta v h by constructor.
  have [hNormal hUnit]:=(euclidean_frame_extension_orthogonal_iff hA hW hB hExt).1 hH.
  pose z:=p v.
  have haz:a z=v:=frame_complement_range hComp hNormal.
  have hNv:inner_norm (@euclidean_inner_productP R n) v= 1.
    apply:inner_norm_value; first exact:ler01.
    by rewrite expr1n.
  exists z.
  + change (inner_norm (@euclidean_inner_productP R (n-k)) z= 1).
    rewrite -(hNorm z) haz; exact hNv.
  + apply:hom_ext=>x.
    rewrite (@euclidean_frame_extension_evaluation R k n alpha w beta (a z) (F z) hA hW (hF z) x)
      (@euclidean_frame_extension_evaluation R k n alpha w beta v h hA hW hExt x) haz.
    reflexivity.
Qed.
