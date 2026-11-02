(** Federer (1969), 3.2.28(3), printed p. 266:
    the forgetful-map fibre is isometric to its sphere
    of last-vector parameters. The distance is the actual
    Hilbert Hom distance of 1.7.9, p. 35. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  OrthogonalMaps EuclideanHomInnerCharts EuclideanRectangularAdjoint EuclideanHyperplaneNormalUP
  EuclideanFrameExtensionUP EuclideanFrameExtension EuclideanRankOneInner.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_frame_extension_difference]: two
    members of the same fibre differ by the rank-one
    map x to (x.e_m)(v_1-v_2), supporting Federer
    3.2.28(3), p. 266. This follows from the
    abstract extension equations and source splitting. *)
Theorem euclidean_frame_extension_difference (R:realType) k n
    (alpha:Hom (R_n R k) (R_n R k.+1)) w
    (beta:Hom (R_n R k) (R_n R n)) v1 v2
    (h1 h2:Hom (R_n R k.+1) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R k.+1)
    (hom_as_linear alpha) ->is_euclidean_hyperplane_normal alpha w ->
  is_euclidean_frame_extension alpha w beta v1 h1 ->
  is_euclidean_frame_extension alpha w beta v2 h2 ->
  h1-h2=euclidean_rank_one_hom w (v1-v2).
Proof.
move=>hA hW h1E h2E; apply:hom_ext=>x.
change (h1 x-h2 x=euclidean_inner_product x w*:(v1-v2)).
rewrite (@euclidean_frame_extension_evaluation R k n alpha w beta v1 h1 hA hW h1E x)
  (@euclidean_frame_extension_evaluation R k n alpha w beta v2 h2 hA hW h2E x).
by rewrite [beta _+_]addrC addrKA scalerBr.
Qed.

(** Source for [euclidean_frame_fibre_distance_isometry]:
    the fibre-to-sphere isometry in Federer 3.2.28(3),
    p. 266. No replacement norm or scalar factor
    is introduced in the actual Hom metric. *)
Theorem euclidean_frame_fibre_distance_isometry (R:realType) k n
    (alpha:Hom (R_n R k) (R_n R k.+1)) w
    (beta:Hom (R_n R k) (R_n R n)) v1 v2
    (h1 h2:Hom (R_n R k.+1) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R k.+1)
    (hom_as_linear alpha) ->is_euclidean_hyperplane_normal alpha w ->
  is_euclidean_frame_extension alpha w beta v1 h1 ->
  is_euclidean_frame_extension alpha w beta v2 h2 ->
  mdist (h1:inner_metric_space (@euclidean_hom_inner_productP R k.+1 n)) h2=
    mdist (v1:inner_metric_space (@euclidean_inner_productP R n)) v2.
Proof.
move=>hA hW h1E h2E; rewrite !inner_metric_distanceE.
rewrite (@euclidean_frame_extension_difference R k n alpha w beta v1 v2 h1 h2 hA hW h1E h2E).
exact:(@euclidean_unit_rank_one_norm R k.+1 n w (v1-v2) (hyperplane_normal_unit hW)).
Qed.
