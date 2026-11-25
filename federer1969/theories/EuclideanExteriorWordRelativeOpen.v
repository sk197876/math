(** Federer (1969), 3.2.28(2), printed p. 265:
    Q is open onto its actual image. This transports
    the proved homogeneous-space openness to the exact
    norm-metric convention of the manifold calculus. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanLinearMaps InnerProductUP InnerNorm InnerMetric
  InnerNormedTopology HilbertFormCompactness HomInner OrthogonalMaps OrthogonalInjectionSpaces
  EuclideanOrthogonalInvariantMeasures ExteriorGrading InnerExteriorPositivity
  SimpleVectorHomogeneous EuclideanHomInnerCharts EuclideanExteriorWordSmooth
  EuclideanExteriorWordImage EuclideanExteriorWordOpen EuclideanSubmanifoldUP
  InnerOwnNormTopology InnerMetricLawCompatibility HomeomorphismUP
  HomeomorphismRelativeOpen MetricSubsetBackground MetricSubsetRelativeOpen NormMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_exterior_word_relative_open]: the
    actual open image law for Q in Federer 3.2.28(2),
    p. 265, after the erratum deletion on line 3.
    This supplies every relatively open piece required by
    3.1.19(3), p. 231, in the norm topology of
    the actual Hilbert Hom and exterior inner products. *)
Theorem euclidean_exterior_word_relative_open (R:realType) m n:
  (0<m)%N ->(m<=n)%N ->forall W,
  @relatively_open_set [the topologicalType of real_norm_metric_space
    (inner_norm_real_norm (@euclidean_hom_inner_productP R m n))]
    [set g|is_orthogonal_map (@euclidean_inner_product R m)
      (@euclidean_inner_product R n) (hom_as_linear g)] W ->
  @relatively_open_set [the topologicalType of real_norm_metric_space
    (inner_norm_real_norm (@exterior_inner_productP R (euclidean_two_nonzero R)
      (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m))]
    ((@euclidean_exterior_word_map R m n) @`
      [set g|is_orthogonal_map (@euclidean_inner_product R m)
        (@euclidean_inner_product R n) (hom_as_linear g)])
    ((@euclidean_exterior_word_map R m n) @` W).
Proof.
move=>hm hmn W hW.
pose hBm:=@euclidean_inner_productP R m.
pose hBn:=@euclidean_inner_productP R n.
pose hX:=@euclidean_hom_inner_productP R m n.
pose hCan:=hom_inner_productP hBm hBn (@coordinate_basisP R m).
pose hY:=@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
  (@euclidean_inner_product R n) hBn m.
pose S:set (Hom (R_n R m) (R_n R n)):=
  [set g|is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g)].
pose X:=inner_metric_space hCan.
pose Y:=inner_metric_space hY.
have hWA:=homeomorphism_relative_open_images
  (homeomorphism_with_inverse_symmetric (inner_own_norm_homeomorphism hX)) hW.
rewrite !image_id in hWA.
have hWC:=homeomorphism_relative_open_images (inner_metric_law_homeomorphism hX hCan) hWA.
rewrite !image_id in hWC.
have hVal x:(val (@euclidean_frame_unit_exterior_map R m n x):Y)=
    euclidean_exterior_word_map (val x) by [].
have hOpen:=@metric_subset_open_relative_images R X Y S (unit_simple_set hBn m)
  (@euclidean_exterior_word_map R m n) (@euclidean_frame_unit_exterior_map R m n)
  hVal (@euclidean_frame_unit_exterior_open R m n hm hmn) W hWC.
have hImage:(@euclidean_exterior_word_map R m n) @` S=unit_simple_set hBn m.
  rewrite (@euclidean_exterior_word_image_simple_unit R m n hm).
  apply/seteqP; split=>x [h1 h2]; split=>//; by rewrite inner_norm_topologyE.
rewrite -hImage in hOpen.
have hNorm:=homeomorphism_relative_open_images (inner_own_norm_homeomorphism hY) hOpen.
by rewrite !image_id in hNorm.
Qed.
