(** Federer (1969), 3.2.47, p. 283: supporting
    actual smoothness of the isotropy image of O(n-1).
    The smooth constant-rank theorem supplies one set of local
    straightening charts valid at every finite order. This is
    stronger than merely asserting each finite class separately. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom ModuleQuotient SubspaceSums SubspaceCarrier SubspaceEquality
  GrassmannSubspaces GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric HilbertFormCompactness NormMetric OrthogonalMaps
  LinearRankUP LinearRankTransport TangentConeUP EuclideanSubmanifoldUP SubmanifoldTangentPlane
  FiniteInnerSmoothSubmanifoldUP SmoothSubmanifoldOpenImage EuclideanIsometricEmbeddingCalculus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_isometric_smooth_submanifold_image]:
    an actual isometric ambient injection preserves class
    infinity with common local charts, supporting I in
    3.2.47, p. 283. Actual differential ranks follow
    from the original tangent dimensions and orthogonal linear part. *)
Theorem euclidean_isometric_smooth_submanifold_image (R:realType) m n mu
    (S:set (R_n R m)) (F:R_n R m->R_n R n):
  @is_euclidean_smooth_submanifold R m mu S ->
  (forall x y,mdist (F x:inner_metric_space (@euclidean_inner_productP R n)) (F y)=
    mdist (x:inner_metric_space (@euclidean_inner_productP R m)) y) ->
  @is_euclidean_smooth_submanifold R n mu (F @` S).
Proof.
move=>hS hMetric.
pose X:=R_n R m.
pose Y:=R_n R n.
pose hX:=@euclidean_inner_productP R m.
pose hY:=@euclidean_inner_productP R n.
have [L [hL [hSmooth [hField [G [hGF hGContinuous]]]]]]:=
  @euclidean_isometric_embedding_calculus R m n F hMetric.
apply:(@smooth_submanifold_open_constant_rank_image R m n mu mu S F (fun _=>L)
  hS hSmooth hField).
- move=>a ha J hJ.
  have [W hTan]:=@submanifold_tangent_plane R m mu 1 S a (leqnn 1)
    (@euclidean_smooth_submanifold_class R m mu S hS 1%N) ha.
  have hRange:range_subspace (hom_as_linear J)=grassmann_val W.
    apply:subspace_ext=>v.
    split.
    - move=>[x hx]; have hv:range J v.
        exists x; first exact I; exact (esym hx).
      by rewrite -hJ hTan in hv.
    - move=>hv; have hRangeJ:range J v by rewrite -hJ hTan.
      have [x _ hx]:=hRangeJ; exists x; exact (esym hx).
  have hRank:has_linear_rank J mu.
    rewrite /has_linear_rank hRange; exact:grassmann_proof W.
  have hInjective:injective (hom_as_linear L):=orthogonal_map_injective hX hY hL.
  exact (@linear_injective_postcomposition_rank R (R_n R mu) X Y J L n
    (@coordinate_basis R n) (@coordinate_basisP R n) mu hInjective hRank).
- move=>W [O [hO hW]].
  exists (G @^-1` O); split.
  + exact (@open_comp (NormMetric.real_norm_metric_space (HilbertFormCompactness.inner_norm_real_norm hY))
      (NormMetric.real_norm_metric_space (HilbertFormCompactness.inner_norm_real_norm hX)) G O
      (fun y _=>hGContinuous y) hO).
  + rewrite hW; apply/seteqP; split=>y.
    * move=>[x [hx hxO] <-]; split; first by exists x.
      change (O (G (F x))); by rewrite hGF.
    * move=>[[x hx <-] hGO]; exists x; last reflexivity.
      split; first exact hx.
      change (O (G (F x))) in hGO; by rewrite hGF in hGO.
Qed.
