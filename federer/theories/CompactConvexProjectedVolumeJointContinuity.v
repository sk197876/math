(** Federer (1969), 3.2.36, p. 272:
    actual projected volume is jointly continuous
    in the projection and compact convex body. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanProjectionSpace EuclideanProjectionMetric ProjectedVolumeMeasurability
  CompactSetDistanceProfile CompactHausdorffMetric CompactEuclideanProjectionImage
  CompactProjectionJointImageControl CompactConvexVolumeHausdorffBound PositiveUniformErrorRadius
  EuclideanProjectionConvexImage EuclideanLebesgueDimensions EuclideanLebesgueBoxes MeasureUP MeasureBasic
  RealMetricBackground MeasurableRealEmbedding ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_convex_projection_pairs]: the
    domain O*(n,m) times C in Federer
    3.2.36, p. 272, expressed as the
    convex-body subspace of the existing product
    of projection and compact Hausdorff spaces.
    The convexity predicate is independent; no
    replacement hyperspace or image operation
    is introduced. *)
Definition compact_convex_projection_pairs (R:realType) n m:
    set ((euclidean_projection_space R n m)*
      (compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)))):=
  [set z|is_inner_convex (val z.2)].

(** Source for [compact_convex_projected_volume_joint_scalar_continuous]:
    direct joint projected-volume continuity in
    Federer 3.2.36, p. 272. Uniform
    compact image control in both variables
    and the actual Steiner volume estimate
    discharge every continuity premise. All
    compact convex sources, including those
    with empty interior, are retained, as
    are zero-dimensional projection blocks. *)
Theorem compact_convex_projected_volume_joint_scalar_continuous (R:realType) n m:
  continuous (fun z:subspace (@compact_convex_projection_pairs R n m)=>
    (fine (projected_volume_function (val z.2) z.1):real_line_metric R)).
Proof.
rewrite subspace_continuousP=>z hz U hU.
pose H:=compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)).
pose p:=z.1; pose A:H:=z.2.
have hA:is_inner_convex (val A):=hz.
have [K hK]:=compact_euclidean_projection_image_exists p A.
have hKConvex:is_inner_convex (val K).
  rewrite hK; exact:euclidean_projection_convex_image hA.
have hKVolume:euclidean_lebesgue_measure m (val K)=projected_volume_function (val A) p.
  by rewrite hK.
have [e he hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP
  (fine (projected_volume_function (val A) p):real_line_metric R) U) hU.
have [C [hC hError]]:=compact_convex_volume_hausdorff_bound hKConvex.
have [d [hd [hd1 hSmall]]]:=positive_uniform_error_radius_exists hC he.
have [V [hV [hp hControl]]]:=@compact_projection_joint_image_control R n m p A d hd.
have hdHalf:0<d/2 by rewrite divr_gt0 // ltr0n.
change (nbhs z (fun w:(euclidean_projection_space R n m*H)%type=>
  is_inner_convex (val w.2) ->U (fine (projected_volume_function (val w.2) w.1):real_line_metric R))).
exists (V,[set B:H|mdist A B<d/2]).
- split.
  + rewrite openE in hV; exact:hV p hp.
  + apply:(metricType_numDomainType.nbhs_mdistP A _).2; by exists (d/2).
- move=>[q B] [hq hAB] hBClass.
  have hB:is_inner_convex (val B):=hBClass.
  have [Q hQ]:=compact_euclidean_projection_image_exists q B.
  have hQConvex:is_inner_convex (val Q).
    rewrite hQ; exact:euclidean_projection_convex_image hB.
  have hClose:=hControl q B K Q hq hAB hK hQ.
  have hCloseOne:mdist K Q<1:=lt_le_trans hClose hd1.
  have hVolume:=hError Q hQConvex hCloseOne d hd hd1 hClose.
  have hQVolume:euclidean_lebesgue_measure m (val Q)=projected_volume_function (val B) q.
    by rewrite hQ.
  have hProjectedError:=hVolume.
  rewrite hKVolume hQVolume in hProjectedError.
  apply:hBall; exact:le_lt_trans hProjectedError hSmall.
Qed.

(** Source for [compact_convex_projected_volume_joint_continuous]:
    the same joint continuity conclusion in
    Federer 3.2.36, p. 272, for
    the original extended-real volume values.
    Actual compact image finiteness justifies
    finite embedding; there is no default
    value at infinity or added regularity
    hypothesis on the convex source. *)
Theorem compact_convex_projected_volume_joint_continuous (R:realType) n m:
  continuous (fun z:subspace (@compact_convex_projection_pairs R n m)=>
    (projected_volume_function (val z.2) z.1:extended_real_line R)).
Proof.
have hScalar:=@compact_convex_projected_volume_joint_scalar_continuous R n m.
have hFinite (z:subspace (@compact_convex_projection_pairs R n m)):
    projected_volume_function (val z.2) z.1 \is a fin_num.
  rewrite (ge0_fin_numE (projected_volume_function_nonnegative (val z.2) z.1)).
  exact:euclidean_compact_finite (@euclidean_projected_compact_image R n m z.1 (val z.2) (set_valP z.2).1).
have hEq:(fun z:subspace (@compact_convex_projection_pairs R n m)=>
    (fine (projected_volume_function (val z.2) z.1))%:E)=
    (fun z:subspace (@compact_convex_projection_pairs R n m)=>projected_volume_function (val z.2) z.1).
  apply:funext=>z; exact:fineK (hFinite z).
rewrite -hEq=>z.
exact:continuous_comp (hScalar z) (@real_extended_embedding_continuous R _).
Qed.
