(** Federer (1969), 3.2.36, p. 272:
    Lebesgue volume is continuous on the
    nonempty compact convex Hausdorff class. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  CompactSetDistanceProfile CompactHausdorffMetric CompactConvexVolumeHausdorffBound
  PositiveUniformErrorRadius RealMetricBackground MeasurableRealEmbedding ExtendedRealOrderTopology
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_convex_euclidean_class]:
    the class C in the first paragraph
    of Federer 3.2.36, p. 272.
    Its members are the existing nonempty
    compact-set carrier, restricted by the
    independent convexity predicate. The existing
    Hausdorff topology is retained. *)
Definition compact_convex_euclidean_class (R:realType) n:
    set (compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n))):=
  [set A|is_inner_convex (val A)].

(** Source for [compact_convex_volume_scalar_continuous]:
    direct first conclusion of Federer 3.2.36,
    p. 272. The actual finite scalar part
    of Lebesgue volume is continuous on C
    in Hausdorff distance. The local error
    bound is proved from actual Steiner tubes;
    no full-dimensional interior or nonzero
    volume is assumed. Ambient zero remains
    an explicit extension with its unit atom. *)
Theorem compact_convex_volume_scalar_continuous (R:realType) n:
  continuous (fun A:subspace (@compact_convex_euclidean_class R n)=>
    (fine (euclidean_lebesgue_measure n (val A)):real_line_metric R)).
Proof.
rewrite subspace_continuousP=>A hA U hU.
pose H:=compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)).
pose f (B:H):real_line_metric R:=fine (euclidean_lebesgue_measure n (val B)).
have hConvex:is_inner_convex (val A):=hA.
have [e he hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP (f A) U) hU.
have [C [hC hError]]:=compact_convex_volume_hausdorff_bound hConvex.
have [d [hd [hd1 hSmall]]]:=positive_uniform_error_radius_exists hC he.
have hNeighbourhood:nbhs A [set B:H|mdist A B<d].
  apply:(metricType_numDomainType.nbhs_mdistP A _).2; by exists d.
change (nbhs (A:H) (fun B:H=>is_inner_convex (val B) ->U (f B))).
apply:(@filterS _ (nbhs A) _ [set B:H|mdist A B<d] _ _ hNeighbourhood)=>B hB hBClass.
apply:hBall.
have hConvexB:is_inner_convex (val B):=hBClass.
have hB1:mdist A B<1:=lt_le_trans hB hd1.
exact:le_lt_trans (hError B hConvexB hB1 d hd hd1 hB) hSmall.
Qed.

(** Source for [compact_convex_volume_continuous]:
    direct Lebesgue-volume continuity in Federer
    3.2.36, p. 272, with the
    original extended-real measure values. Compact
    finiteness was proved before taking the
    scalar part; finite embedding recovers the
    actual measure, including zero-volume bodies. *)
Theorem compact_convex_volume_continuous (R:realType) n:
  continuous (fun A:subspace (@compact_convex_euclidean_class R n)=>
    (euclidean_lebesgue_measure n (val A):extended_real_line R)).
Proof.
have hScalar:=@compact_convex_volume_scalar_continuous R n.
have hEq:(fun A:subspace (@compact_convex_euclidean_class R n)=>
    (fine (euclidean_lebesgue_measure n (val A)))%:E)=
    (fun A:subspace (@compact_convex_euclidean_class R n)=>
      euclidean_lebesgue_measure n (val A)).
  apply:funext=>A.
  have hNonnegative:=measure_nonnegative
    (euclidean_lebesgue_is_measure R n) (val A).
  have hFinite:=euclidean_compact_finite (set_valP A).1.
  apply:fineK; by rewrite (ge0_fin_numE hNonnegative).
rewrite -hEq=>A.
exact:continuous_comp (hScalar A) (@real_extended_embedding_continuous R _).
Qed.
