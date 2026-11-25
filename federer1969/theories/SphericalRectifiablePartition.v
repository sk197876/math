(** Federer (1969), 3.2.48, p. 285: the reduction by
    3.2.29 to countably many class-one manifolds can be made
    subordinate to a disjoint Borel partition contained in the sphere.
    The original rectifiable set itself need not be Borel. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric UnitSphereSpace
  EuclideanSubmanifoldUP SphericalRectifiableManifoldCover RectifiableManifoldCoverUP RectifiableSetUP
  SubmanifoldBorel TopologicalBorel BorelPartition BorelSubordinatePartition
  CountablyClosedFamilyUP HausdorffMeasure MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_spherical_rectifiable_partition]: independent
    laws for the manifold partition used in 3.2.48, p. 285.
    Pieces are Borel ambient sets; only their intersections with
    the original A are used as completed measurable source pieces. *)
Record is_spherical_rectifiable_partition (R:realType) d r
    (A:set (R_n R (1+d))) (P:set (set (R_n R (1+d))))
    (M:set (R_n R (1+d))->set (R_n R (1+d))):Prop:={
  (** Source: countability in 3.2.29, p. 267, used in 3.2.48, p. 285. *)
  spherical_partition_countable:countable P;
  (** Source: disjointification by 2.2.1, p. 60, supporting 3.2.48, p. 285. *)
  spherical_partition_disjoint:set_family_disjoint P;
  (** Source: Borel pieces in the reduction of 3.2.48, p. 285, by 3.2.29. *)
  spherical_partition_borel:forall B,P B ->@borel_set (inner_metric_space (@euclidean_inner_productP R (1+d))) B;
  (** Source: actual class-one manifolds in 3.2.29, p. 267, used in 3.2.48, p. 285. *)
  spherical_partition_manifold:forall B,P B ->@is_euclidean_submanifold R (1+d)%N r 1%N (M B);
  (** Source: containment in the sphere in the manifold reduction of 3.2.48, p. 285. *)
  spherical_partition_inside:forall B,P B ->M B `<=` @euclidean_unit_sphere_set R (1+d);
  (** Source: subordination in the partition reduction of 3.2.48, p. 285. *)
  spherical_partition_subordinate:forall B,P B ->B `<=` M B;
  (** Source: the null uncovered remainder in 3.2.29, p. 267, used in 3.2.48, p. 285. *)
  spherical_partition_almost:measure_almost_included (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) r) A (\bigcup_(B in P) B)
}.

(** Source for [spherical_rectifiable_partition_exists]: existence
    of the preceding independent partition laws from 3.2.29 and
    2.2.1, as used in 3.2.48, p. 285. Neither a Borel
    hypothesis on the original set nor a supplied atlas is added. *)
Theorem spherical_rectifiable_partition_exists (R:realType) d r (A:set (R_n R (1+d))):
  A `<=` @euclidean_unit_sphere_set R (1+d) ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) r) r A ->
  exists P M,is_spherical_rectifiable_partition r A P M.
Proof.
move=>hA hRA.
pose X:=inner_metric_space (@euclidean_inner_productP R (1+d)).
have [C [hC hInside]]:=@spherical_rectifiable_class_one_cover R d r A hA hRA.
pose U:=\bigcup_(M in C) M.
have hCB M (hM:C M):@borel_set X M.
  exact (euclidean_submanifold_borel (submanifold_measure_cover_class hC hM)).
have hUB:@borel_set X U.
  exact (borel_set_countable_union (submanifold_measure_cover_countable hC) hCB).
have [P [hP hSub]]:=@borel_countable_cover_subordinate_partition X U C
  hUB (submanifold_measure_cover_countable hC) hCB (fun x hx=>hx).
have hPoint B:exists M,P B ->C M /\B `<=` M.
  have [hB|hB]:=pselect (P B).
  - have [_ [M hM]]:=hSub B hB; exists M; by move=>_.
  - exists set0; by move=>h; exfalso; exact (hB h).
have [M hM]:=choice hPoint.
exists P,M; constructor.
- exact (borel_partition_countable hP).
- exact (borel_partition_disjoint hP).
- exact (borel_partition_members hP).
- move=>B hB; exact (submanifold_measure_cover_class hC (hM B hB).1).
- move=>B hB; exact (hInside (M B) (hM B hB).1).
- move=>B hB; exact (hM B hB).2.
- rewrite (borel_partition_union hP); exact (submanifold_measure_cover_almost hC).
Qed.
