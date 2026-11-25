(** Federer (1969), 3.3.4, p. 292: membership
    in every original image R_v gives actual
    punctured source points in the plane arbitrarily
    near the centre. Keep every source point in
    the original A and in the original affine plane. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient
  EuclideanInnerProduct InnerMetric InnerNorm StructurePlaneGrowth
  ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_plane_accumulation_reciprocals]:
    the final implication from all R_v to D in
    Federer 3.3.4, p. 292, in all actual
    Grassmann dimensions. Reciprocal radii are cofinal
    in every positive real radius; no source closure
    or measurable replacement is used. *)
Theorem structure_plane_accumulation_reciprocals (R:realType) n k
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) a
    (V:G (R_n R n) k):
  structure_plane_accumulation A a V <->forall i,
    exists x:inner_metric_space (@euclidean_inner_productP R n),
      A x /\ grassmann_val V (x-a) /\
      0<inner_norm (@euclidean_inner_productP R n) (x-a)<((i.+1)%:R:R)^-1.
Proof.
split.
- move=>hClosure i.
  have hPos:0<((i.+1)%:R:R)^-1 by rewrite invr_gt0 ltr0n.
  have hn:nbhs a [set x|mdist a x<((i.+1)%:R:R)^-1].
    apply:(proj2 (metricType_numDomainType.nbhs_mdistP a _)).
    by exists ((i.+1)%:R:R)^-1.
  have [x [[hA [hNe hV]] hNear]]:=hClosure _ hn.
  exists x; split=>//; split=>//; apply/andP; split.
  + by rewrite inner_norm_gt0 subr_eq0.
  + change (is_true (mdist a x<((i.+1)%:R:R)^-1)) in hNear.
    by move:hNear; rewrite inner_metric_distanceE -[a-x]opprB inner_normN.
- move=>hNear U hU.
  have [e he hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP a U) hU.
  have [i hSmall]:=positive_reciprocal_nat_small he.
  have [x [hA [hV /andP [hPos hDist]]]]:=hNear i.
  exists x; split.
  + split=>//; split=>//.
    by move:hPos; rewrite inner_norm_gt0 subr_eq0.
  + apply:hBall; change (is_true (mdist a x<e)).
    rewrite inner_metric_distanceE -[a-x]opprB inner_normN.
    exact:(lt_trans hDist hSmall).
Qed.
