(** Federer (1969), 3.3.19, pp. 303–304:
    sufficiently fine original levels are subordinate to
    every original open cover, and the level pieces form
    a basis of the actual relative topology of A.
    Both claims follow from actual compactness and shrinking. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology lra.
From Federer Require Import CoveringFamilyUP EuclideanInnerProduct InnerMetric MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularDiscTreeUP CircularDiscTreeTopology CircularDiscLimitUP CircularDiscDescendants
  CircularDiscLevelPieces CompactMetricOpenCoverNumber.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Covers.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation N:=(@FactorialDiscScales.count R).
Local Notation hs:=(@FactorialDiscScales.laws R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_levels_subordinate_open_cover]:
    the original fine level discs, not only their parts
    in A, lie in individual original open cover members,
    3.3.19, p. 303. Actual intersection with A,
    compactness and shrinking discharge the uniform choice. *)
Theorem circular_disc_levels_subordinate_open_cover (I:choiceType) (D:set I) (U:I->set E):
  (forall i,D i ->open (U i)) ->A `<=` \bigcup_(i in D) U i ->
  exists J:nat,forall j,(J<=j)%N ->forall z:E,z \in H j ->
    exists i,D i /\metric_closed_ball z (rho j) `<=` U i.
Proof.
move=>hOpen hCover.
have [hNonempty hCompact]:=@circular_disc_limit_nonempty_compact R H hH A hA.
have [d [hd hNumber]]:=@compact_metric_open_cover_number R E I D U A
  hNonempty hCompact hOpen hCover.
have hHalf:0<d/2 by rewrite divr_gt0 // ltr0n.
have [J hSmall]:=@factorial_disc_radius_small R N rho hs (d/2) hHalf.
exists J=>j hj z hz;apply:hNumber.
- exact:(@circular_disc_limit_meets_every_disc R H hH A hA j z hz).
- move=>x y hx hy.
  have hDistance:=@circular_disc_within_ball_distance R j z x y hx hy.
  have hRadius:=hSmall j hj;lra.
Qed.

(** Source for [circular_disc_pieces_relative_basis]: each
    original relative neighbourhood of each original point
    contains a whole level piece through that point,
    the basis assertion in 3.3.19, p. 304.
    The actual ambient open set and original A remain. *)
Theorem circular_disc_pieces_relative_basis (U:set E) (x:E):
  open U ->U x ->A x ->exists j:nat,exists z:E,
    z \in H j /\metric_closed_ball z (rho j) x /\
    A `&` metric_closed_ball z (rho j) `<=` U.
Proof.
move=>hU hxU hxA.
have hNeighbour:nbhs x U by apply:open_nbhs_nbhs;by split.
have [d hd hBall]:=(proj1 (metricType_numDomainType.nbhs_mdistP x U)) hNeighbour.
have hHalf:0<d/2 by rewrite divr_gt0 // ltr0n.
have [j hSmall]:=@factorial_disc_radius_small R N rho hs (d/2) hHalf.
have [z [hz hxZ]]:=(hA x).1 hxA j.
exists j,z;split=>//;split=>//;move=>y [_ hyZ].
have hDistance:=@circular_disc_within_ball_distance R j z x y hxZ hyZ.
have hRadius:=hSmall j (leqnn j).
have hInside:mdist x y<d by lra.
exact:hBall y hInside.
Qed.
End Covers.
