(** Federer (1969), 3.2.31, p. 269: supporting proved finite
    compact rescaling cover. Continuous differentials give the
    local contractions; finite closed first-hit pieces overlap
    only on Lebesgue null ball shells. Witness choices stay local. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanLebesgueDimensions MeasureUP LipschitzUP NormClassOneUP LinearRankAtLeast MetricClosedBalls
  SmallExteriorMajorantUP ClassOneSmallExteriorNeighborhood FinitePositiveBallCover
  EuclideanBallShellNull FiniteCompactNullOverlapCoverUP FiniteCompactNullOverlapCoverExistence
  CompactRescaledCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section RescaledCoverExistence.
Variable R:realType.
Variables m v mu:nat.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y:=(inner_metric_space (@euclidean_inner_productP R v)).

(** Source for [compact_rescaled_cover_exists]: supporting finite
    compact cover for the estimate in Federer 3.2.31, p. 269.
    Small-exterior majorants and actual local unit Lipschitz bounds
    are proved at each critical point. Compactness and null ball
    shells provide compact pieces with no overlap mass. Neither
    a source/target degree bound nor a prescribed cover is assumed. *)
Theorem compact_rescaled_cover_exists (G:X->Y) (D:X->Hom (R_n R m) (R_n R v))
    (K:set X) (epsilon:R):
  is_norm_class_one_field (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R v)) setT G D ->
  compact K ->(forall a,K a ->~linear_rank_at_least (D a) mu) ->(0<epsilon)%R ->
  exists N a T U C,@is_compact_rescaled_cover R m v mu G D K epsilon N a T U C.
Proof.
move=>hG hK hRank heps.
pose Z:Type:=(Hom (R_n R v) (R_n R v)*Hom (R_n R v) (R_n R v)*R)%type.
pose P (a:X) (z:Z):Prop:=(0<z.2)%R /\(K a ->
  @is_small_exterior_majorant R m v mu (D a) epsilon z.1.1 z.1.2 /\
  @is_metric_lipschitz_bound R X Y (metric_closed_ball a z.2) (fun x=>z.1.2 (G x)) 1%R).
have hData a:exists z,P a z.
  case:(pselect (K a))=>ha.
  - have [T [U [r [hMajor [hr hLip]]]]]:=@class_one_small_exterior_neighborhood R m v mu
      G D a epsilon hG (hRank a ha) heps.
    exists (T,U,r); split=>//; by move=>_.
  - exists (0%R,0%R,1%R); split; first exact:ltr01.
    by move=>h; exfalso; exact:ha h.
pose z a:=projT1 (cid (hData a)).
have hz a:P a (z a):=projT2 (cid (hData a)).
pose r a:=(z a).2.
have hr a:K a ->(0<r a)%R by move=>_; exact:(hz a).1.
have [N [a [hCenters hCover]]]:=@finite_positive_ball_cover R X 0%R K r hK hr.
pose B i:=metric_closed_ball (a i) (r (a i)).
pose O i:=[set x:X|(mdist (a i) x<r (a i))%R].
have hO i (hi:(i<N)%N):open (O i):=metric_open_ball_open (a i) (r (a i)).
have hB i (hi:(i<N)%N):closed (B i):=@metric_closed_ball_closed R X (a i) (r (a i)).
have hOB i (hi:(i<N)%N):O i `<=` B i by move=>x hx; exact:ltW hx.
have hShell i (hi:(i<N)%N):@euclidean_lebesgue_measure R m (B i `\` O i)=0.
  exact (@euclidean_positive_ball_shell_null R m (a i) (r (a i)) (hr _ (hCenters i hi))).
have [C hC]:=@finite_compact_null_overlap_cover_exists R X (@euclidean_lebesgue_measure R m)
  (euclidean_lebesgue_is_measure R m) K N O B hK hO hB hOB hShell hCover.
exists N,a,(fun i=>(z (a i)).1.1),(fun i=>(z (a i)).1.2),C.
constructor.
- exact hCenters.
- exact:null_overlap_cover_compact hC.
- move=>i hi x hx; exact (@null_overlap_cover_subordinate R X
    (@euclidean_lebesgue_measure R m) K N B C hC i hi x hx).1.
- exact:null_overlap_cover_union hC.
- exact:null_overlap_cover_pairwise_null hC.
- move=>i hi; exact ((hz (a i)).2 (hCenters i hi)).1.
- move=>i hi; have hLip:=((hz (a i)).2 (hCenters i hi)).2.
  split; first exact hLip.1.
  move=>x y hx hy; apply:hLip.2.
  + exact (@null_overlap_cover_subordinate R X (@euclidean_lebesgue_measure R m) K N B C hC i hi x hx).2.
  + exact (@null_overlap_cover_subordinate R X (@euclidean_lebesgue_measure R m) K N B C hC i hi y hy).2.
Qed.
End RescaledCoverExistence.
