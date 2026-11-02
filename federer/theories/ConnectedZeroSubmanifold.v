(** Federer (1969), 3.1.20, p. 233: the nonempty connected
    rank-zero case consists of one point, by the isolated-point
    characterization of 3.1.19. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormMetric NormDifferentialUP EuclideanSubmanifoldUP
  SubmanifoldBasicLaws ZeroSubmanifold MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [connected_zero_submanifold_singleton]: the
    rank-zero singleton observation in the converse proof of
    Federer 3.1.20, p. 233. Any nonempty connected
    zero-dimensional submanifold is exactly a singleton. *)
Lemma connected_zero_submanifold_singleton (R:realType) n k (B:set (R_n R n)) b :
  @connected [the topologicalType of real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))] B ->
  @is_euclidean_submanifold R n 0 k B -> B b -> B=[set b].
Proof.
move=>hConn hB hb.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose M:=real_norm_metric_space hNX.
have [_ [r [hr hIso]]]:=zero_submanifold_point_isolated hB hb.
pose O:set M:=fun x=>@mdist R M b x<r.
have hO:open O:=@metric_open_ball_open R M b r.
have heq:[set b]=B `&` O.
  apply/seteqP; split=>x.
  - move=>->; split=>//; by rewrite /O mdistxx.
  - move=>[hx hOx].
    have hh:NX (x-b)<r by rewrite /NX (real_seminorm_subtract hNX.1); exact hOx.
    have hxi:=hIso (x-b) hh; rewrite addrC subrK in hxi.
    exact: hxi hx.
have hcl:closed [set b:M].
  exact (@compact_closed M _ (@metric_hausdorff R M) (@compact_set1 M b)).
have hsingle:[set b]=B.
  apply: (hConn [set b]); first by exists b.
  - by exists O.
  - exists [set b]; first exact hcl.
    apply/seteqP; split=>x.
    + move=>->; by split.
    + by move=>[_ hx].
exact: esym hsingle.
Qed.
