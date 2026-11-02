(** Federer (1969), 3.2.31, p. 269: supporting closed
    low-rank loci for the class-one representatives. The rank
    superlevel is open by 3.1.18, p. 229. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness NormDifferentialUP NormClassOneUP NormMetric
  LinearRankAtLeast RankThresholdOpen InnerOwnNormTopology HomeomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [class_one_low_rank_locus_closed]: supporting
    compact critical-source restrictions in Federer 3.2.31,
    p. 269. Continuity of the actual differential makes
    its rank-below-mu locus closed. All natural degrees and
    source/target dimensions are included. *)
Theorem class_one_low_rank_locus_closed (R:realType) m v mu
    (G:R_n R m->R_n R v) (D:R_n R m->Hom (R_n R m) (R_n R v)):
  is_norm_class_one_field (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R v)) setT G D ->
  @closed (inner_metric_space (@euclidean_inner_productP R m))
    [set x|~linear_rank_at_least (D x) mu].
Proof.
move=>hG.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NY:=inner_norm (@euclidean_inner_productP R v).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
have hInterior a:(@setT (R_n R m)) a ->norm_domain_interior NX setT a.
  move=>_; exists 1; split; first exact:ltr01.
  by move=>z hz.
have hOpen:=@rank_threshold_open R (R_n R m) (R_n R v)
  NX (@euclidean_inner_product R m) (@euclidean_inner_product R v) hNX
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R v)
  m (@coordinate_basis R m) (@coordinate_basisP R m) erefl setT D hInterior
  (norm_class_one_continuity hG) mu.
have hCont:=homeomorphism_continuous (inner_own_norm_homeomorphism (@euclidean_inner_productP R m)).
have hClosed: @closed (inner_metric_space (@euclidean_inner_productP R m))
    ((fun x:inner_metric_space (@euclidean_inner_productP R m)=>
      (x:real_norm_metric_space hNX)) @^-1` (~` [set x|setT x /\linear_rank_at_least (D x) mu])).
  exact ((continuous_closedP _).1 hCont _ (open_closedC hOpen)).
have hEq:((fun x:inner_metric_space (@euclidean_inner_productP R m)=>
      (x:real_norm_metric_space hNX)) @^-1` (~` [set x|setT x /\linear_rank_at_least (D x) mu]))=
    [set x|~linear_rank_at_least (D x) mu].
  apply/seteqP; split=>x hx.
  - move=>hRank; apply:hx; by split.
  - by move=>[_ hRank]; exact:hx hRank.
by rewrite -hEq.
Qed.
