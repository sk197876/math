(** Federer (1969), 3.2.29, p. 268:
    full source rank gives open neighbourhoods
    whose actual images are class-one manifolds. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormDifferentialUP NormClassOneUP NormRegularity NormRegularityOperations
  NormClassOneRestriction NormOpenDomainLaws RankThresholdOpen LinearRankAtLeast LinearFullRank LinearInjectiveRank
  NormRankZero ConstantRankLocalManifoldImage EuclideanSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [full_rank_local_manifold_image]: the
    open neighbourhoods U inside the full-rank
    locus P, Federer 3.2.29, p. 268, obtained
    from the actual constant-rank theorem. Every
    image f(U) is an m-dimensional class-one
    submanifold; the rank is not an extra image premise. *)
Theorem full_rank_local_manifold_image (R:realType) m n
    (f:R_n R m->R_n R n) (D:R_n R m->Hom (R_n R m) (R_n R n)) a:
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f 1 ->
  is_norm_class_one_field (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f D ->
  linear_rank_at_least (D a) m ->
  exists U:set (R_n R m),U a /\
    @open [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] U /\
    U `<=` [set x|linear_rank_at_least (D x) m] /\@is_euclidean_submanifold R n m 1 (f @` U).
Proof.
move=>hF hD hRank.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose P:set (R_n R m):=[set x|linear_rank_at_least (D x) m].
have hOpen x:P x ->norm_domain_interior NX P x.
  move=>hx.
  have [r [hr hBall]]:=@rank_threshold_interior R (R_n R m) (R_n R n)
    NX (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
    m (@coordinate_basis R m) (@coordinate_basisP R m) (erefl NX) setT D
    (fun x _=>@norm_full_domain_interior R (R_n R m) NX x)
    (norm_class_one_continuity hD) x m I hx.
  exists r; split; first exact hr.
  move=>h hh; exact:(hBall h hh).2.
have hDP:=@norm_class_one_field_open_restriction R (R_n R m) (R_n R n) NX NY setT P f D
  (fun x _=>I) hOpen hD.
have hFP:=@norm_class_open_restriction R (R_n R m) (R_n R n) NX NY hNX hNY setT P f 1
  (fun x _=>I) hOpen hF.
have hGeneric:norm_generic_rank NX P D a m.
  have [r [hr hBall]]:=hOpen a hRank.
  exists r; split; first exact hr.
  move=>h hh; have hx:=hBall h hh; split; first exact hx.
  apply:(@linear_injective_rank R (R_n R m) (R_n R n) m (@coordinate_basis R m)
    (@coordinate_basisP R m) n (@coordinate_basis R n) (@coordinate_basisP R n) (D (a+h))).
  exact:(linear_full_rankP (@coordinate_basisP R m) (D (a+h))).1 hx.
have hLocal:=@constant_rank_local_manifold_image R m 0 n 1.
rewrite addn0 in hLocal.
exact:hLocal P f D a (leqnn 1) hFP hDP hGeneric.
Qed.
