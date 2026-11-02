(** Federer (1969), 3.2.28(1), printed p. 263: the
    regular-level application of 3.1.19 and 3.1.21.
    This supporting theorem derives local constant full rank
    from surjectivity on the actual fibre and derivative continuity. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP
  NormClassOneUP NormClassOneRestriction NormRegularity NormRegularityOperations
  NormOpenDomainLaws LinearRankUP LinearRankAtLeast LinearSurjectiveRank
  RankThresholdOpen EuclideanSubmanifoldUP SubmanifoldChartsUP
  SubmanifoldLevelStraightening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope nat_scope.

(** Source for [regular_fibre_submanifold]: the regular-level
    argument in Federer 3.2.28(1), p. 263, using
    3.1.19(2), p. 231. The derivative need only
    be onto at points of the stated fibre. Constant
    rank on neighbourhoods and the dimension bound are derived,
    including empty fibres and zero dimensions. *)
Theorem regular_fibre_submanifold (R:realType) N q k
    (f:R_n R N->R_n R q)
    (D:R_n R N->Hom (R_n R N) (R_n R q)) (c:R_n R q):
  (1<=k)%N ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R N))
    (inner_norm_real_norm (@euclidean_inner_productP R q)) (fun _=>True) f k ->
  is_norm_class_one_field (inner_norm (@euclidean_inner_productP R N))
    (inner_norm (@euclidean_inner_productP R q)) (fun _=>True) f D ->
  (forall b,f b=c ->forall y,exists x,D b x=y) ->
  @is_euclidean_submanifold R N (N-q) k [set x|f x=c].
Proof.
move=>hk hf hD hSurj.
pose X:=R_n R N; pose Y:=R_n R q.
pose NX:=inner_norm (@euclidean_inner_productP R N).
pose NY:=inner_norm (@euclidean_inner_productP R q).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R N).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R q).
apply:(@regular_level_charts_submanifold R N (N-q) k [set x|f x=c] hk).
move=>b hb.
have hThreshold:=@linear_surjective_rank_at_least R X Y q
  (@coordinate_basis R q) (@coordinate_basisP R q) (D b) (hSurj b hb).
have hRank:=@linear_rank_from_full_threshold R X Y q
  (@coordinate_basis R q) (@coordinate_basisP R q) (D b) hThreshold.
have hqN:=@linear_rank_domain_bound R X Y (D b) N
  (@coordinate_basis R N) (@coordinate_basisP R N) q hRank.
pose T:=fun x:X=>True /\ linear_rank_at_least (D x) q.
have hOpen x (hx:T x):norm_domain_interior NX T x.
  have hResult:=@rank_threshold_interior R X Y NX
    (@euclidean_inner_product R N) (@euclidean_inner_product R q)
    (@euclidean_inner_productP R N) (@euclidean_inner_productP R q)
    N (@coordinate_basis R N) (@coordinate_basisP R N) erefl
    (fun _=>True) D (fun x _=>@norm_full_domain_interior R X NX x)
    (norm_class_one_continuity hD) x q I hx.2.
  exact hResult.
have hfT:=@norm_class_open_restriction R X Y NX NY hNX hNY
  (fun _=>True) T f k (fun x _=>I) hOpen hf.
have hDT:=@norm_class_one_field_open_restriction R X Y NX NY
  (fun _=>True) T f D (fun x _=>I) hOpen hD.
exists q,T,f,D; split; first exact:(hOpen b (conj I hThreshold)).
split; first exact:leq_subr.
split; first by rewrite (subKn hqN).
split; first exact:hfT.
split; first exact:hDT.
split.
- apply/seteqP; split=>x.
  + move=>[hx hTx]; split; first exact:hTx.
    change (f x=f b); exact:(eq_trans hx (esym hb)).
  + move=>[hTx hx]; split; last exact:hTx.
    change (f x=c); exact:(eq_trans hx hb).
- move=>x hx; rewrite (subKn hqN).
  exact:(@linear_rank_from_full_threshold R X Y q
    (@coordinate_basis R q) (@coordinate_basisP R q) (D x) hx.2).
Qed.
