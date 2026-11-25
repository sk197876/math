(** Federer (1969), 3.2.21, p. 257: a countable
    dense family of orthogonal changes detects every differential
    of rank at least mu. This makes the null-set argument countable. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct OrthogonalMaps
  RealNormUP NormMetric EuclideanHomOperator EuclideanBlockLinearMaps EuclideanLinearJacobian
  EuclideanHomPostcomposeContinuity
  LinearRankAtLeast RankOrthogonalBlock RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dense_orthogonal_rank_detection]: supporting
    orthogonal selection in Federer 3.2.21, p. 257.
    Continuity and positive top Jacobian replace an uncountable
    family of exceptional sets by one countable family; no
    probability law or extra rank hypothesis is assumed. *)
Lemma dense_orthogonal_rank_detection (R:realType) k mu n
    (S:set (Hom (R_n R (k+mu)) (R_n R (k+mu))))
    (D:Hom (R_n R (k+mu)) (R_n R n)):
  (forall g:Hom (R_n R (k+mu)) (R_n R (k+mu)),
    is_orthogonal_map (@euclidean_inner_product R (k+mu))
      (@euclidean_inner_product R (k+mu)) (hom_as_linear g) ->
    forall r:R,0<r ->exists s,S s /\ euclidean_operator_norm (s-g)<r) ->
  linear_rank_at_least D mu ->exists s,S s /\
    0<euclidean_linear_jacobian mu
      (hom_comp D (hom_comp s (@euclidean_last_injection_map R k mu))).
Proof.
move=>hDense hRank; have [g [hg hInj]]:=rank_orthogonal_block_injection hRank.
pose J:=fun A:Hom (R_n R (k+mu)) (R_n R (k+mu))=>
  euclidean_linear_jacobian mu (hom_comp D (hom_comp A (@euclidean_last_injection_map R k mu))).
have hJg:0<J g:= (euclidean_linear_jacobian_top_positive _).2 hInj.
have hCont:=@euclidean_restricted_jacobian_coordinates_continuous R (k+mu) n mu
  D (@euclidean_last_injection_map R k mu).
pose H:=real_norm_metric_space (@euclidean_operator_norm_is_norm R (k+mu) (k+mu)).
pose U:=fun y:real_line_metric R=>mdist (J g:real_line_metric R) y<J g.
have hU:nbhs (J g:real_line_metric R) U.
  apply:(proj2 (metricType_numDomainType.nbhs_mdistP (J g:real_line_metric R) U)).
  exists (J g)=>// y hy; exact hy.
have [r hr hNear]:=proj1 (metricType_numDomainType.nbhs_mdistP (g:H) _) (hCont g U hU).
have [s [hSs hs]]:=hDense g hg r hr.
exists s; split; first exact hSs.
have hDistance:mdist (g:H) (s:H)<r.
  rewrite real_norm_metric_distanceE.
  by rewrite (real_seminorm_subtract (@euclidean_operator_norm_is_norm R (k+mu) (k+mu)).1 g s).
have hValue:=hNear s hDistance.
change (is_true (`|J g-J s|<J g)) in hValue.
have hLower:=ler_norm (J g-J s).
have hStep:J g-J s<J g:=le_lt_trans hLower hValue.
change (is_true (0<J s)); by move:hStep; rewrite ltrBlDr ltrDl.
Qed.
