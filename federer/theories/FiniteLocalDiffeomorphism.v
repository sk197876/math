(** Federer (1969), 3.1.18, p. 229: an injective differential in
    equal finite dimensions gives a local diffeomorphism of class k.
    Rank openness supplies the inverse field on a neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm
  NormMetric NormDifferentialUP NormClassOneUP LinearBasis FiniteNormMetricPolish
  NormRegularity NormRegularityOperations NormOpenDomainLaws
  NormClassOneRestriction NormDiffeomorphismUP NormLocalDiffeomorphism
  LinearRankAtLeast LinearFullRank RankThresholdOpen FiniteLinearInverseField.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_local_diffeomorphism]: the inverse-function
    inference for g at a in Federer 3.1.18, p. 229. This supporting
    form applies to any finite-dimensional inner-product space. No
    inverse or inverse regularity is assumed. *)
Theorem finite_local_diffeomorphism (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B)
    (hN:is_real_norm (inner_norm hB)) m (b:'I_m->X) (hb:is_basis b)
    (A:set X) (f:X->X) (D:X->Hom X X) a k :
  norm_class hN hN A f k -> is_norm_class_one_field (inner_norm hB) (inner_norm hB) A f D ->
  A a -> injective (D a) ->
  exists r:R, 0<r /\
    (forall x, inner_norm hB (x-a)<r -> A x) /\
    exists g:X->X, is_norm_diffeomorphism hN hN
      (fun x=>inner_norm hB (x-a)<r)
      (f @` [set x|inner_norm hB (x-a)<r]) f g k.
Proof.
move=>hf hD ha hinj.
have hfull : linear_rank_at_least (D a) m := (linear_full_rankP hb (D a)).2 hinj.
have hfzero := norm_class_one_zero hD.
have [s [hs hball]] := @rank_threshold_interior R X X (inner_norm hB)
  B B hB hB m b hb erefl A D
  (fun x hx=>(@hfzero x hx).1) (norm_class_one_continuity hD)
  a m ha hfull.
pose U:=fun x=>inner_norm hB (x-a)<s.
have hU x (hx:U x) : A x /\ injective (D x).
  have hh := hball (x-a) hx.
  rewrite (addrC a (x-a)) subrK in hh; split; first exact hh.1.
  exact: (linear_full_rankP hb (D x)).1 hh.2.
have hopen x (hx:U x) : norm_domain_interior (inner_norm hB) U x.
  exact (@norm_open_ball_domain_interior R X (inner_norm hB) hN a s x hx).
have hUA x (hx:U x) : A x := (hU x hx).1.
have hfU := @norm_class_open_restriction R X X (inner_norm hB) (inner_norm hB)
  hN hN A U f k hUA hopen hf.
have hDU := @norm_class_one_field_open_restriction R X X (inner_norm hB) (inner_norm hB)
  A U f D hUA hopen hD.
have [E hE] := @norm_finite_inverse_field_exists R X (inner_norm hB) hN
  m b hb U D (fun x hx=>(hU x hx).2).
have haU:U a by rewrite /U subrr inner_norm0.
have hc := @finite_norm_metric_complete R X (inner_norm hB) hN m b hb.
have [r [hr [hUr [g hg]]]] := @norm_local_diffeomorphism_from_inverse_field R X
  (inner_norm hB) hN hc U f D E a k hfU hDU haU
  (fun x hx=>(hE x hx).1) (fun x hx=>(hE x hx).2.1) (fun x hx=>(hE x hx).2.2).
exists r; split=>//; split.
- move=>x hx; exact: hUA x (hUr x hx).
- by exists g.
Qed.
