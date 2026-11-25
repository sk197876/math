(** Federer (1969), 2.2.16, p. 72, first paragraph: every subfamily union of
    uniformly separated closed sets is closed. A ball of radius half the
    separation meets at most one family member; avoid that closed member by
    a smaller neighborhood. This supplies the printed claim from metric
    topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [uniformly_separated_closed_union]: direct
    closed-union assertion in Federer 2.2.16, p. 72.
    The family and subfamily may be uncountable. Empty members
    and repeated empty sets are allowed. *)
Theorem uniformly_separated_closed_union (R : realType) (X : metricType R)
    (J : Type) (D : set J) (F : J -> set X) (r : R) : 0 < r ->
  (forall j, D j -> closed (F j)) ->
  (forall j k, D j -> D k -> j <> k -> forall x y, F j x -> F k y -> r <= mdist x y) ->
  closed (\bigcup_(j in D) F j).
Proof.
move=> hr hclosed hsep.
have hr2 : 0 < r/2 by rewrite divr_gt0 // ltr0n.
have ho : open (~` \bigcup_(j in D) F j).
  rewrite openE=> x hx.
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP x _)).
  case: (pselect (exists j, D j /\ exists y, F j y /\ mdist x y < r/2))=> [[j [hj [y [hy hxy]]]]|hn].
  - have hxj : (~` F j) x by move=> hxj; apply: hx; by exists j.
    have hnb : nbhs x (~` F j).
      have hh := closed_openC (hclosed j hj); rewrite openE in hh; exact: hh x hxj.
    have [e he heB] := proj1 (metricType_numDomainType.nbhs_mdistP x _) hnb.
    exists (Order.min e (r/2)); first by change (is_true (0 < Order.min e (r/2))); rewrite lt_min he hr2.
    move=> z hz [k hk hzk].
    have hmin1 : Order.min e (r/2) <= e by rewrite ge_min lexx.
    have hze : mdist x z < e := lt_le_trans hz hmin1.
    case: (pselect (j = k))=> hjk.
    + apply: (heB z hze); by rewrite hjk.
    + have hmin2 : Order.min e (r/2) <= r/2 by rewrite ge_min lexx orbT.
      have hzr : mdist x z < r/2 := lt_le_trans hz hmin2.
      have ht := metric_triangle y x z; rewrite (metric_sym y x) in ht.
      have hl := ltrD hxy hzr; rewrite -splitr in hl.
      have hh := le_lt_trans (hsep j k hj hk hjk y z hy hzk) (le_lt_trans ht hl).
      by move: hh; rewrite ltxx.
  - exists (r/2)=> // z hz [j hj hzj].
    apply: hn; exists j; split=> //; exists z; by split.
have hc := open_closedC ho; by rewrite setCK in hc.
Qed.

(** Source for [uniformly_separated_closed_subfamily_union]: direct
    every-subfamily form in Federer 2.2.16, p. 72,
    needed to apply the second Ulam property of 2.1.6. *)
Corollary uniformly_separated_closed_subfamily_union (R : realType) (X : metricType R)
    (J : Type) (D : set J) (F : J -> set X) (r : R) : 0 < r ->
  (forall j, D j -> closed (F j)) ->
  (forall j k, D j -> D k -> j <> k -> forall x y, F j x -> F k y -> r <= mdist x y) ->
  forall E : set J, closed (\bigcup_(j in D `&` E) F j).
Proof.
move=> hr hc hs E; apply: (@uniformly_separated_closed_union R X J (D `&` E) F r hr).
- move=> j [hj _]; exact: hc j hj.
- move=> j k [hj _] [hk _]; exact: hs j k hj hk.
Qed.
