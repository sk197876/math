(** Federer (1969), 2.10.28(2), p. 192: replacing each member S of a special
    family by a family special for S gives a special family for the original
    parent. Descendants of different disjoint parents are disjoint and have
    a unique parent. The clipped bound of (1) controls the test-interval
    sum. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge ConcaveIntervalGaugeUP
  SpecialIntervalFamilyUP SpecialIntervalClipping.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [special_interval_refinement]: direct
    union of the families K(S), S in H,
    in 2.10.28(2), p. 192. Use the
    finite union, with no enumeration order
    or multiplicities of interval sets. *)
Definition special_interval_refinement (R : realType) (H : {fset compact_real_intervals R})
    (K : compact_real_intervals R -> {fset compact_real_intervals R}) :=
  (\bigcup_(S <- H) K S)%fset.

(** Source for [special_interval_refinement_membership]:
    supporting union-membership law in 2.10.28(2),
    p. 192. A descendant belongs to the
    refinement exactly when it belongs to a
    family attached to some original member. *)
Lemma special_interval_refinement_membership (R : realType) (H : {fset compact_real_intervals R})
    (K : compact_real_intervals R -> {fset compact_real_intervals R}) U :
  U \in special_interval_refinement H K <-> exists S, S \in H /\ U \in K S.
Proof.
rewrite /special_interval_refinement; split.
- move=> /bigfcupP[S /andP[hS _] hU]; exists S; by split.
- move=> [S [hS hU]]; apply/bigfcupP; exists S; by rewrite ?andbT.
Qed.

(** Source for [special_interval_descendant_families_disjoint]:
    supporting uniqueness of the parent interval
    in 2.10.28(2), p. 192. A
    nonempty interval cannot belong to descendant
    families of two disjoint parent intervals. *)
Lemma special_interval_descendant_families_disjoint (R : realType) (h : R -> R)
    (J : compact_real_intervals R) (H : {fset compact_real_intervals R})
    (K : compact_real_intervals R -> {fset compact_real_intervals R}) :
  is_special_interval_family h J H ->
  (forall S, S \in H -> is_special_interval_family h S (K S)) ->
  forall S T, S \in H -> T \in H -> S!=T -> [disjoint K S & K T]%fset.
Proof.
move=> hH hK S T hS hT hne; apply/fdisjointP=> U hUS; apply/negP=> hUT.
have [x hx] := compact_real_interval_nonempty (set_valP U).
have hsubS := @special_interval_subsets R h S (K S) (hK S hS) U hUS.
have hsubT := @special_interval_subsets R h T (K T) (hK T hT) U hUT.
have hmem : (val S `&` val T) x by split; [exact: hsubS x hx | exact: hsubT x hx].
by rewrite (@special_intervals_disjoint R h J H hH S T hS hT hne) in hmem.
Qed.

(** Source for [special_interval_filtered_clipped_bound]:
    supporting test-interval estimate for the
    descendants of one parent in 2.10.28(2),
    p. 192. Whole descendants lying in T
    lie in T intersect S; the latter is
    an interval or empty, so the printed
    special-family condition applies directly. *)
Lemma special_interval_filtered_clipped_bound (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (S T : compact_real_intervals R)
    (K : {fset compact_real_intervals R}) :
  is_special_interval_family h S K ->
  \sum_(U <- K | `[< val U `<=` val T >]) concave_interval_cost h (val U)<=
    concave_interval_cost h (val T `&` val S).
Proof.
move=> hK; case: (pselect (val T `&` val S !=set0))=> hnon.
- have hI := compact_real_interval_intersection (set_valP T) (set_valP S) hnon.
  pose V : compact_real_intervals R := Sub (val T `&` val S) (mem_set hI).
  have heq : (\sum_(U <- K | `[< val U `<=` val T >]) concave_interval_cost h (val U))=
      \sum_(U <- K | `[< val U `<=` val V >]) concave_interval_cost h (val U).
    rewrite [LHS]big_mkcond [RHS]big_mkcond /=; apply: eq_big_seq=> U hU.
    have hsub := @special_interval_subsets R h S K hK U hU.
    have hc : `[< val U `<=` val T >]=`[< val U `<=` val V >].
      apply/idP/idP=> /asboolP hu; apply/asboolP.
      + move=> x hx; split; [exact: hu x hx | exact: hsub x hx].
      + by move=> x hx; have [hxt _] := hu x hx.
    by rewrite hc.
  rewrite heq; exact (@special_interval_envelope R h S K hK V).
- have he : val T `&` val S=set0.
    apply/seteqP; split=> [x hx|x []]; exfalso; apply: hnon; by exists x.
  have hz : (\sum_(U <- K | `[< val U `<=` val T >]) concave_interval_cost h (val U))=0.
    rewrite big_mkcond /= big_seq; apply: big1=> U hU.
    have hnotsub : ~ (val U `<=` val T).
      move=> hsubT; have [x hx] := compact_real_interval_nonempty (set_valP U).
      have hsubS := @special_interval_subsets R h S K hK U hU.
      have hmem : (val T `&` val S) x by split; [exact: hsubT x hx | exact: hsubS x hx].
      by rewrite he in hmem.
    by rewrite (asboolF hnotsub).
  by rewrite hz he (concave_interval_cost_empty hg).
Qed.

(** Source for [federer_2_10_28_2]: direct second
    property of special families, 2.10.28(2),
    p. 192. Exact mass is preserved by
    disjoint finite regrouping; the first property
    supplies the clipped outer bound. Empty
    child families and degenerate intervals remain
    included under their stated zero-cost laws. *)
Theorem federer_2_10_28_2 (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (J : compact_real_intervals R)
    (H : {fset compact_real_intervals R})
    (K : compact_real_intervals R -> {fset compact_real_intervals R}) :
  is_special_interval_family h J H ->
  (forall S, S \in H -> is_special_interval_family h S (K S)) ->
  is_special_interval_family h J (special_interval_refinement H K).
Proof.
move=> hH hK.
have hdis := @special_interval_descendant_families_disjoint R h J H K hH hK.
constructor.
- move=> U /special_interval_refinement_membership[S [hS hU]] x hx.
  apply: (@special_interval_subsets R h J H hH S hS).
  exact: (@special_interval_subsets R h S (K S) (hK S hS) U hU x hx).
- move=> U V /special_interval_refinement_membership[S [hS hU]]
    /special_interval_refinement_membership[T [hT hV]] hne.
  case: (eqVneq S T)=> [he|hneST].
  + move: hV; rewrite -he=> hV; exact: (@special_intervals_disjoint R h S (K S) (hK S hS) U V hU hV hne).
  + apply/seteqP; split=> [x [hxU hxV]|x []].
    have hsubU := @special_interval_subsets R h S (K S) (hK S hS) U hU.
    have hsubV := @special_interval_subsets R h T (K T) (hK T hT) V hV.
    have hmem : (val S `&` val T) x by split; [exact: hsubU x hxU | exact: hsubV x hxV].
    by rewrite (@special_intervals_disjoint R h J H hH S T hS hT hneST) in hmem.
- rewrite /special_interval_refinement partition_disjoint_bigfcup //.
  transitivity (\sum_(S <- H) concave_interval_cost h (val S)); first exact: special_interval_cost_sum hH.
  apply: eq_big_seq=> S hS; exact: special_interval_cost_sum (hK S hS).
- move=> T; rewrite /special_interval_refinement big_mkcond partition_disjoint_bigfcup //.
  apply: le_trans (_ : _<=\sum_(S <- H) concave_interval_cost h (val T `&` val S))
    (@federer_2_10_28_1 R h hg J T H hH).
  rewrite !big_seq; apply: ler_sum=> S hS.
  rewrite -big_mkcond.
  exact: (@special_interval_filtered_clipped_bound R h hg S T (K S) (hK S hS)).
Qed.
