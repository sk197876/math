(** Federer (1969), 2.10.1, p. 170: threshold-infimum characterisation of
    the corrected topological extension. Quantify over open covers of the
    whole space. The literal printed A-cover extension is refuted by the
    sealed counterexample in OpenRefinementNonmonotonicity.v; the metric
    formula retains the printed quantifier. The change here is a local
    correction, distinct from the reference correction in the local erratum
    p. 3, book p. 170 lines 24 and 35. Source context and the corrected
    Federer1955 reference: TopologicalCaratheodoryUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum ExtendedRealBounds OpenRefiningEnvelopeUP
  OpenRefiningEnvelopeLaws OpenRefiningEnvelope TopologicalCaratheodoryUP TopologicalCaratheodoryLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_global_open_refinement_bound]: corrected
    strict-threshold property for the topological extension of
    Federer 2.10.1, p. 170. Every open cover of X admits
    a countable generator refinement covering the target A
    with cost strictly below t. A itself need not be open,
    closed or measurable. *)
Definition is_global_open_refinement_bound (R : realType) (X : topologicalType)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (A : set X) (t : \bar R) := forall H, is_whole_space_open_cover H ->
  exists G : set J, countable G /\ A `<=` \bigcup_(j in G) S j /\
    (forall j, G j -> generator_refines_cover S H j) /\ nonnegative_sum G cost<t.

(** Source for [topological_caratheodory_strict_refinement_bound]:
    supporting strict-upper-bound direction of the corrected
    topological version of Federer 2.10.1, p. 170. Every
    fixed-cover infimum lies below the final supremum, so its
    approximation law supplies the required refined cover. *)
Lemma topological_caratheodory_strict_refinement_bound (R : realType) (X : topologicalType)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu : set X -> \bar R) (A : set X) (t : \bar R) :
  is_topological_caratheodory S cost mu -> mu A<t ->
  is_global_open_refinement_bound S cost A t.
Proof.
move=> hm ht H hH.
have hn := open_refining_envelope_specification S cost H.
have hb := @topological_caratheodory_upper R X J S cost mu hm A H _ hH hn.
have [G [hc [hr [hcov hcost]]]] := open_refining_envelope_approximation hn (le_lt_trans hb ht).
exists G; by split=> //; split=> //; split.
Qed.

(** Source for [global_open_refinement_bound_controls_measure]:
    supporting reverse bound in the corrected topological
    version of Federer 2.10.1, p. 170. Every fixed-cover
    infimum is bounded by the cost of its supplied cover;
    the supremum therefore does not exceed the threshold. *)
Lemma global_open_refinement_bound_controls_measure (R : realType) (X : topologicalType)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu : set X -> \bar R) (A : set X) (t : \bar R) :
  is_topological_caratheodory S cost mu ->
  is_global_open_refinement_bound S cost A t -> mu A<=t.
Proof.
move=> hm ht; apply: (topological_caratheodory_least hm)=> H nu hH hn.
have [G [hc [hcov [hr hcost]]]] := ht H hH.
exact: le_trans (@open_refining_envelope_lower R X J S cost H nu hn A G hc hr hcov) (ltW hcost).
Qed.

(** Source for [topological_caratheodory_refinement_characterization]:
    full threshold-infimum formula for the corrected arbitrary-
    topological extension supporting Federer 2.10.1, p. 170.
    The whole-space cover convention is explicit; infinite
    values and empty infimum sets are retained. *)
Theorem topological_caratheodory_refinement_characterization (R : realType) (X : topologicalType)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu : set X -> \bar R) (A : set X) :
  is_topological_caratheodory S cost mu ->
  mu A=extended_real_inf [set t | is_global_open_refinement_bound S cost A t].
Proof.
move=> hm; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: extended_real_inf_greatest=> t ht.
  exact: global_open_refinement_bound_controls_measure hm ht.
- case hval: (mu A)=> [M| |].
  + apply/lee_addgt0Pr=> e he.
    have hb : mu A<(M+e)%R%:E by rewrite hval lte_fin ltrDl.
    have ht := @topological_caratheodory_strict_refinement_bound R X J S cost mu A
      (M+e)%R%:E hm hb.
    rewrite -EFinD; exact: extended_real_inf_lower ht.
  + exact: leey.
  + by have := topological_caratheodory_nonnegative hm A; rewrite hval.
Qed.
