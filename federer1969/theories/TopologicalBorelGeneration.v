(** Federer (1969), 2.2.1, p. 60: topological generation criteria when open
    sets have countable closed covers. The stronger closure class may start
    from closed sets; the disjoint-union class may start from open sets. We
    retain Federer's closed generators in the first assertion and prove the
    corresponding open-generator case as well. Source context:
    BorelFamilyUP.v. The corrected empty-generator hypothesis is satisfied
    by open0 and closed0. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import BorelFamilyUP CountablyClosedFamilyUP
  CountablyClosedFamilyBasic BorelGenerationCriterion TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [has_closed_sequence_covers]: Federer 2.2.1,
    p. 60, the stated topological hypothesis: every open set is
    a countable union of closed sets. Sequences may contain empty
    gaps, so finite and empty covering families are included. *)
Definition has_closed_sequence_covers (T : topologicalType) :=
  forall U : set T, open U -> exists C : nat -> set T,
    (forall n, closed (C n)) /\ U = \bigcup_n C n.

(** Source for [borel_generated_by_open_closure]: Federer 2.2.1, p. 60, the
    weakest printed generation criterion for open generators, under
    countable closed covers of open sets. The statement includes either
    union convention, matching both cases. *)
Theorem borel_generated_by_open_closure (d : bool) (T : topologicalType)
    (F : set (set T)) : has_closed_sequence_covers T ->
  is_generated_closed_family d setT (@open T) F -> F = @borel_set T.
Proof.
move=> hcover hF; apply: generated_borel_family_unique _ (borel_sets_specification T).
apply: (@generated_closed_family_borel_criterion d _ setT (@open T) F hF).
- exact: open0.
- move=> U ho; rewrite setTD; have [C [hc he]] := hcover U ho.
  have heC : ~` U = \bigcap_n (~` C n) by rewrite he setC_bigcup.
  rewrite heC; apply: (countably_closed_indexed_intersection (generated_closed_family_laws hF)).
  + exact: countableP.
  + by exists 0%N.
  + move=> n _; apply: (@generated_closed_family_contains d _ setT (@open T) F hF).
    exact: closed_openC (hc n).
Qed.

(** Source for [borel_generated_by_closed_closure]: Federer 2.2.1, p. 60:
    under the same cover hypothesis the Borel sets are the smallest family
    satisfying unrestricted (2),(3) and containing all closed sets. *)
Theorem borel_generated_by_closed_closure (T : topologicalType)
    (F : set (set T)) : has_closed_sequence_covers T ->
  is_generated_closed_family false setT (@closed T) F -> F = @borel_set T.
Proof.
move=> hcover hF; have hl := generated_closed_family_laws hF.
have hopen U : open U -> F U.
  move=> ho; have [C [hc ->]] := hcover U ho.
  apply: (countably_closed_indexed_union hl); first exact: countableP.
  move=> n _; exact: (@generated_closed_family_contains false _ setT (@closed T) F hF _ (hc n)).
have hB : is_generated_borel_family setT (@closed T) F.
  apply: (@generated_closed_family_borel_criterion false _ setT (@closed T) F hF).
  - exact: closed0.
  - move=> C hc; rewrite setTD; exact: hopen _ (closed_openC hc).
apply/seteqP; split.
- apply: (@generated_closed_family_least false _ setT (@closed T) F hF).
  + exact: (@borel_family_countably_closed false _ setT _ (borel_sets_family T)).
  + exact: closed_borel_set.
- exact: (@generated_borel_family_least _ setT (@open T) _ (borel_sets_specification T)
    F (generated_borel_family_laws hB) hopen).
Qed.
