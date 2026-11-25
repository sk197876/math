(** Federer (1969), Corollary 2.8.3, p. 143: adequacy for each member of a
    countable family implies adequacy for its union. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP CoveringFamilyUP ContractionCoverUP
  CoverContractionCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [adequate_selection_is_contraction]: supporting inference for
    Federer 2.8.3, p. 143 A zero remainder satisfies every nonnegative
    contraction bound. The factor need not be less than one for this
    auxiliary implication. *)
Lemma adequate_selection_is_contraction (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (F : set (set X)) (A W : set X) (q : R) (G : set (set X)) :
  (0 <= q)%R -> is_adequate_cover_selection mu F A W G ->
  is_contraction_cover_selection mu F A W q G.
Proof.
move=> hq hG; constructor.
- exact: adequate_selection_members hG.
- exact: adequate_selection_disjoint hG.
- exact: adequate_selection_within hG.
- rewrite (adequate_selection_remainder hG).
  apply: mule_ge0; last exact (measure_nonnegative hm _).
  by rewrite lee_fin.
Qed.

(** Source for [adequate_family_has_local_contraction]: the hypothesis of
    2.8.2 follows from adequacy in Federer 2.8.3, p. 143. Countability is
    supplied by the adequate selection. *)
Lemma adequate_family_has_local_contraction (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (F : set (set X)) (A : set X) (q : R) :
  (0 <= q)%R -> family_is_measure_adequate mu F A ->
  has_local_cover_contraction mu F A q.
Proof.
move=> hq ha W hW; have [G hG] := ha W hW.
exists G; split; first exact: adequate_selection_countable hG.
exact (@adequate_selection_is_contraction R X mu hm F A W q G hq hG).
Qed.

(** Source for [adequate_family_countable_union]: direct formalisation of
    Federer 2.8.3, p. 143: if F is adequate for each member of a countable
    K, it is adequate for union K. we follow that proof. The standing
    context is the same as in 2.8.1 and no target measurability or
    disjointness is added. *)
Theorem adequate_family_countable_union (R : realType) (X : metricType R)
    (F K : set (set X)) (mu : set X -> \bar R) :
  is_covering_theory_context F mu -> countable K ->
  (forall A, K A -> family_is_measure_adequate mu F A) ->
  family_is_measure_adequate mu F (\bigcup_(A in K) A).
Proof.
move=> hc hK ha.
have hhalf : (0 < (2^-1 : R) < 1)%R.
  by rewrite invr_gt0 ltr0n /= invf_lt1 ?ltr0n // ltr1n.
apply: (@federer_2_8_2 R X F K mu (fun _ => (2^-1)%R) hc hK).
- by move=> A.
- move=> [A hA] /=.
  exact (@adequate_family_has_local_contraction R X mu
    (covering_context_measure hc) F A (2^-1)%R
    (ltW (andP hhalf).1) (ha A hA)).
Qed.
