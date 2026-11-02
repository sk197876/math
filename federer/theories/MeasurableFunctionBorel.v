(** Federer (1969), 2.3.2(1)–(2), p. 73: the Borel inverse-image theorem and
    generating-family criterion. The proof uses the local measurable-set
    laws and the sealed generated-Borel-family interface. *)
From mathcomp Require Import all_boot all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionPreimages
  MeasureUP MeasureFiniteClosure MeasureCountableClosure MeasureSplit
  MeasureAlmostUP BorelFamilyUP GeneratedBorel TopologicalBorel MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [conull_partial_function_domain_measurable]: supporting
    domain measurability in Federer 2.3.2, p. 73, first two
    paragraphs, by the null-set law of 2.1.3(6), p. 55. *)
Lemma conull_partial_function_domain_measurable (R : realType) (X : choiceType)
    (Y : Type) (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X Y) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  measure_measurable mu (partial_function_domain f).
Proof.
move=> hd; have hc := @measure_null_measurable R X mu hm (~` partial_function_domain f) hd.
have h := measure_measurable_complement hc; by rewrite setCK in h.
Qed.

(** Source for [measurable_preimage_borel_family]: direct observation
    preceding (1) in Federer 2.3.2, p. 73. The conull-domain
    assumption is retained, even though a measurable domain suffices
    for this intermediate Borel-family fact. *)
Theorem measurable_preimage_borel_family (R : realType) (X Y : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X Y) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  is_borel_family setT [set A | measure_measurable mu (partial_function_preimage f A)].
Proof.
move=> hd; have hD := @conull_partial_function_domain_measurable R X Y mu hm f hd.
constructor.
- change (measure_measurable mu (partial_function_preimage f set0)).
  rewrite partial_function_preimage_empty; exact: measure_measurable_empty hm.
- by move=> A hA x hx.
- move=> A hA; change (measure_measurable mu (partial_function_preimage f (setT `\` A))).
  rewrite setTD partial_function_preimage_complement.
  exact (@measure_measurable_difference R X mu hm _ _ hD hA).
- move=> G hG hc; change (measure_measurable mu (partial_function_preimage f (\bigcup_(A in G) A))).
  rewrite partial_function_preimage_union.
  exact (@measure_measurable_countable_union R X [the choiceType of set Y] mu hm
    G (fun A => partial_function_preimage f A) hc hG).
- move=> G hG hc _; change (measure_measurable mu (partial_function_preimage f (\bigcap_(A in G) A))).
  rewrite partial_function_preimage_intersection.
  apply: (@measure_measurable_intersection R X mu hm _ _ hD).
  exact (@measure_measurable_countable_intersection R X [the choiceType of set Y] mu hm
    G (fun A => partial_function_preimage f A) hc hG).
Qed.

(** Source for [measurable_function_borel_preimage]: direct assertion (1) of
    Federer 2.3.2, p. 73 *)
Theorem measurable_function_borel_preimage (R : realType) (X : choiceType)
    (Y : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X Y) : is_measure_measurable_function mu f ->
  forall A, borel_set A -> measure_measurable mu (partial_function_preimage f A).
Proof.
move=> hf; apply: (@generated_borel_family_least Y setT (@open Y) _
  (borel_sets_specification Y) [set A | measure_measurable mu (partial_function_preimage f A)]).
- exact (@measurable_preimage_borel_family R X Y mu hm f (measurable_function_domain hf)).
- exact: measurable_function_open_preimage hf.
Qed.

(** Source for [measurable_function_generated_criterion]: direct assertion
    (2) of Federer 2.3.2, p. 73 The generating Borel family is given
    abstractly by its specification, with no construction exposed. *)
Theorem measurable_function_generated_criterion (R : realType) (X : choiceType)
    (Y : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X Y) (S F : set (set Y)) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  is_generated_borel_family setT S F -> (forall U, open U -> F U) ->
  (forall A, S A -> measure_measurable mu (partial_function_preimage f A)) ->
  is_measure_measurable_function mu f.
Proof.
move=> hd hF ho hS; constructor=> // U hU.
exact (@generated_borel_family_least Y setT S F hF
  [set A | measure_measurable mu (partial_function_preimage f A)]
  (@measurable_preimage_borel_family R X Y mu hm f hd) hS U (ho U hU)).
Qed.
