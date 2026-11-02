(** A cardinal encoding supporting Federer (1969), 2.2.4, p. 62 To implement
    two disjoint selections, index their requests by pairs (C,b), where b is
    Boolean. Prefixing one binary coordinate embeds this doubled index
    family into the sequence space whenever the original family embeds
    there. A small-prefix well ordering can then be applied directly to the
    requests. This interleaving variant avoids importing a general theorem
    about products of infinite cardinals. Source context:
    SeparableMetricBaseConstruction.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals.
From Federer Require Import SequenceSpace SequenceCoordinates SequenceCylinderHomeomorphism
  CardinalInjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [sequence_cardinal_bound_doubled]: supporting bound on two
    requests per set in Federer 2.2.4, p. 62. The first coordinate records
    the Boolean request and the remaining coordinates record its original
    family member. *)
Lemma sequence_cardinal_bound_doubled (R : realType) (I : choiceType) :
  (@setT I) #<= (@setT (positive_sequence_space R)) ->
  (@setT (I * bool)) #<= (@setT (positive_sequence_space R)).
Proof.
move=> hc; have [g [hg hi]] := cardinal_injection_with_default (positive_sequence_default R) hc.
pose f (p : I * bool) := positive_sequence_prepend (if p.2 then 0%N else 1%N) (g p.1).
apply: (@cardinal_bound_of_injection _ _ setT setT f).
- by move=> p _.
- move=> [i b] [j c] _ _ he.
  have ht := congr1 (@positive_sequence_tail R) he.
  rewrite /f !positive_sequence_tail_prepend in ht.
  have hij : i = j by apply: hi ht; rewrite inE.
  have hh := congr1 (fun n => positive_sequence_coordinates n 0%N) he.
  rewrite /f !positive_sequence_prepend_head in hh.
  have hbool (u v : bool) : (if u then 0%N else 1%N) = (if v then 0%N else 1%N) -> u = v.
    by case: u; case: v.
  have hbc : b = c := hbool b c hh.
  by rewrite hij hbc.
Qed.
