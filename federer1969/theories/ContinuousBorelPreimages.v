(** Federer (1969), 2.2.11, p. 68, last paragraph: the non-Borel example
    transfers through the 2.2.9 embedding. Continuous inverse images of
    Borel sets preserve Borelness, by the generated-family argument printed
    in 2.2.14, p. 70. This supporting development uses only the local 2.2.1
    laws; it does not claim completion of the later Borel-function item.
    Source context: CountableOpenBaseUP.v. *)
From mathcomp Require Import all_boot classical_sets cardinality topology.
From Federer Require Import BorelFamilyUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_preimage_family_laws]: direct supporting family
    assertion in Federer 2.2.14, p. 70: the sets whose inverse images are
    Borel form a Borel family. It is used here for the transfer in 2.2.11,
    p. 68. *)
Lemma borel_preimage_family_laws (X Y : topologicalType) (f : X -> Y) :
  is_borel_family setT [set A : set Y | borel_set (f @^-1` A)].
Proof.
constructor; rewrite /=.
- rewrite preimage_set0; exact: open_borel_set (@open0 X).
- by move=> A _ x _.
- move=> A hA; rewrite setTD -preimage_setC; exact: borel_set_complement hA.
- move=> G hG hc; rewrite preimage_bigcup.
  apply: borel_set_countable_union hc _=> A hA; exact: hG A hA.
- move=> G hG hc hn; rewrite preimage_bigcap.
  apply: borel_set_countable_intersection hc hn _=> A hA; exact: hG A hA.
Qed.

(** Source for [continuous_borel_preimage]: supporting inverse-image fact
    for Federer 2.2.11, p. 68, proved by the generated-family argument of
    2.2.14, p. 70. *)
Theorem continuous_borel_preimage (X Y : topologicalType) (f : X -> Y) :
  continuous f -> forall A, borel_set A -> borel_set (f @^-1` A).
Proof.
move=> hf; apply: (@generated_borel_family_least Y setT (@open Y) _
  (borel_sets_specification Y) [set A | borel_set (f @^-1` A)]).
- exact: borel_preimage_family_laws.
- move=> A hA; apply: open_borel_set; apply: open_comp=> // x _; exact: hf.
Qed.
