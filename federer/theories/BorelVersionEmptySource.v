(** Boundary of the total Borel representative in Federer (1969), 2.3.6, p.
    77. Source context: LusinBorelVersion.v. An empty source requires no
    target point. For nonempty sources an empty target prevents every total
    representative, even when the source measure is zero; this is a local
    qualification. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic MeasureUP MeasureBasic
  MeasureAlmostUP BorelFunctionUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_version_empty_source]: supporting empty-source
    case for the first corollary of Federer 2.3.6, p. 77.
    It complements the inhabited-target statements without adding
    an artificial point to an empty target. *)
Lemma borel_version_empty_source (R : realType) (X Y : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X Y) :
  (forall x : X, False) -> exists h : X -> Y,
    is_borel_function h /\ measure_almost_equal mu f (partial_function_total h).
Proof.
move=> hn; exists (fun x => False_rect Y (hn x)); split.
- move=> U hU; have he : (fun x => False_rect Y (hn x)) @^-1` U = set0.
    apply/seteqP; split=> [x _|x []]; exact: hn x.
  rewrite he; exact: open_borel_set open0.
- rewrite /measure_almost_equal /measure_almost_everywhere.
  have he : (~` partial_function_agreement f
      (partial_function_total (fun x => False_rect Y (hn x)))) = set0.
    apply/seteqP; split=> [x _|x []]; exact: hn x.
  by rewrite he (measure_empty hm).
Qed.
