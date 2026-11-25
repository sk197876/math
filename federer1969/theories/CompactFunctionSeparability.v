(** Federer (1969), 2.5.20, p. 114: E=K(Y) is separable in its supremum norm
    when Y is compact metric. The proof chooses one representative from each
    nonempty finite rational cell over a countable open base. The countable
    approximation is proved here, rather than assumed as an extra hypothesis
    of disintegration. Source context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology lra.
From Federer Require Import RealNormUP NormMetric CountableOpenBaseUP VectorDaniellHypotheses
  CompactFunctionSpaceUP CompactFunctionSpaceLaws CompactFunctionCountableCells CompactMetricSeparability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_countable_base_function_space_separable]:
    supporting separability of E=K(Y) in Federer 2.5.20,
    p. 114. This version needs compactness and a countable
    base; a metric supplies the base in the following theorem. *)
Theorem compact_countable_base_function_space_separable (R : realType) (Y : topologicalType)
    (E : lmodType R) (ev : E -> Y -> R) (hE : is_compact_function_space ev)
    (B : nat -> set Y) :
  compact (@setT Y) -> is_countable_open_base B ->
  is_separable_normed_space (compact_function_norm_laws hE).
Proof.
move=> hY hB.
pose J := [the countType of (seq (nat*rat*rat) : Type)].
pose C := @compact_function_interval_cell R Y E ev B.
have hchoice (s : J) : exists v : E, (exists u, C s u) -> C s v.
  case: (pselect (exists u, C s u))=> [[v hv]|hn].
  - exists v=> _; exact hv.
  - exists 0=> h; exact: False_ind _ (hn h).
pose pick (s : J) := projT1 (cid (hchoice s)).
have hpick s := projT2 (cid (hchoice s)).
exists (pick @` setT); split.
- apply: sub_countable (card_image_le _ _) _; exact: countableP.
- move=> U [v hv] hU.
  have hn : nbhs v U by rewrite openE in hU; exact: hU v hv.
  have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP v U) hn.
  have hd : 0<e/2 by rewrite divr_gt0 // ltr0n.
  have [s [hc [hw hs]]] := @compact_function_interval_cell_cover R Y E ev B hE hB v (e/2) hY hd.
  have hp : C s (pick s) by apply: hpick; exists v.
  exists (pick s); split; last by exists s.
  apply: hb.
  have hbound := @compact_function_same_cell_norm_bound R Y E ev B hE s v (pick s)
    (e/2) (ltW hd) hc (fun j hj => ltW (hw j hj)) hs hp.
  have hhalf : e/2<e by rewrite ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
  exact: le_lt_trans hbound hhalf.
Qed.

(** Source for [compact_metric_function_space_separable]: the
    separability requirement (1) of 2.5.12 is verified for
    the actual E=K(Y) in Federer 2.5.20, p. 114.
    Empty compact metric spaces are included. *)
Theorem compact_metric_function_space_separable (R : realType) (Y : metricType R)
    (E : lmodType R) (ev : E -> Y -> R) (hE : is_compact_function_space ev) :
  compact (@setT Y) -> is_separable_normed_space (compact_function_norm_laws hE).
Proof.
move=> hY; have [B hB] := compact_metric_countable_open_base hY.
exact: (@compact_countable_base_function_space_separable R Y E ev hE B hY hB).
Qed.
