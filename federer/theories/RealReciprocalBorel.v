(** Federer (1969), 3.1.4, p. 214: measurability of the coordinate
    difference quotient. The scalar reciprocal is continuous off zero;
    assigning its algebraic default at zero gives a Borel function.
    The actual derivative quotient is separately restricted to t<>0. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground BorelFunctionUP TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_reciprocal_borel]: supporting scalar arithmetic
    for the jointly measurable quotient in Federer 3.1.4, p. 214.
    Only continuity away from zero and the closed singleton are used. *)
Lemma real_reciprocal_borel (R : realType) :
  @is_borel_function [the topologicalType of real_line_metric R]
    [the topologicalType of real_line_metric R] (fun t=>t^-1).
Proof.
move=> U hU.
have hzero : closed [set (0 : real_line_metric R)].
  apply: accessible_closed_set1; apply: hausdorff_accessible.
  exact: (@metric_hausdorff R [the metricType R of real_line_metric R]).
have hpunctured : open [set t : real_line_metric R | t!=0 /\ U t^-1].
  rewrite openE=> t [ht hu].
  have hn : nbhs t (~` [set (0 : real_line_metric R)]).
    apply: open_nbhs_nbhs; split; first exact: closed_openC hzero.
    by move=> he; move: ht; rewrite he eqxx.
  have hUinv : nbhs (t^-1 : real_line_metric R) U.
    apply: open_nbhs_nbhs; by split.
  have hinv : nbhs t ((fun z : real_line_metric R=>z^-1) @^-1` U).
    exact: (@inv_continuous R t ht U hUinv).
  apply: (filterS _ (filterI hn hinv))=> z [hz huz]; split=> //.
  by apply/eqP=> he; apply: hz.
case: (pselect (U 0))=> h0.
- have he : (fun t : real_line_metric R=>t^-1) @^-1` U=
      [set (0 : real_line_metric R)] `|` [set t | t!=0 /\ U t^-1].
    apply/seteqP; split=> t ht.
    + case: (eqVneq t 0)=> [->|ht0]; [by left|right; by split].
    + move: ht=> [->|[_ ht]]=> //; by rewrite /= invr0.
  rewrite he; apply: (borel_family_binary_union (borel_sets_family [the topologicalType of real_line_metric R])).
  + exact: closed_borel_set hzero.
  + exact: open_borel_set hpunctured.
- have he : (fun t : real_line_metric R=>t^-1) @^-1` U=
      [set t | t!=0 /\ U t^-1].
    apply/seteqP; split=> t ht; last exact ht.2.
    split=> //; apply/eqP=> he; apply: h0; by move: ht; rewrite he /= invr0.
  rewrite he; exact: open_borel_set hpunctured.
Qed.
