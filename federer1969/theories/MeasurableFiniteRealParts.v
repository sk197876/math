(** Federer (1969), 3.2.5, p. 245: measurable
    finite real weights have measurable positive and negative
    parts, by the Borel-composition rule of 2.3.2(4). *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground PartialFunctionBasic MeasureUP MeasurableFunctionUP
  BorelFunctionBasic MeasurableTotalBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_real_positive_part_continuous]: supporting
    continuity of the scalar positive part for Federer
    3.2.5, p. 245, using general real topology. *)
Lemma finite_real_positive_part_continuous (R:realType):
  continuous (fun x:real_line_metric R=>(Num.max x 0:real_line_metric R)).
Proof.
move=>x; apply:(@continuous_max R [the topologicalType of real_line_metric R]
  (fun x=>x) (fun _=>0) x); [exact:cvg_id|exact:cvg_cst].
Qed.

(** Source for [finite_real_negative_part_continuous]: supporting
    continuity of the scalar negative part for Federer
    3.2.5, p. 245. *)
Lemma finite_real_negative_part_continuous (R:realType):
  continuous (fun x:real_line_metric R=>(Num.max (-x) 0:real_line_metric R)).
Proof.
move=>x; apply:(@continuous_max R [the topologicalType of real_line_metric R]
  (fun x=>-x) (fun _=>0) x); [exact:cvgN cvg_id|exact:cvg_cst].
Qed.

(** Source for [measurable_finite_real_parts]: positive and
    negative part measurability in the signed approximation
    for Federer 3.2.5, p. 245. *)
Lemma measurable_finite_real_parts (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (g:X->real_line_metric R):
  is_measure_measurable_function mu (partial_function_total g) ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(Num.max (g x) 0:real_line_metric R))) /\
  is_measure_measurable_function mu (partial_function_total (fun x=>(Num.max (-g x) 0:real_line_metric R))).
Proof.
move=>hg; split.
- exact (measurable_total_borel_postcomposition hm hg
    (continuous_borel_function (@finite_real_positive_part_continuous R))).
- exact (measurable_total_borel_postcomposition hm hg
    (continuous_borel_function (@finite_real_negative_part_continuous R))).
Qed.
