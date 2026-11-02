(** Federer (1969), 2.9.24, p. 169: the finite step approximations are
    measurable, so bounded convergence applies to their products with g'.
    The tagged values are constants, hence f itself need not be measurable
    for this finite step. The local Federer erratum has no entry for this
    step. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionBasic MeasureUP BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions
  MeasurableFunctionUP MeasurableTotalBasic MeasurableTotalPiecewise MeasurableGraphEquivalence
  SummableRealFunctionUP MeasurableRealEmbedding TaggedStepFunction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [right_closed_interval_borel]: supporting Borel
    cells {x:a<x<=b} for Federer 2.9.24, p. 169. A
    cell is [a,b] minus [a,a], including the empty case. *)
Lemma right_closed_interval_borel (R : realType) (a b : R) :
  borel_set (`]a,b] : set (real_line_metric R)).
Proof.
have he : (`]a,b] : set (real_line_metric R))=`[a,b] `\` `[a,a].
  apply/seteqP; split=> x; rewrite /= !in_itv /=.
  - move=> /andP[h1 h2]; split; first by rewrite (ltW h1) h2.
    move=> /andP[_ h3]; by have hh := lt_le_trans h1 h3; rewrite ltxx in hh.
  - move=> [/andP[h1 h2] hn].
    case: (ltP a x)=> hx; first exact: h2.
    exfalso; apply: hn; apply/andP; by split.
rewrite he; apply: borel_set_difference; apply: closed_borel_set; exact: segment_closed_real.
Qed.

(** Source for [tagged_step_function_measurable]: supporting
    measurability of the approximations in Federer 2.9.24,
    p. 169. It holds for every Borel regular measure on
    the line and every finite tagged list, without regularity
    assumptions on f or the partition. *)
Lemma tagged_step_function_measurable (R : realType)
    (mu : set (real_line_metric R) -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regular_measure mu) (f : R -> R) (w : seq R) :
  is_measure_measurable_function mu
    (partial_function_total (tagged_step_function f w : real_line_metric R -> real_line_metric R)).
Proof.
have hzero (v : seq R) : (size v<=2)%N -> is_measure_measurable_function mu
    (partial_function_total (tagged_step_function f v : real_line_metric R -> real_line_metric R)).
  move=> hv.
  have he : tagged_step_function f v=(fun _ => 0).
    apply: funext=> x; exact: (@tagged_step_function_short R f v hv x).
  rewrite he; exact (@measurable_total_constant R (real_line_metric R)
    [the topologicalType of real_line_metric R] mu hm 0).
have [n] := ubnP (size w).
elim: n w=> [//|n ih] [|a [|r [|b rest]]] hs;
  try by apply: hzero; rewrite /=.
pose A : set (real_line_metric R) := `]a,b].
have hA : measure_measurable mu A.
  exact: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    mu hm hr _ (right_closed_interval_borel a b)).
have hsize : (size (b::rest)<n)%N by move: hs; rewrite /= !ltnS; exact: ltnW.
have htail := ih (b::rest) hsize.
have he : tagged_step_function f (a::r::b::rest)=
    (fun x => if pselect (A x) then f r else tagged_step_function f (b::rest) x).
  apply: funext=> x; rewrite tagged_step_function_cons.
  case: (pselect (A x))=> hx.
  - have hb : a<x<=b by move: hx; rewrite /A /= in_itv /=.
    by rewrite hb.
  - have hb : (a<x<=b)=false.
      apply/negbTE/negP=> hb; apply: hx; by rewrite /A /= in_itv /=.
    by rewrite hb.
rewrite he; apply: (@measurable_total_piecewise R (real_line_metric R)
  [the topologicalType of real_line_metric R] mu hm A (fun _ => f r)
  (tagged_step_function f (b::rest)) hA _ htail).
exact (@measurable_total_constant R (real_line_metric R)
  [the topologicalType of real_line_metric R] mu hm (f r)).
Qed.

(** Source for [tagged_step_integrand_measurable]: supporting extended-
    real integral convention for the step approximations in Federer
    2.9.24, p. 169. The finite scalar embedding preserves
    measurability and every point value; no extra domain is added. *)
Lemma tagged_step_integrand_measurable (R : realType)
    (mu : set (real_line_metric R) -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regular_measure mu) (f : R -> R) (w : seq R) :
  is_measure_measurable_function mu (real_total_integrand (tagged_step_function f w)).
Proof.
have hf := @tagged_step_function_measurable R mu hm hr f w.
have he := @measurable_total_real_embedding R (real_line_metric R) mu hm
  (tagged_step_function f w) hf.
apply: (@measurable_function_graph_equivalent R (real_line_metric R)
  (extended_real_line R) mu _ _ _ he)=> x z.
by rewrite real_total_integrand_graph.
Qed.
