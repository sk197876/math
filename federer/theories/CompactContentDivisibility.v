(** Supporting Federer (1969), 2.10.47(3), p. 205: attain every intermediate
    content by a compact sublevel slice. A finite cumulative function is
    supplied through its existing opaque interface; compact-level
    neighbourhoods give continuity, and the intermediate-value theorem gives
    the desired slice. The cheap-neighbourhood property remains an explicit
    premise to be established for gamma_i. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal
  topology num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import RealMetricBackground MeasureUP MeasureBasic MeasureRestriction MeasurePushforward
  FiniteCumulativeFunctionUP FiniteCumulativeFunction CompactContentSliceContinuity
  RestrictedCumulativeRange CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_content_intermediate_subset]: supporting
    intermediate-value step in 2.10.47(3), p. 205.
    It is valid for finite outer content on E without
    assuming that the coordinate sublevel sets are measurable. *)
Theorem compact_content_intermediate_subset (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (E : set X)
    (f : X -> real_line_metric R) (y : R) :
  compact E -> continuous f -> (mu E< +oo)%E ->
  (forall t e : R, 0<e -> exists U, [/\ open U,
    (E `&` [set x | f x=t]) `<=` U & (mu (E `&` U)<e%:E)%E]) ->
  0<=y -> (y%:E<=mu E)%E ->
  exists D, [/\ compact D, D `<=` E & mu D=y%:E].
Proof.
move=> hE hf hfinite hopen hy hyE.
case: (eqVneq y 0)=> [->|hyne].
  exists set0; split; [exact: compact0 | by [] | exact: measure_empty hm].
have hypos : 0<y by rewrite lt_def hyne hy.
have hyposE : (0<y%:E)%E by rewrite lte_fin.
have hEpos : (0<mu E)%E := lt_le_trans hyposE hyE.
have hEne : E!=set0.
  apply: contrapT=> hempty.
  have he : E=set0 by apply/seteqP; split=> [x hx|x []]; apply: hempty; by exists x.
  by rewrite he (measure_empty hm) ltxx in hEpos.
pose nu := measure_pushforward f (measure_restrict mu E).
pose hn := measure_pushforward_is_measure f (measure_restrict_is_measure hm E).
have htotal : nu setT=mu E by rewrite /nu /measure_pushforward /measure_restrict preimage_setT setIT.
have hnfin : (nu setT< +oo)%E by rewrite htotal.
pose F := @finite_cumulative_function R nu hn hnfin.
have hF t : mu (E `&` [set x | f x<=t])=(F t)%:E.
  exact (@finite_cumulative_function_specification R nu hn hnfin t).
have hFc := @compact_content_slice_continuous R X mu hm E f F hE hf hF hopen.
have him : compact (f @` E) := continuous_compact (continuous_subspaceT hf) hE.
have himne : f @` E!=set0 by have [x hx] := hEne; exists (f x); by exists x.
have [a [b [ha [hb hbounds]]]] := @compact_real_set_extremes R (f @` E) himne him.
have hab : a<=b := (hbounds a ha).2.
have ha1 : a-1<a by rewrite ltrBlDr ltrDl.
have hlo : E `&` [set x | f x<=a-1]=set0.
  apply/seteqP; split=> [x [hx hxa]|x []].
  have hax := (hbounds (f x) (ltac:(by exists x))).1.
  change (is_true (f x<=a-1)) in hxa.
  have hbad := le_lt_trans hax (le_lt_trans hxa ha1).
  by rewrite ltxx in hbad.
have hhi : E `&` [set x | f x<=b]=E.
  apply/seteqP; split=> x hx; first exact hx.1.
  split=> //; exact: (hbounds (f x) (ltac:(by exists x))).2.
have hFa : F (a-1)=0.
  apply: EFin_inj; by rewrite -(hF (a-1)) hlo (measure_empty hm).
have hFb : mu E=(F b)%:E by rewrite -(hF b) hhi.
have hyb : y<=F b by rewrite hFb lee_fin in hyE.
have hFb0 : 0<=F b := le_trans hy hyb.
have hab' : a-1<=b := le_trans (ltW ha1) hab.
have hseg : {within (`[a-1,b] : set (real_line_metric R)), continuous F} := continuous_subspaceT hFc.
have hybounds : Order.min (F (a-1)) (F b)<=y<=Order.max (F (a-1)) (F b).
  by rewrite hFa min_l ?max_r // hy hyb.
have [t ht hFt] := @IVT R F (a-1) b y hab' hseg hybounds.
exists (E `&` [set x | f x<=t]); split.
- apply: compact_closedI hE _.
  apply: (@preimage_closed X (real_line_metric R) f [set z | z<=t]);
    [by move=> x _; exact: hf | exact: order_closed_lower_ray_closed].
- by move=> x hx; exact hx.1.
- by rewrite hF hFt.
Qed.
