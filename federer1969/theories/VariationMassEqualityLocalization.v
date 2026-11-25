(** Federer (1969), 2.9.20, p. 166, proof of (2)=>(3): equality of the full
    variation and absolute derivative integral forces equality on each
    subinterval. This proof uses only additive variation and the abstract
    measure laws. Source context: RealAbsoluteContinuityUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength
  MeasureUP AtomlessSegmentSplitting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [variation_mass_equality_subsegment]: direct localisation
    step in Federer 2.9.20, p. 166 If an atomless measure is dominated by
    variation on subsegments and equals it on [a,b], the deficits on the
    three pieces are nonnegative and sum to zero. Cancellation uses only the
    finite outer variations; infinite subtraction is never used. *)
Lemma variation_mass_equality_subsegment (R : realType) (g : R -> R)
    (nu : set R -> \bar R) (a b u v : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  (forall p q : R, measure_measurable nu `[p,q]) ->
  (forall x : R, nu [set x]=0) ->
  (forall p q : R, (a<=p)%R -> (p<=q)%R -> (q<=b)%R ->
    nu `[p,q]<=curve_variation (g : R -> real_line_metric R) p q) ->
  nu `[a,b]=curve_variation (g : R -> real_line_metric R) a b ->
  (a<=u)%R -> (u<=v)%R -> (v<=b)%R ->
  nu `[u,v]=curve_variation (g : R -> real_line_metric R) u v.
Proof.
move=> hg hm hz hbound he hau huv hvb.
have hub := le_trans huv hvb.
have hleft := hbound a u (lexx a) hau hub.
have hright := hbound v b (le_trans hau huv) hvb (lexx b).
have hcmp := leeD (leeD hleft (lexx (nu `[u,v]))) hright.
have hsplit : nu `[a,b]=(nu `[a,u]+nu `[u,v])+nu `[v,b].
  rewrite (@atomless_segment_measure_split R nu a u b hau hub (hm a u) (hz u)).
  by rewrite (@atomless_segment_measure_split R nu u v b huv hvb (hm u v) (hz v)) addeA.
rewrite -hsplit he (@curve_variation_split R [the metricType R of real_line_metric R]
  g a u b hau hub) (@curve_variation_split R [the metricType R of real_line_metric R]
  g u v b huv hvb) addeA in hcmp.
rewrite (@leeD2rE R _ _ _ (@curve_variation_fin_num R
  [the metricType R of real_line_metric R] g hg v b hvb)) in hcmp.
rewrite (@leeD2lE R _ _ _ (@curve_variation_fin_num R
  [the metricType R of real_line_metric R] g hg a u hau)) in hcmp.
by apply/eqP; rewrite eq_le (hbound u v hau huv hvb) hcmp.
Qed.
