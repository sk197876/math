(** Federer (1969), 4.1.18, p. 376: finite
    prefixes of the compact coefficient series use the
    original pointwise vector operations and L1 pseudodistance.
    Reuse the opaque field carrier and the earlier
    partial-function norm laws of 2.4.12, pp. 86–87. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier RealNormUP
  NormMetric PartialFunctionUP PartialFunctionBasic PartialNormedArithmetic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableNormedFunctionUP
  MeasurableNormedDifference MeasureLpNorm MeasureLpNormAlmostEquality
  MeasureLpConvergence CompactSummableFieldSealed CompactSummableFieldLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FinitePrefix.
Variable R:realType.
Variable X:topologicalType.
Variable V:lmodType R.
Variable N:V->R.
Variable hN:is_real_norm N.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Local Notation W:=(@CompactSummableField.space R X V N hN mu hm).
Local Notation value:=(@compact_summable_field_value R X V N hN mu hm).
Local Notation size:=(@compact_summable_field_size R X V N hN mu hm).

(** Source for [compact_summable_field_value_zero]: the
    original zero field of Omega_m in Federer 4.1.18,
    p. 375, has its pointwise zero representative. *)
Lemma compact_summable_field_value_zero:value 0=(fun _=>0).
Proof. by rewrite /compact_summable_field_value !linear0. Qed.

(** Source for [compact_summable_field_value_subtract]:
    pointwise subtraction in the original field space,
    supporting the coefficient sums of Federer 4.1.18,
    p. 376. *)
Lemma compact_summable_field_value_subtract (u v:W):
  value (u-v)=(fun x=>value u x-value v x).
Proof. by rewrite /compact_summable_field_value !linearB. Qed.

(** Source for [compact_summable_field_distance]: the
    exact original L1 pseudodistance equals the size
    of the difference, supporting the compact field
    limit in Federer 4.1.18, p. 376. *)
Lemma compact_summable_field_distance (u v:W):
  measure_lp_distance mu N 1
    (partial_function_total (value u))
    (partial_function_total (value v))=(size (u-v))%:E.
Proof.
have hU:=@compact_summable_field_measurable R X V N hN mu hm u.
have hV:=@compact_summable_field_measurable R X V N hN mu hm v.
have hD:=@measurable_normed_function_subtract R X V N hN mu hm
  (partial_function_total (value u)) (partial_function_total (value v)) hU hV.
have hW:=@compact_summable_field_measurable R X V N hN mu hm (u-v).
have hEqual:measure_almost_equal mu
    (partial_vector_subtract (partial_function_total (value u))
      (partial_function_total (value v)))
    (partial_function_total (value (u-v))).
  apply:(@measure_almost_everywhere_mono R X mu hm setT _ _
    (measure_almost_everywhere_true hm))=>x _.
  exists (value u x-value v x);split.
  - apply/partial_vector_subtract_graph;exists (value u x),(value v x);by split=>//;split.
  - by rewrite compact_summable_field_value_subtract.
rewrite /measure_lp_distance
  (@measure_lp_norm_almost_equal R X V N hN mu hm 1 _ _ (lexx 1) hD.1 hW.1 hEqual).
exact:(esym (@compact_summable_field_size_exact R X V N hN mu hm (u-v))).
Qed.

(** Source for [compact_summable_field_prefix_carrier]:
    all finite prefixes retain the original common
    compact carrier, supporting xi=sum xi_i in
    Federer 4.1.18, p. 376. *)
Lemma compact_summable_field_prefix_carrier (K:set X) (u:nat->W):
  (forall i x,~K x->value (u i) x=0)->
  forall k x,~K x->value (\sum_(i<k) u i) x=0.
Proof.
move=>hOff;elim=>[|k ih] x hx.
- by rewrite big_ord0 compact_summable_field_value_zero.
- rewrite big_ord_recr /= compact_summable_field_value_add /= (ih x hx) (hOff k x hx).
  exact:add0r.
Qed.
End FinitePrefix.
