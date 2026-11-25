(** Federer (1969), 4.1.18, p. 375: the total-domain
    field carrier retains every original summable partial
    field through a representative agreeing on its exact
    original domain. Reuse the sealed zero extension and
    2.3.2's total extension. Undefined null points receive
    zero, so the original compact carrier is retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric ModuleQuotient
  SubspaceCarrier MeasureUP MeasureAlmostUP MeasurableFunctionUP
  MeasurableNormedFunctionUP MeasurableNormedBasic
  PartialFunctionUP PartialFunctionBasic PartialFunctionExtensionUP
  PartialFunctionExtensionSealed PartialZeroExtension MeasurableTotalExtension
  MeasureLpNorm MeasureLpNormAlmostEquality MeasureLpNormTotal
  TotalMeasurableFunctionSpace CompactSummableFieldUP
  CompactSummableFieldSealed CompactSummableFieldLaws
  LinearSubspaceRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section Representation.
Variable R:realType.
Variable X:topologicalType.
Variable V:lmodType R.
Variable N:V->R.
Variable hN:is_real_norm N.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Local Notation M:=(real_norm_metric_space hN).
Local Notation F:=(GRing.Lmodule.clone R (X->M) _).
Local Notation A:=(@total_measurable_normed_subspace R X V N hN mu hm).
Local Notation W:=(@CompactSummableField.space R X V N hN mu hm).
Local Notation value:=(@compact_summable_field_value R X V N hN mu hm).
Local Notation size:=(@compact_summable_field_size R X V N hN mu hm).

(** Source for [compact_summable_partial_field_representative]:
    every original summable compact field used in Omega_m
    has an actual compact total representative, Federer
    4.1.18, p. 375, through 2.3.2, p. 73.
    Values on the partial domain and the original L1 size
    are preserved exactly; partial domains are not redefined. *)
Theorem compact_summable_partial_field_representative
    (f:partial_function X M)
    (hMeas:is_measurable_normed_function mu f)
    (hFinite:measure_lp_norm mu N 1 f< +oo)
    (K:set X) (hK:compact K)
    (hOff:forall x y,partial_function_graph f x y->~K x->y=0%R):
  exists w:W,
    is_partial_function_total_extension f (value w) /\
    (forall x,~partial_function_domain f x->value w x=0%R) /\
    (forall x,~K x->value w x=0%R) /\
    measure_almost_equal mu f (partial_function_total (value w)) /\
    measure_lp_norm mu N 1 f=(size w)%:E.
Proof.
pose f0:=partial_function_zero_extension (0%R:M) (partial_function_domain f) f.
pose g:=@PartialFunctionExtension.value X M f0 0%R.
pose hG:=@PartialFunctionExtension.laws X M f0 0%R.
have hExtend:is_partial_function_total_extension f g.
  move=>x y hxy;apply:(@hG x y).
  apply/partial_function_zero_extension_graph;left;split.
  - by exists y.
  - exact:hxy.
have hUndefined:forall x,~partial_function_domain f x->g x=0%R.
  move=>x hx;apply:(@hG x 0%R).
  apply/partial_function_zero_extension_graph;right;by split.
have hAlmost:=@partial_function_total_extension_almost_equal R X M mu f g
  (measurable_function_domain hMeas.1) hExtend.
have hGMeas:=@measurable_normed_almost_equal R X V N hN mu hm f
  (partial_function_total g) hMeas hAlmost.
have hEqual:=@measure_lp_norm_almost_equal R X V N hN mu hm 1 f
  (partial_function_total g) (lexx 1) hMeas.1 hGMeas.1 hAlmost.
have hGOff:forall x,~K x->g x=0%R.
  move=>x hx;case:(pselect (partial_function_domain f x))=>[[y hy]|hUndefinedX].
  - exact:(eq_trans (@hExtend x y hy) (@hOff x y hy hx)).
  - exact:(@hUndefined x hUndefinedX).
pose a:=@subspace_lift R F A g hGMeas.
have hA:@compact_summable_field_subspace R X V N hN mu hm a.
  split.
  - change (measure_lp_norm mu N 1 (partial_function_total g)< +oo).
    by rewrite -hEqual.
  - exists K;split;first exact:hK.
    exact:hGOff.
have[w hW]:=@subspace_representation_full R (subspace_space A) W
  (@compact_summable_field_subspace R X V N hN mu hm)
  (@CompactSummableField.inclusion R X V N hN mu hm)
  (@CompactSummableField.laws R X V N hN mu hm) a hA.
have hValue:value w=g.
  by rewrite /compact_summable_field_value hW subspace_liftE.
exists w;split;first by rewrite hValue.
split;first by rewrite hValue.
split;first by rewrite hValue.
split;first by rewrite hValue.
rewrite (@compact_summable_field_size_exact R X V N hN mu hm w).
change (measure_lp_norm mu N 1 f=
  measure_lp_norm mu N 1 (partial_function_total (value w))).
rewrite hValue;exact:hEqual.
Qed.
End Representation.
