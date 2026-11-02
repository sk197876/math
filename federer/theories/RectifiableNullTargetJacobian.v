(** Federer (1969), 3.2.22, pp. 258–259:
    assemble the compact source charts to prove that the
    intrinsic approximate Jacobian vanishes above the null
    target remainder. Keep the source-chart remainder too. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  LipschitzUP PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionExtensionUP
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureRestriction HausdorffMeasure
  RectifiableSetUP RectifiableCompactChartsUP RectifiableCompactCharts EuclideanRectifiableNullImage
  MeasureApproximateJacobian RectifiableParameterNullTargetJacobian HausdorffZeroNullEmpty.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_null_target_jacobian_zero]:
    ap J_mu f=0 for H^m almost all points above Q,
    Federer 3.2.22, pp. 258–259. For positive
    mu, the chart parameter result follows from 3.2.21;
    2.10.11 transports its null exceptions to each image,
    and countable union with the H^m-null source remainder
    completes the proof. If mu=0, Q is empty by counting
    measure. No Borel premise on Q or new Jacobian domain
    values are assumed. The arbitrary total representative
    must agree with every actual approximate Jacobian value. *)
Theorem rectifiable_null_target_jacobian_zero (R:realType) m n k q
    (W:set (R_n R n)) (F:R_n R n->R_n R k)
    (Q:set (R_n R k)) (J0:R_n R n->R):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R k)) setT F ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k)) q Q=0%E ->
  is_partial_function_total_extension
    (measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W) m q
      (partial_function_source_restrict W (partial_function_total F))) J0 ->
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m)
    (W `&` (F @^-1` Q)) [set w|J0 w=0].
Proof.
move=>hRect hW hF hQ hJ0.
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@hausdorff_measure R Y m.
have hm:=@hausdorff_measure_is_measure R Y m.
have [hq0|hq0]:=eqVneq q 0%N.
- have hQ0:@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k)) 0 Q=0%E.
    by rewrite -hq0.
  have hEmpty:=hausdorff_zero_null_set_empty hQ0.
  rewrite /measure_almost_everywhere_on.
  have hSet:(W `&` (F @^-1` Q)) `\` [set w|J0 w=0]=set0.
    apply/seteqP; split=>[w [[hw hQw] _]|w []].
    by rewrite hEmpty in hQw.
  by rewrite hSet (measure_empty hm).
have hPos:(0<q)%N by rewrite lt0n.
have hTwo:1<(2:R) by rewrite ltr1n.
have [K [psi hCover]]:=@federer_3_2_18 R m n 2 W hRect hW hTwo.
pose E:=fun i:nat=>(K i `&` (fun a=>Q (F (psi i a)))) `\` [set a|J0 (psi i a)=0].
have hENull i:mu (psi i @` E i)=0%E.
  have hChart:=(hCover.1 i).1.
  have hParam:=@rectifiable_parameter_null_target_jacobian R m n k q 2 W
    (K i) (psi i) F Q J0 hPos hTwo hChart (hCover.1 i).2 hW hRect.2 hF hQ hJ0.
  have hLip:@is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R m)) Y setT (psi i).
    exists 2; split; first by rewrite ltr0n.
    exact:rectifiable_chart_global_bound hChart.
  exact:(euclidean_lipschitz_null_image hLip hParam).
have hNullUnion:mu (\bigcup_i psi i @` E i)=0%E.
  have hU:=@measure_null_countable_union R [the choiceType of Y] [the choiceType of (nat:Type)]
    mu hm setT (fun i=>psi i @` E i)
    (@countableP [the countType of (nat:Type)] setT) (fun i _=>hENull i).
  exact hU.
have hNull:mu ((W `\` (\bigcup_i psi i @` K i)) `|` (\bigcup_i psi i @` E i))=0%E.
  exact:(measure_null_union hm hCover.2.2 hNullUnion).
apply:(measure_null_subset hm _ hNull)=>w [[hw hQw] hNotZero].
have [hIn|hIn]:=pselect ((\bigcup_i psi i @` K i) w).
- right; have [i _ [a ha hEq]]:=hIn; exists i; first exact:Logic.I.
  exists a; last exact hEq; split.
  + split; first exact ha.
    change (Q (F (psi i a))); by rewrite hEq.
  + change (~(J0 (psi i a)=0)); by rewrite hEq.
- left; by split.
Qed.
