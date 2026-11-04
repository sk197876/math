(** Federer (1969), 3.2.48, p. 284: restore completed
    Hausdorff measurable sets after using actual orthonormal
    coordinates in the application of 3.2.22. These supporting
    laws concern full outer measures, in every natural degree. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerMetric FiniteInnerChartUP FiniteInnerChartCompact
  FiniteInnerChartMeasureTransport HausdorffMeasure MeasureUP
  MeasurePushforward PushforwardMeasurableSets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_chart_direct_hausdorff_pushforward]:
    supporting exact measure change in the coarea application
    of 3.2.48, p. 284, by the isometry assertion
    2.10.11, p. 176. Equality holds on all subsets. *)
Lemma finite_inner_chart_direct_hausdorff_pushforward (R:realType) (V:lmodType R)
    B (hB:@is_inner_product R V B) N
    (e:Hom (R_n R N) V) (p:Hom V (R_n R N)) q:
  is_finite_inner_chart B e p ->
  measure_pushforward e (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R N)) q)=
    @hausdorff_measure R (inner_metric_space hB) q.
Proof.
move=>hChart; apply:funext=>A.
have hPre:e @^-1` A=p @` A.
  apply/seteqP; split=>x.
  - move=>hx; exists (e x); first exact hx.
    exact:finite_inner_chart_left_inverse hChart x.
  - move=>[y hy <-]; change (A (e (p y))).
    by rewrite (finite_inner_chart_right_inverse hChart).
rewrite /measure_pushforward hPre.
exact (@finite_inner_chart_inverse_hausdorff R V B hB N e p hChart q A).
Qed.

(** Source for [finite_inner_chart_image_measurable]: completed
    measurable coordinate sets have completed measurable actual
    images, supporting 3.2.48, p. 284. The inverse
    laws and full outer-measure equality discharge the completion
    issue; no Borel restriction is imposed. *)
Lemma finite_inner_chart_image_measurable (R:realType) (V:lmodType R)
    B (hB:@is_inner_product R V B) N
    (e:Hom (R_n R N) V) (p:Hom V (R_n R N)) q (A:set (R_n R N)):
  is_finite_inner_chart B e p ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R N)) q) A ->
  measure_measurable (@hausdorff_measure R (inner_metric_space hB) q) (e @` A).
Proof.
move=>hChart hMeas.
rewrite -(@finite_inner_chart_direct_hausdorff_pushforward R V B hB N e p q hChart).
apply:pushforward_measurable_from_preimage.
have hPre:e @^-1` (e @` A)=A.
  apply/seteqP; split=>x.
  - move=>[y hy hSame].
    have hEqual:y=x.
      have h:=congr1 p hSame.
      by rewrite !(finite_inner_chart_left_inverse hChart) in h.
    by rewrite -hEqual.
  - move=>hx; by exists x.
by rewrite hPre.
Qed.
