(** Federer (1969), 3.2.22(2), p. 258: almost
    every fibre of each source/target chart pair is
    countably Hausdorff rectifiable. Transfer the coordinate
    theorem 3.2.15 through both Lipschitz charts. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP LipschitzBasic
  EuclideanLebesgueDimensions HausdorffMeasure MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  RectifiableSetUP CountablyMeasureRectifiableOperations LipschitzRectifiableImages LipschitzFibreRectifiability
  EuclideanRectifiableNullImage MappingMultiplicity RectifiableChartPairPieces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lipschitz_chart_pair_fibres_countably_rectifiable]:
    supporting strict m>mu fibre assertion in Federer
    3.2.22(2), p. 258. Theorem 3.2.15
    gives coordinate fibres up to Lebesgue-null target
    exceptions. Restrict them to A_ij and map through
    psi_i; 2.10.11 maps the exceptional parameters through
    gamma_j to an H^mu-null target set. Fibres
    outside gamma_j(C_j) are empty. No fibre mass
    finiteness or measurability is assumed here. *)
Theorem lipschitz_chart_pair_fibres_countably_rectifiable (R:realType) m n mu v
    (K:set (R_n R m)) (C:set (R_n R mu))
    (psi:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (F:R_n R n->R_n R v)
    (gamma:inner_metric_space (@euclidean_inner_productP R mu)->
      inner_metric_space (@euclidean_inner_productP R v))
    (G:R_n R v->R_n R mu):
  (mu<m)%N ->is_metric_lipschitz setT psi ->is_metric_lipschitz setT gamma ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R mu)) setT (fun a=>G (F (psi a))) ->
  (forall y,C y ->G (gamma y)=y) ->
  measure_almost_everywhere (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) [set z|
      is_countably_measure_m_rectifiable (@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) (m-mu)) (m-mu)
        (mapping_fibre F (rectifiable_chart_pair_piece K C psi F gamma) z)].
Proof.
move=>hDim hPsi hGamma hPhi hG.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose T:=inner_metric_space (@euclidean_inner_productP R mu).
pose Z:=inner_metric_space (@euclidean_inner_productP R v).
pose phi:=fun a:X=>(G (F (psi a)):T).
pose A:=rectifiable_chart_pair_parameters K C psi F gamma.
pose P:=rectifiable_chart_pair_piece K C psi F gamma.
pose rho:=@hausdorff_measure R Y (m-mu).
pose Good:=fun z:Z=>is_countably_measure_m_rectifiable rho (m-mu) (mapping_fibre F P z).
have hr:=@hausdorff_measure_is_measure R Y (m-mu).
have hCoordinate:=@federer_3_2_15 R m mu phi hDim hPhi.
have hGood:measure_almost_everywhere_on (@euclidean_lebesgue_measure R mu) C
    [set y|Good (gamma y)].
  apply:(measure_almost_everywhere_on_implication _ _ _).2.
  apply:(measure_almost_everywhere_mono (euclidean_lebesgue_is_measure R mu) _ hCoordinate)=>y hFy hy.
  have hSub:mapping_fibre phi A y `<=` mapping_fibre phi setT y by move=>a [ha hVal]; by split.
  have hRestricted:=countably_measure_rectifiable_subset hSub hFy.
  have hPsiRestricted:@is_metric_lipschitz R X Y (mapping_fibre phi A y) psi.
    have [L [hL hBound]]:=hPsi; exists L; split; first exact hL.
    exact:(metric_lipschitz_bound_restrict (fun _ _=>Logic.I) hBound).
  have hImage:=countably_hausdorff_rectifiable_lipschitz_image hPsiRestricted hRestricted.
  have hFibre:=@rectifiable_chart_pair_fibre X Y T Z K C psi F gamma G y hG hy.
  change (is_countably_measure_m_rectifiable rho (m-mu) (mapping_fibre F P (gamma y))).
  by rewrite hFibre.
pose B:=C `\` [set y|Good (gamma y)].
have hB0:@euclidean_lebesgue_measure R mu B=0:=hGood.
have hImageNull:=euclidean_lipschitz_null_image hGamma hB0.
apply:(measure_null_subset (@hausdorff_measure_is_measure R Z mu) _ hImageNull)=>z hNotGood.
have [hIn|hIn]:=pselect ((gamma @` C) z).
- have [y hy hValue]:=hIn; exists y; last exact hValue; split; first exact hy.
  move=>hGy; apply:hNotGood; by rewrite -hValue.
- exfalso; apply:hNotGood.
  have hEmpty:mapping_fibre F P z=set0.
    apply/seteqP; split=>[x [[hSource hTarget] hValue]|x []].
    apply:hIn; change ((gamma @` C) z); by rewrite -hValue.
  change (is_countably_measure_m_rectifiable rho (m-mu) (mapping_fibre F P z)).
  rewrite hEmpty; exact:(@countably_measure_rectifiable_null R [the metricType R of Y] rho (m-mu) set0 hr (measure_empty hr)).
Qed.
