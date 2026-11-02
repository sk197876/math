(** Federer (1969), 3.2.31, pp. 268–269: the full
    original-domain theorem. The Lipschitz function has exactly
    its given partial graph. Its global extension is auxiliary,
    and every fibre is the original partial preimage. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialMetricLipschitz
  EuclideanPartialLipschitzExtension RectifiableFibreThreshold RectifiableSetUP
  HausdorffMeasure HausdorffFibreCutoffs MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section OriginalPartialThreshold.
Variable R:realType.
Variables n v:nat.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R n)).
Local Notation Y:=(inner_metric_space (@euclidean_inner_productP R v)).

(** Source for [federer_3_2_31]: the complete theorem of
    Federer 3.2.31, pp. 268–269. For a finite H^m-measurable
    (H^m,m)-rectifiable domain and a Lipschitz map on exactly
    that domain, the set of target points with complementary
    fibre mass at least lambda>0 is finite (H^mu,mu)-rectifiable.
    Every natural 0<=mu<=m is retained, without an ambient
    dimension bound, finite-fibre premise or chosen differential.
    The conclusion also proves threshold measurability for 3.2.32. *)
Theorem federer_3_2_31 (f:partial_function (R_n R n) (R_n R v)) m mu L (lambda:R):
  (mu<=m)%N ->(0<lambda)%R ->
  is_measure_m_rectifiable (@hausdorff_measure R X m) m (partial_function_domain f) ->
  measure_measurable (@hausdorff_measure R X m) (partial_function_domain f) ->
  @is_partial_metric_lipschitz_bound R X Y f L ->
  measure_measurable (@hausdorff_measure R Y mu)
    [set y:Y|lambda%:E<=@hausdorff_measure R X (m-mu) (partial_function_preimage f [set y])] /\
  is_measure_m_rectifiable (@hausdorff_measure R Y mu) mu
    [set y:Y|lambda%:E<=@hausdorff_measure R X (m-mu) (partial_function_preimage f [set y])].
Proof.
move=>hMu hLambda hRect hMeas hLip.
pose W:=partial_function_domain f.
have [F [hF hGraph]]:=@euclidean_partial_lipschitz_global_extension R n v f L hLip.
have hFibre y:partial_function_preimage f [set y]=W `&` F @^-1` [set y].
  apply/seteqP; split=>x.
  - move=>[z [hxy hz]].
    have hx:W x by exists z.
    have hxy':=hxy; rewrite hGraph in hxy'.
    have hValue:F x=z:=hxy'.2.
    split=>//; by rewrite /= hValue.
  - move=>[hx hValue].
    exists y; split; last reflexivity.
    rewrite hGraph; by split.
have hThreshold:[set y:Y|lambda%:E<=@hausdorff_measure R X (m-mu) (partial_function_preimage f [set y])]=
    [set y:Y|lambda%:E<=@hausdorff_fibre_mass R X Y F W (m-mu) y].
  apply:funext=>y.
  change (is_true (lambda%:E<=@hausdorff_measure R X (m-mu) (partial_function_preimage f [set y]))=
    is_true (lambda%:E<=@hausdorff_fibre_mass R X Y F W (m-mu) y)).
  by rewrite /hausdorff_fibre_mass hFibre.
rewrite hThreshold.
exact (@rectifiable_fibre_threshold_rectifiable R n v F W m mu L lambda
  hMu hLambda hRect hMeas hF).
Qed.
End OriginalPartialThreshold.
