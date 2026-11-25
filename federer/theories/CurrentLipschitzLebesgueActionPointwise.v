(** Federer (1969), 4.1.25, p. 383: the paired
    smooth image integrands converge at almost every point
    to the literal partial-differential integrand. Rademacher's
    theorem supplies its original conull domain. Critical
    points of the map are retained, without a Jacobian
    denominator or an injectivity qualification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormDifferentialLipschitzBound NormClassOneUP GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  EuclideanHomOperator HomSpaceTopology ExteriorGrading ExteriorMaps
  AlternatingForms AlternatingPairing CurrentCoefficientNorms
  CurrentMapDifferential LipschitzUP Rademacher EuclideanLebesgueDimensions
  MeasureAlmostUP MeasureAlmostBasic PartialDominatedConvergence
  SummableRealFunctionUP RealErrorOrderLimit
  CurrentLipschitzLebesgueActionIntegrand CurrentLipschitzLebesgueActionFamilyUP
  CurrentLipschitzLebesgueActionPullbackLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section LebesgueActionPointwise.
Variable R : realType.
Hypothesis h2 : (1+1:R) != 0.
Variables m n k : nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation QN := (@current_form_comass R h2 n k).
Local Notation Op := (@euclidean_operator_norm R m n).
Local Notation mu := (@euclidean_lebesgue_measure R m).
Local Notation hm := (euclidean_lebesgue_is_measure R m).
Variables (f:X->Y) (L:R) (g:nat->X->Y).
Hypothesis hL : 0<=L.
Hypothesis hLip : forall x y,NY (f x-f y)<=L*NX (x-y).
Hypothesis hFamily : is_current_lipschitz_lebesgue_action_family f L g.
Variable xi : X->exterior_power X k.
Variable phi : Y->A_m Y R^o k.
Hypothesis hPhi : norm_class_zero NY QN setT phi.
Local Notation image i x := (exterior_power_map
  (hom_as_linear (@current_map_differential R m n setT (g i) x)) k (xi x)).

(** Source for [current_lipschitz_lebesgue_action_integrands_ae_limit]:
    the original almost-everywhere integrand convergence in
    the proof of 4.1.25, p. 383. No property
    of the exterior field other than its given values
    is needed for this pointwise step. Summability is
    used only in the subsequent integral domination. *)
Theorem current_lipschitz_lebesgue_action_integrands_ae_limit :
  measure_almost_everywhere mu
    (partial_extended_convergence_locus
      (fun i=>real_total_integrand (fun x=>pairing (image i x) (phi (g i x))))
      (@current_lipschitz_lebesgue_action_integrand R m n k f xi phi)).
Proof.
have hPositive:0<L+1:=ltr_wpDl hL ltr01.
have hWide x y:NY (f x-f y)<=(L+1)*NX (x-y).
  apply:le_trans (hLip x y) _.
  apply:ler_wpM2r; first exact:real_seminorm_nonnegative hNX.1 (x-y).
  by rewrite lerDl.
have hMetric : @is_metric_lipschitz R
    (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R n)) setT f.
  exists (L+1); split=>//; split; [exact: ltW hPositive | move=>x y _ _].
  exact:hWide x y.
have hActual:=@federer_3_1_6 R m n f hMetric.
have hBoth:=measure_almost_everywhere_and hm hActual
  (current_lipschitz_lebesgue_action_family_differential_ae hFamily).
apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hBoth)
  =>x [[D hD] hDifferential].
pose A i:=@current_map_differential R m n setT (g i) x.
pose c:=L+1.
have hC:1<=c by rewrite /c lerDr.
have hLWide:L<=c by rewrite /c lerDl.
have hA i:Op (A i)<=c.
  exact:le_trans
    (current_lipschitz_lebesgue_action_family_differential_bound hFamily i x) hLWide.
have hDOriginal:Op D<=L.
  apply:hom_operator_norm_least; first exact:hL.
  exact:(@norm_differential_global_lipschitz_bound R X Y NX NY hNX hNY
    f x D L hD hLip).
have hB:Op D<=c:=le_trans hDOriginal hLWide.
have hValues:forall eta:R,0<eta ->exists N:nat,forall i:nat,(N<=i)%N ->
    NY (g i x-f x)<eta.
  move=>eta hEta.
  have [N hN]:=current_lipschitz_lebesgue_action_family_uniform hFamily hEta.
  exists N=>i hi;exact:hN i hi x.
have hDifferentials:forall eta:R,0<eta ->exists N:nat,forall i:nat,(N<=i)%N ->
    Op (A i-D)<eta.
  exact:hDifferential D hD.
pose value:=pairing (exterior_power_map (hom_as_linear D) k (xi x)) (phi (f x)).
exists (fun i=>(pairing (image i x) (phi (g i x)))%:E),value%:E.
split; first by move=>i;apply/real_total_integrand_graph.
split.
- apply:(@current_lipschitz_lebesgue_action_integrand_graph R m n k f xi phi x value%:E).2.
  by exists D;split.
- apply:real_error_extended_order_limit.
  exact:(@current_lipschitz_lebesgue_action_point_pairing_limit R h2 m n k
    A D (fun i=>g i x) (f x) c hC hA hB hValues hDifferentials phi hPhi (xi x)).
Qed.
End LebesgueActionPointwise.
