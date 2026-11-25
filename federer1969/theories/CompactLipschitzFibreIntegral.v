(** Federer (1969), 3.2.31, p. 269: supporting the compact
    local fibre estimate using the rough inequality 2.10.25,
    pp. 188–189, and the same-bound extension 2.10.43, p. 201. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric EuclideanClosedBallCompact
  LipschitzUP LipschitzFunctionCompact NormMetricScaleContinuity KirszbraunExtensionUP KirszbraunExtensionSealed
  HausdorffMeasure HausdorffFibreCost HausdorffFibreCutoffs HausdorffFibreIntegralBound
  CompactFibreMeasurability MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  PartialExtendedOrderLoci MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureNonnegativeIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section CompactFibreIntegral.
Variable R:realType.
Variables m v:nat.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y:=(inner_metric_space (@euclidean_inner_productP R v)).

(** Source for [compact_lipschitz_fibre_integral_finite_bound]:
    supporting compact-domain form of the inequality used in
    Federer 3.2.31, p. 269. The same Lipschitz bound extends
    opaquely to the whole source; exact agreement identifies every
    actual fibre. Compact fibres give measurability, and finite
    source mass proves a finite nonnegative integral value. *)
Theorem compact_lipschitz_fibre_integral_finite_bound (f:X->Y)
    (K:set X) k mu (L:R):
  compact K ->@hausdorff_measure R X (k+mu) K< +oo ->
  (0<L)%R ->is_metric_lipschitz_bound K f L ->
  exists a:R,is_measure_integral (@hausdorff_measure R Y mu)
    (partial_function_total (hausdorff_fibre_mass f K k)) a%:E /\
    (0<=a)%R /\a%:E<=(@hausdorff_fibre_bound_constant R k mu L)%:E*
      @hausdorff_measure R X (k+mu) K.
Proof.
move=>hK hFinite hL hLip.
pose g:=@KirszbraunExtension.value R m v K f L hLip.
have hg:=@KirszbraunExtension.laws R m v K f L hLip.
have hGlobal:is_metric_lipschitz_bound setT g L:=kirszbraun_extension_bound_law hg.
have hCont:continuous g.
  apply:(metric_fixed_lipschitz_continuous hGlobal.1)=>x y.
  exact (hGlobal.2 x y Logic.I Logic.I).
have hFibre:hausdorff_fibre_mass f K k=hausdorff_fibre_mass g K k.
  apply:funext=>y; rewrite /hausdorff_fibre_mass; congr (hausdorff_measure k _).
  apply/seteqP; split=>x [hx hxy]; split=>//.
  - have he:g x=f x:=kirszbraun_extension_agreement_law hg hx.
    change (g x=y); by rewrite he.
  - have he:g x=f x:=kirszbraun_extension_agreement_law hg hx.
    change (f x=y); by rewrite -he.
have hTarget:metric_boundedly_compact Y.
  move=>b r hr; exact (@euclidean_closed_metric_ball_compact R v b r).
have hRough:=@hausdorff_positive_lipschitz_fibre_integral_bound R X Y g L k mu K
  hGlobal hL (or_intror hTarget).
have hm:=@hausdorff_measure_is_measure R Y mu.
have hMeas:=@compact_hausdorff_fibre_mass_measurable R X Y g K k mu hCont hK.
have hPos:measure_almost_everywhere (@hausdorff_measure R Y mu)
    (partial_extended_nonnegative_locus (partial_function_total (hausdorff_fibre_mass g K k))).
  apply:(measure_almost_everywhere_mono hm _ (measure_almost_everywhere_true hm))=>y _.
  exists (hausdorff_fibre_mass g K k y); split=>//.
  exact (@measure_nonnegative R X (@hausdorff_measure R X k) (@hausdorff_measure_is_measure R X k)
    (K `&` g @^-1` [set y])).
have [hI hI0]:=nonnegative_measurable_function_integral hm hMeas hPos.
have hValue:=measure_upper_integral_unique
  (measure_upper_integral_specification (@hausdorff_measure R Y mu) _) hI.2.1.
rewrite hValue in hRough.
have hC0:0<=(@hausdorff_fibre_bound_constant R k mu L)%:E.
  rewrite lee_fin; exact:hausdorff_fibre_bound_constant_nonnegative (ltW hL).
have hBudget:(@hausdorff_fibre_bound_constant R k mu L)%:E*
    @hausdorff_measure R X (k+mu) K< +oo.
  apply:lte_mul_pinfty=>//.
have hIFinite:measure_lower_integral (@hausdorff_measure R Y mu)
    (partial_function_total (hausdorff_fibre_mass g K k)) \is a fin_num.
  rewrite (ge0_fin_numE hI0); exact:le_lt_trans hRough hBudget.
exists (fine (measure_lower_integral (@hausdorff_measure R Y mu)
  (partial_function_total (hausdorff_fibre_mass g K k)))).
rewrite -hFibre in hI hI0 hRough hIFinite *.
rewrite fineK //; split=>//; split=>//.
by rewrite -lee_fin fineK.
Qed.
End CompactFibreIntegral.
