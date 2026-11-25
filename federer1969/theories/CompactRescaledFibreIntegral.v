(** Federer (1969), 3.2.31, p. 269: supporting fibre-integral
    estimate after a linear change of target coordinates. The
    actual all-set distortion bound and the compact-source rough
    coarea estimate imply the displayed rescaling inequality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLinearMaps LipschitzUP HausdorffMeasure HausdorffClosedCoverAgreement HausdorffFibreCutoffs HausdorffFibreCost
  CompactFibreMeasurability MeasureUP MeasureBasic BorelRegularMeasureUP
  PartialFunctionUP PartialFunctionBasic MeasurableFunctionUP MeasureIntegralUP MeasureIntegralBounds
  CompactLipschitzFibreIntegral BijectiveFiniteIntegralImageBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section RescaledIntegral.
Variable R:realType.
Variables m v:nat.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y:=(inner_metric_space (@euclidean_inner_productP R v)).

(** Source for [compact_rescaled_fibre_integral_bound]: supporting
    rescaled estimate in Federer 3.2.31, p. 269. Exact inverse
    identities match every fibre, including infinite fibre masses.
    The target distortion is a bound on actual images of arbitrary
    sets. Compact-source measurability and finite integrability
    discharge every hypothesis of image-measure integration. *)
Theorem compact_rescaled_fibre_integral_bound (F:X->Y) (K:set X) k mu
    (T U:Hom (R_n R v) (R_n R v)) (c:R):
  continuous F ->compact K ->@hausdorff_measure R X (k+mu) K< +oo ->
  cancel T U ->cancel U T ->(0<c)%R ->
  (forall A,@hausdorff_measure R Y mu (T @` A)<=c%:E*@hausdorff_measure R Y mu A) ->
  @is_metric_lipschitz_bound R X Y K (fun x=>U (F x)) 1%R ->
  measure_upper_integral (@hausdorff_measure R Y mu)
    (partial_function_total (hausdorff_fibre_mass F K k))<=
      c%:E*((@hausdorff_fibre_bound_constant R k mu 1%R)%:E*
        @hausdorff_measure R X (k+mu) K).
Proof.
move=>hF hK hFinite hTU hUT hc hImage hLip.
pose g:X->Y:=fun x=>U (F x).
have [a [hI [ha0 ha]]]:=@compact_lipschitz_fibre_integral_finite_bound R m v
  g K k mu 1%R hK hFinite ltr01 hLip.
have hFibre:(fun y:Y=>hausdorff_fibre_mass g K k (U y))=hausdorff_fibre_mass F K k.
  apply:funext=>y; rewrite /hausdorff_fibre_mass; congr (hausdorff_measure k _).
  apply/seteqP; split=>x [hx hxy]; split=>//.
  - have he:U (F x)=U y:=hxy.
    have hh:=congr1 T he; by rewrite !hUT in hh.
  - have he:F x=y:=hxy; by rewrite /g /= he.
have hTransMeas:is_measure_measurable_function (@hausdorff_measure R Y mu)
    (partial_function_total (fun y:Y=>hausdorff_fibre_mass g K k (U y))).
  rewrite hFibre; exact:compact_hausdorff_fibre_mass_measurable hF hK.
have hContU:continuous (U:Y->Y).
  exact (@euclidean_linear_continuous R v (hom_as_linear U)).
have hP y:0<=hausdorff_fibre_mass g K k y.
  exact (@measure_nonnegative R X (@hausdorff_measure R X k) (@hausdorff_measure_is_measure R X k)
    (K `&` g @^-1` [set y])).
have hBound:=@bijective_finite_integral_image_bound R Y (@hausdorff_measure R Y mu)
  (@hausdorff_measure_is_measure R Y mu) (@hausdorff_measure_borel_regular R Y mu)
  T U (hausdorff_fibre_mass g K k) a c hTU hUT hContU hc hImage hP hI hTransMeas.
rewrite hFibre in hBound.
apply:le_trans hBound _; apply:lee_wpmul2l=>//.
by rewrite lee_fin; exact:ltW hc.
Qed.
End RescaledIntegral.
