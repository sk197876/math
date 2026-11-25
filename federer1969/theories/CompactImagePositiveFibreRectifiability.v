(** Federer (1969), 3.2.31, p. 269: supporting passage
    from a compact Lipschitz parametrization to its image.
    Hausdorff Lipschitz comparison transfers positive image-fibre
    mass to positive parameter-fibre mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  LipschitzUP MetricLipschitzComposition HausdorffMeasure HausdorffFibreCutoffs HausdorffLipschitzImages
  CompactPositiveFibreRectifiability RectifiableSetUP CountablyMeasureRectifiableOperations MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section CompactImagePositiveFibres.
Variable R:realType.
Variables m n v:nat.
Local Notation P:=(inner_metric_space (@euclidean_inner_productP R m.+1)).
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R n)).
Local Notation Y:=(inner_metric_space (@euclidean_inner_productP R v)).

(** Source for [compact_image_positive_fibre_locus_countably_rectifiable]:
    supporting compact-chart reduction in Federer 3.2.31, p. 269.
    No injectivity or inverse bound is required: a Lipschitz
    image of a null parameter fibre is null in the fibre degree.
    The actual image and original map determine both fibres. *)
Theorem compact_image_positive_fibre_locus_countably_rectifiable (F:X->Y) (psi:P->X)
    (K:set P) L M k mu:
  (0<v)%N ->(0<mu)%N ->m.+1=(k+mu)%N ->
  is_metric_lipschitz_bound setT F L ->is_metric_lipschitz_bound setT psi M ->compact K ->
  is_countably_measure_m_rectifiable (@hausdorff_measure R Y mu) mu
    [set y|0<hausdorff_fibre_mass F (psi @` K) k y].
Proof.
move=>hv hmu hDim hF hPsi hK.
pose G:P->Y:=fun x=>F (psi x).
have hComp:is_metric_lipschitz_bound setT G (L*M)%R.
  exact (@metric_lipschitz_composition_bound R P X Y setT setT psi F M L
    (fun _ _=>Logic.I) hPsi hF).
have hRect:=@compact_positive_fibre_locus_countably_rectifiable R m v G K (L*M)%R k mu
  hv hmu hDim hComp hK.
apply:(countably_measure_rectifiable_subset _ hRect)=>y hy.
have hImage:psi @` (K `&` G @^-1` [set y])=(psi @` K) `&` F @^-1` [set y].
  apply/seteqP; split=>x.
  - move=>[a [ha hGa] <-]; split; first by exists a.
    exact hGa.
  - move=>[[a ha <-] hFa]; exists a=>//; by split.
have hBound:=@hausdorff_lipschitz_image_bound R P X psi M k hPsi (K `&` G @^-1` [set y]).
rewrite hImage in hBound.
change (is_true (0<hausdorff_fibre_mass G K k y)).
rewrite ltNge; apply/negP=>hNonpos.
have hZero:hausdorff_fibre_mass G K k y=0.
  apply/eqP; rewrite eq_le hNonpos /=.
  exact (@measure_nonnegative R P (@hausdorff_measure R P k) (@hausdorff_measure_is_measure R P k)
    (K `&` G @^-1` [set y])).
change (is_true (hausdorff_fibre_mass F (psi @` K) k y<=
  (M^+k)%R%:E*hausdorff_fibre_mass G K k y)) in hBound.
rewrite hZero mule0 in hBound.
have hFalse:=lt_le_trans hy hBound; by rewrite ltxx in hFalse.
Qed.
End CompactImagePositiveFibres.
