(** Federer (1969), 4.1.25, p. 383: for
    Hausdorff almost every target point, every regular
    source point in the original compact support has
    the same differential image plane. Assemble the
    original countable cover from 3.2.2, p. 242,
    and the full-density comparison of 3.2.17 and
    2.10.19(4), pp. 254 and 181. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureRestriction HausdorffMeasure LipschitzUP EuclideanLipschitzClassZero
  InjectiveDifferentialPieceUP InjectiveDifferentialCover
  MeasureApproximateTangentUP CurrentAreaPieceTangentCore.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section RegularFibreTangents.
Variable R : realType.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation H := (@hausdorff_measure R Y m).
Variable f : X -> Y.
Variable K : set X.
Hypothesis hLip : is_metric_lipschitz setT f.
Hypothesis hK : compact K.
Local Notation Plane := (fun y => measure_approximate_tangent_cone hNY
  (measure_restrict H (f @` K)) m y).

(** Source for [current_area_regular_fibre_tangents]:
    the common differential-image plane in the proof
    of Federer 4.1.25, p. 383. The exceptional
    target set is independent of the source point
    and of its differential witness. Global injectivity,
    differentiability everywhere and a new plane choice
    are not imposed. *)
Theorem current_area_regular_fibre_tangents :
  measure_almost_everywhere H [set y | forall x, K x -> f x = y ->
    forall D : Hom (R_n R m) (R_n R n),
      has_norm_differential NX NY setT f x D -> injective D ->
      Plane y = range D].
Proof.
have hH := @hausdorff_measure_is_measure R Y m.
have hTwo : (1 < (2 : R))%R by rewrite ltr1n.
have [G hG] := injective_differential_borel_cover_exists
  (euclidean_lipschitz_norm_class_zero hLip) hTwo.
pose P (E : set X) := [set y | forall x, (E `&` K) x -> f x = y ->
  forall D : Hom (R_n R m) (R_n R n),
    has_norm_differential NX NY setT f x D -> Plane y = range D].
have hOne E : G E -> measure_almost_everywhere H (P E).
  move=> hE.
  have [S [_ [_ [hLoss hPlane]]]] :=
    @current_area_piece_tangent_core R m n f K hLip hK 2%R E (hG.2.2 E hE).
  pose Bad := f @` ((E `&` K) `\` S).
  have hOff : measure_almost_everywhere H (~` Bad).
    by rewrite /measure_almost_everywhere setCK; exact: hLoss.
  apply: (measure_almost_everywhere_mono hH _
    (measure_almost_everywhere_and hH hOff hPlane)) => y [hNotBad hAt] x hx hXY D hD.
  have hS : S x.
    apply: contrapT => hOutside.
    apply: hNotBad; exists x; last exact: hXY.
    by split.
  exact: hAt x hS hXY D hD.
have hEvery := @measure_almost_everywhere_countable R Y [the choiceType of set X]
  H hH G P hG.1 hOne.
apply: (measure_almost_everywhere_mono hH _ hEvery) => y hAt x hxK hXY D hD hInjective.
have hLocus : injective_differential_locus f x by exists D; split.
rewrite -hG.2.1 in hLocus.
have [E hE hxE] := hLocus.
exact: hAt E hE x (conj hxE hxK) hXY D hD.
Qed.
End RegularFibreTangents.
