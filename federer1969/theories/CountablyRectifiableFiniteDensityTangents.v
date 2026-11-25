(** Federer (1969), 3.3.18, p. 301: countably assemble
    the actual tangent planes on the original finite-density strata. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  CountablyRectifiableBorelEnlargement RectifiableSetUP RectifiableTangentPlaneUP
  CountablyRectifiablePositiveUpperDensity PositiveFiniteIntegerStrata
  StructureRectifiableDensityStrata StructureDensityStratumTangents
  MeasureUP MeasureBasic MeasureSplit MeasureAlmostUP MeasureAlmostBasic
  BorelRegularMeasureUP TopologicalBorel MetricDensities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countably_rectifiable_finite_density_tangents]: the
    final countable exhaustion in Federer 3.3.18, p. 301.
    Close each original bounded rectifiable image, then use the
    printed positive integer density bands on each image. Their
    actual tangent-plane conclusions and countable null unions
    cover every original point with positive finite upper density;
    the zero-density remainder is already proved null. No carrier
    measurability or finite carrier mass is added. *)
Theorem countably_rectifiable_finite_density_tangents (R:realType) n m
    (psi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_measure psi ->is_borel_regular_measure psi ->psi setT< +oo ->
  is_countably_m_rectifiable m S ->
  measure_almost_everywhere_on psi S [set a|
    upper_metric_density m psi a< +oo ->is_m_dimensional_approximate_tangent m psi a].
Proof.
move=>hPsi hRegular hFinite hS.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Good:=[set a:X|upper_metric_density m psi a< +oo ->is_m_dimensional_approximate_tangent m psi a].
have [G [hG [hClosed hCover]]]:=countably_rectifiable_closed_family_enlargement hS.
pose Band F i:=structure_rectifiable_density_stratum m psi F ((i.+1)%:R:R).
pose B F i:=Band F i `\` Good.
have hNull F i:G F ->psi (B F i)= 0.
  move=>hF.
  have hb:(0<((i.+1)%:R:R))%R by rewrite ltr0n.
  have hPlanes:=@structure_density_stratum_tangent_plane R n m psi F ((i.+1)%:R:R)
    hPsi hRegular hFinite hb (closed_borel_set (hClosed F hF).1) (hClosed F hF).2.
  apply:(measure_null_subset hPsi _ hPlanes)=>a [ha hn]; split; first exact:ha.
  by move=>hPlane; apply:hn=>_.
pose U:=\bigcup_(F in G) \bigcup_i B F i.
have hUNull:psi U= 0.
  apply:(@measure_null_countable_union R [the choiceType of X] [the choiceType of set X]
    psi hPsi G _ hG)=>F hF.
  apply:(@measure_null_countable_union R [the choiceType of X] [the choiceType of (nat:Type)]
    psi hPsi setT _ (countableP setT))=>i _.
  exact:hNull F i hF.
pose P:=[set a:X|0<upper_metric_density m psi a].
have hZero:psi (S `\` P)= 0:=@countably_rectifiable_positive_upper_density R n m psi S
  hPsi (borel_regular_is_regular hPsi hRegular) hS.
have hBadCover:S `\` Good `<=` (S `\` P) `|` U.
  move=>a [ha hn].
  have [hPositive|hNotPositive]:=pselect (P a); last by left; split.
  right.
  have hAtFinite:upper_metric_density m psi a< +oo.
    apply:contrapT=>hNotFinite; apply:hn=>hFiniteAt; exact:False_ind _ (hNotFinite hFiniteAt).
  have hBandValue:(0<upper_metric_density m psi a< +oo)%E by apply/andP; split.
  have [i hIndex]:=positive_finite_integer_stratum hBandValue.
  have [F hF hFa]:=hCover a ha.
  exists F; first exact:hF.
  exists i; first exact:Logic.I.
  split; last exact:hn.
  by split.
have hUnionNull:=measure_null_union hPsi hZero hUNull.
exact:(@measure_null_subset R [the choiceType of X] psi hPsi (S `\` Good)
  ((S `\` P) `|` U) hBadCover hUnionNull).
Qed.
