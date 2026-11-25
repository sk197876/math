(** Federer (1969), 3.2.3, pp. 243–244: the
    finite-measure reduction to a Borel subset where the
    actual differential is injective. The leftover source
    has zero Jacobian mass and its image is Hausdorff null. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanLebesgueDimensions EuclideanHausdorffLebesgue EuclideanLipschitzClassZero
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic BorelRegularMeasureUP BorelRegularSandwich
  TopologicalBorel BorelFamilyBasic NormDifferentialUP Rademacher DifferentialRankLociBorel
  InjectiveDifferentialPieceUP EuclideanJacobianRank JacobianDensityMeasure
  AreaCriticalImageNull NullLipschitzArea LipschitzUP HausdorffMeasure AreaBorelReductionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_measurable_injective_area_subset]:
    the Borel finite-measure reduction, Rademacher reduction
    and removal of the critical image in Federer 3.2.3,
    pp. 243–244. No measurability of A's image is
    required as an input. *)
Theorem finite_measurable_injective_area_subset (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (A:set (R_n R m)):
  is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) A ->
  euclidean_lebesgue_measure m A< +oo -> exists C,is_borel_injective_area_subset f A C.
Proof.
move=>hLip hA hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
pose nu:=euclidean_jacobian_measure f.
pose hn:=euclidean_jacobian_measure_is_measure hLip.
pose beta:=@hausdorff_measure R Y m.
pose hb:=@hausdorff_measure_is_measure R Y m.
have [M [hM hBound]]:=hLip.
have hf:=euclidean_lipschitz_norm_class_zero hLip.
have [D [B [hD [hB [hDA [hAB hNull]]]]]]:=borel_regular_finite_sandwich hm
  (euclidean_lebesgue_borel_regular R m) hA hFinite.
pose F:set X:=[set a|norm_differentiable_at (inner_norm (@euclidean_inner_productP R m))
  (inner_norm (@euclidean_inner_productP R n)) setT f a].
pose N1:=A `\` D.
pose N2:=D `\` F.
pose S:=D `&` singular_differential_locus f.
pose C:=D `&` injective_differential_locus f.
have hN1:mu N1=0.
  apply:(measure_null_subset hm _ hNull)=>x [hx hnD].
  by split; first exact:hAB.
have hAE:measure_almost_everywhere mu F:=federer_3_1_6 hLip.
have hN2:mu N2=0.
  apply:(@measure_null_subset R X mu hm N2 (~` F) _ hAE).
  by move=>x [_ hx].
have hS:@borel_set [the topologicalType of X] S.
  exact (borel_family_binary_intersection (borel_sets_family X) hD (singular_differential_locus_borel hf)).
have hC:@borel_set [the topologicalType of X] C.
  exact (borel_family_binary_intersection (borel_sets_family X) hD (injective_differential_locus_borel hf)).
have hSA:S `<=` A by move=>x [hx _]; exact:hDA.
have hSFinite:mu S< +oo:=le_lt_trans (measure_mono hm hSA) hFinite.
have hSCritical:S `<=` singular_differential_locus f by move=>x [_ hx].
have hSImage:beta (f @` S)=0:=finite_borel_critical_image_null hBound hS hSCritical hSFinite.
have hSNu:nu S=0:=critical_jacobian_measure_zero hSCritical.
have hNullImage N:mu N=0 -> beta (f @` N)=0.
  move=>hN; apply:(null_hausdorff_lipschitz_image hBound).
  by rewrite (euclidean_hausdorff_spherical_lebesgue N).1.
have hImage1:beta (f @` N1)=0:=hNullImage N1 hN1.
have hImage2:beta (f @` N2)=0:=hNullImage N2 hN2.
have hNu1:nu N1=0:=euclidean_jacobian_measure_null f hN1.
have hNu2:nu N2=0:=euclidean_jacobian_measure_null f hN2.
have hExcess:A `\` C `<=` (N1 `|` N2) `|` S.
  move=>x [hx hnC].
  case:(pselect (D x))=>hDx; last by left; left; split.
  case:(pselect (F x))=>hFx; last by left; right; split.
  have hSplit:injective_differential_locus f x \/ singular_differential_locus f x.
    exact ((ordinary_differential_rank_split f x).1 hFx).
  case:hSplit=>hi.
  - exfalso; apply:hnC; by split.
  - right; by split.
have hNuExcess:nu (A `\` C)=0.
  apply:(measure_null_subset hn hExcess).
  exact (measure_null_union hn (measure_null_union hn hNu1 hNu2) hSNu).
have hImageCover:f @` (A `\` C) `<=` ((f @` N1) `|` (f @` N2)) `|` (f @` S).
  move=>y [x hx <-]; case:(hExcess x hx)=>[[h1|h2]|h3].
  - left; left; by exists x.
  - left; right; by exists x.
  - right; by exists x.
have hImageExcess:beta (f @` (A `\` C))=0.
  apply:(measure_null_subset hb hImageCover).
  exact (measure_null_union hb (measure_null_union hb hImage1 hImage2) hSImage).
exists C; split; first exact hC.
split; first by move=>x [hx _]; exact:hDA.
split; first by move=>x [_ hx].
by split.
Qed.
