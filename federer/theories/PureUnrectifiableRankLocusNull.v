(** Federer (1969), 3.2.21, p. 257: orthogonal
    slicing annihilates every actual differential of rank at least
    mu above the purely unrectifiable Borel target. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  NormDifferentialUP EuclideanBlockLinearMaps EuclideanLinearJacobian EuclideanLebesgueDimensions
  EuclideanLinearMaps OrthogonalMaps MeasureUP MeasureAlmostBasic LipschitzUP
  RectifiableSetUP HausdorffMeasure TopologicalBorel LinearRankAtLeast
  CountableOrthogonalApproximation DenseOrthogonalRankDetection EuclideanOrthogonalPrecompose
  PositiveRestrictedDifferentialLocus PureUnrectifiableSliceNull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [pure_unrectifiable_rank_locus_null]: the
    orthogonal-coordinate and Fubini argument of Federer 3.2.21,
    p. 257, expressed as a null exceptional locus.
    A countable dense orthogonal family detects every bad actual
    differential. No selected derivative field or common uncountable
    exceptional-set intersection is used. The sliced dimension agrees
    with the correction on erratum p. 5, book p. 257 line 26. *)
Lemma pure_unrectifiable_rank_locus_null (R:realType) k mu n
    (v:inner_metric_space (@euclidean_inner_productP R (k+mu))->
      inner_metric_space (@euclidean_inner_productP R n))
    (T:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_metric_lipschitz setT v ->borel_set T ->
  is_purely_measure_m_unrectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) mu) mu T ->
  @euclidean_lebesgue_measure R (k+mu) [set x|T (v x) /\ exists D,
    has_norm_differential (inner_norm (@euclidean_inner_productP R (k+mu)))
      (inner_norm (@euclidean_inner_productP R n)) setT v x D /\
    linear_rank_at_least D mu]=0%E.
Proof.
move=>hLip hT hPure.
pose X:=R_n R (k+mu).
have [S [hCount [hOrth hDense]]]:=@countable_orthogonal_approximation R (k+mu).
pose A:=fun s:Hom X X=>positive_restricted_differential_locus
  (fun x=>v (s x)) (@euclidean_last_injection_map R k mu) T.
pose N:=fun s:Hom X X=>s @` A s.
have hNull s:S s ->@euclidean_lebesgue_measure R (k+mu) (N s)=0%E.
  move=>hSs; apply:(euclidean_orthogonal_image_null (hOrth s hSs)).
  exact:(pure_unrectifiable_slice_positive_locus_null
    (euclidean_orthogonal_precompose_lipschitz (hOrth s hSs) hLip) hT hPure).
have hUnion:=measure_null_countable_union (euclidean_lebesgue_is_measure R (k+mu)) hCount hNull.
apply:(measure_null_subset (euclidean_lebesgue_is_measure R (k+mu)) _ hUnion)=>x [hTx [D [hD hRank]]].
have [s [hSs hPos]]:=dense_orthogonal_rank_detection hDense hRank.
have hS:=hOrth s hSs.
have hInj:=orthogonal_map_injective (@euclidean_inner_productP R (k+mu))
  (@euclidean_inner_productP R (k+mu)) hS.
have hSurj:=euclidean_injective_surjective hInj.
have [y hy]:=hSurj x.
exists s; first exact hSs; exists y; last exact hy.
split; first by rewrite hy.
exists (hom_comp D s); split.
- apply:(euclidean_orthogonal_precompose_differential hS).
  by rewrite hy.
- have hAssoc:hom_comp (hom_comp D s) (@euclidean_last_injection_map R k mu)=
    hom_comp D (hom_comp s (@euclidean_last_injection_map R k mu)).
    by apply:hom_ext=>z; rewrite !hom_compE.
  by rewrite hAssoc.
Qed.
