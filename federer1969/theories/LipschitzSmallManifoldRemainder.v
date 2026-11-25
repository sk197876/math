(** Federer (1969), 3.2.29, p. 268: combine the actual
    class-one approximation, full-rank local images and null
    critical image to obtain arbitrarily small uncovered images. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets cardinality constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormRegularity NormClassOneUP LinearRankAtLeast LinearFullRank FiniteCoordinates
  EuclideanSubmanifoldUP RectifiableManifoldCoverUP FullRankManifoldImages
  LipschitzClassOneApproximation ClassOneCriticalImageNull ManifoldCoverImageRemainder
  EuclideanJacobianRank LipschitzUP HausdorffMeasure HausdorffLipschitzImages EuclideanHausdorffLebesgue
  MeasureUP MeasureBasic MeasureAlmostBasic MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_small_manifold_remainder]: the two
    final image estimates in Federer 3.2.29, p. 268.
    The image outside a countable family of class-one manifolds
    has mass at most epsilon times the original Lipschitz bound
    to the source dimension. Use the valid remainder containment,
    rather than the printed set equality, which need not hold
    when error images overlap the covered image. *)
Theorem lipschitz_small_manifold_remainder (R:realType) m n
    (F:inner_metric_space (@euclidean_inner_productP R m.+1)->
      inner_metric_space (@euclidean_inner_productP R n)) L e:
  is_metric_lipschitz_bound setT F L ->0<e ->
  exists C:set (set (R_n R n)),countable C /\
    (forall S,C S ->@is_euclidean_submanifold R n m.+1 1 S) /\
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.+1
      ((F @` setT) `\` \bigcup_(S in C) S)<=(L^+m.+1*e)%:E)%E.
Proof.
move=>hLip he.
pose X:=inner_metric_space (@euclidean_inner_productP R m.+1).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose beta:=@hausdorff_measure R Y m.+1.
pose hb:=@hausdorff_measure_is_measure R Y m.+1.
have [f [hf hError]]:=lipschitz_class_one_small_disagreement hLip he.
have hOne:=(@norm_class_firstP R (R_n R m.+1) (R_n R n)
  (inner_norm (@euclidean_inner_productP R m.+1)) (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m.+1))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f).1 hf.
have [D hD]:=hOne.
pose P:=[set x|linear_rank_at_least (D x) m.+1].
have [C [hC [hMan hImage]]]:=full_rank_countable_manifold_images hf hD.
exists C; split; first exact hC.
split; first exact hMan.
pose A:=[set x|F x=f x].
have hCritical:A `\` P `<=` singular_differential_locus f.
  move=>x [_ hnP]; exists (D x); split.
  - exact (@norm_class_one_differential R (R_n R m.+1) (R_n R n)
      (inner_norm (@euclidean_inner_productP R m.+1)) (inner_norm (@euclidean_inner_productP R n))
      setT f D hD x Logic.I).
  - move=>hi; apply:hnP; exact:(linear_full_rankP (@coordinate_basisP R m.+1) (D x)).2 hi.
have hZero:beta (f @` (A `\` P))=0%E.
  apply:(measure_null_subset hb _ (class_one_critical_image_null hOne)).
  by move=>y [x hx <-]; exists x; first exact:hCritical; reflexivity.
have hCover:(F @` setT) `\` \bigcup_(S in C) S `<=`
    F @` (~` A) `|` f @` (A `\` P).
  rewrite -hImage.
  have hh:=@agreement_image_cover_remainder (R_n R m.+1) (R_n R n) F f setT A P (fun x hx=>esym hx).
  by rewrite setTD in hh.
have hImageBound:=@hausdorff_lipschitz_image_bound R X Y F L m.+1 hLip (~` A).
rewrite (euclidean_hausdorff_spherical_lebesgue (~` A)).1 in hImageBound.
have hErrorBound:(beta (F @` (~` A))<=(L^+m.+1*e)%:E)%E.
  apply:le_trans hImageBound _.
  rewrite EFinM.
  apply:lee_wpmul2l.
  - rewrite lee_fin; exact (exprn_ge0 m.+1 (proj1 hLip)).
  - exact:ltW hError.
have hh:=@measure_binary_cover R Y beta hb
  ((F @` setT) `\` \bigcup_(S in C) S) (F @` (~` A)) (f @` (A `\` P)) hCover.
rewrite hZero adde0 in hh.
exact:le_trans hh hErrorBound.
Qed.
