(** Federer (1969), 3.2.29, p. 268: the critical image
    of the class-one approximant is Hausdorff null by 3.2.3.
    We discharge the local Lipschitz and finite-measure reductions,
    rather than assuming the approximant globally Lipschitz. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormClassOneUP NormDifferentialUP NormDifferentialLocalAgreement LipschitzUP LipschitzBasic
  KirszbraunExtensionUP KirszbraunExtension MetricClosedBalls MetricOpenShrinking EuclideanLebesgueDimensions
  EuclideanLipschitzClassZero ClassOneCountableLipschitzCover
  EuclideanJacobianRank DifferentialRankLociBorel AreaCriticalImageNull
  MeasureUP MeasureBasic MeasureAlmostBasic HausdorffMeasure TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [class_one_local_critical_image_null]:
    supporting the last equality H^m[f(C\\P)]=0 in
    Federer 3.2.29, p. 268. On any open finite-measure
    Lipschitz neighborhood, extend the map by 2.10.43;
    locality preserves its actual singular differential.
    The Borel critical superset of 3.2.3 controls arbitrary
    subsets without a measurability premise. *)
Lemma class_one_local_critical_image_null (R:realType) m n
    (f:R_n R m->R_n R n)
    (U:set (inner_metric_space (@euclidean_inner_productP R m))) M:
  open U -> (@euclidean_lebesgue_measure R m U < +oo)%E ->
  @is_metric_lipschitz_bound R (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R n)) U f M ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m
    (f @` (U `&` singular_differential_locus f))=0%E.
Proof.
move=>hU hFinite hLip.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose beta:=@hausdorff_measure R Y m.
pose F:=@euclidean_lipschitz_extension R m n U f M hLip.
have hF:=@euclidean_lipschitz_extension_specification R m n U f M hLip.
have hBound:=kirszbraun_extension_bound_law hF.
have hAgreement x (hx:U x):F x=f x:=@kirszbraun_extension_agreement_law R m n U f F M hF x hx.
pose A:=U `&` singular_differential_locus F.
have hA:@borel_set [the topologicalType of X] A.
  apply:(borel_family_binary_intersection (borel_sets_family X) (open_borel_set hU)).
  apply:singular_differential_locus_borel.
  apply:euclidean_lipschitz_norm_class_zero; exact:metric_lipschitz_of_bound hBound.
have hAFinite:(@euclidean_lebesgue_measure R m A < +oo)%E.
  have hSub:A `<=` U by move=>x [hx _]; exact hx.
  exact (le_lt_trans (measure_mono (euclidean_lebesgue_is_measure R m) hSub) hFinite).
have hAZ:beta (F @` A)=0%E.
  apply:(finite_borel_critical_image_null hBound hA _ hAFinite).
  by move=>x [_ hx].
apply:(measure_null_subset (@hausdorff_measure_is_measure R Y m) _ hAZ).
move=>y [x [hx [D [hD hSing]]] <-].
exists x; last exact:hAgreement.
split; first exact hx.
exists D; split; last exact hSing.
have [r [hr hBall]]:=metric_open_contains_closed_ball hU hx.
apply:(@norm_differential_local_agreement R (R_n R m) (R_n R n)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m)) setT setT f F x D r hr _ _ hD).
- by move=>h hh; split.
- move=>h hh _; symmetry; apply:hAgreement.
  apply:hBall.
  change (is_true (inner_norm (@euclidean_inner_productP R m) (x-(x+h))<=r)).
  rewrite opprD addrA subrr add0r inner_normN.
  exact:ltW hh.
Qed.

(** Source for [class_one_critical_image_null]: the nullity
    H^m[f(C\\P)]=0 in Federer 3.2.29, p. 268,
    for every subset of the actual singular locus. A countable
    finite Lipschitz cover proves the stronger full critical-image
    nullity, with no global Lipschitz or finite source-mass premise.
    Natural dimension zero is retained. *)
Theorem class_one_critical_image_null (R:realType) m n
    (f:R_n R m->R_n R n):
  norm_class_one (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m
    (f @` singular_differential_locus f)=0%E.
Proof.
move=>hf.
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose beta:=@hausdorff_measure R Y m.
pose hb:=@hausdorff_measure_is_measure R Y m.
have [C [hC [hT hLocal]]]:=class_one_countable_finite_lipschitz_cover hf.
have hNull U (hU:C U):beta (f @` (U `&` singular_differential_locus f))=0%E.
  have [ho [hFinite [M hM]]]:=hLocal U hU.
  exact (class_one_local_critical_image_null ho hFinite hM).
have hUnion:=@measure_null_countable_union R Y [the choiceType of set (inner_metric_space (@euclidean_inner_productP R m))]
  beta hb C (fun U=>f @` (U `&` singular_differential_locus f)) hC hNull.
apply:(measure_null_subset hb _ hUnion).
move=>y [x hx <-]; have [U hUC hxU]:=hT x I.
exists U; first exact hUC.
exists x; last reflexivity; by split.
Qed.
