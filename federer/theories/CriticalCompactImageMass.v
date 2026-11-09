(** Federer (1969), 3.4.2(9), p. 316: a compact
    subset of a lower-dimensional manifold has null image in
    every strictly larger Hausdorff degree under a class-one map. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealNormUP NormMetric HomeomorphismUP
  InnerOwnNormTopology RelativeClassUP EuclideanRelativeExtension NormRegularity
  NormClassOneCompactLipschitz LipschitzUP EuclideanSubmanifoldUP
  CompactSubmanifoldRectifiable RectifiableFiniteHausdorffMass
  HausdorffMeasure HausdorffRestrictedLipschitz MeasureUP MeasureBasic
  RealHausdorffMeasure RealHausdorffMeasureLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_compact_submanifold_image_finite_mass]:
    the rectifiability step for gamma=nu in 3.4.2(9),
    p. 316. The compact source has finite gamma-dimensional
    mass. Its original relatively class-one map has an ambient
    extension by 3.1.22 and is Lipschitz on that compact source.
    The actual 2.10.11 bound proves finite image mass, including
    gamma=0 and arbitrary normed targets. *)
Theorem critical_compact_submanifold_image_finite_mass (R:realType) m gamma k
    (S G:set (R_n R m)) (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (f:R_n R m->Y):
  (1<=k)%N ->is_euclidean_submanifold gamma k S ->G `<=` S ->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) G ->
  norm_class_relative (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY S S f 1 ->
  (@hausdorff_measure R (real_norm_metric_space hNY) gamma (f @` G)< +oo)%E.
Proof.
move=>hk hS hGS hG hf.
pose X:=R_n R m.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
have [U [F [hF [hSU hAgree]]]]:=(euclidean_relative_class_extension hNY S S f 1).1 hf.
have hGU:G `<=` U by move=>x hx;exact:hSU x (hGS x hx).
have [L [hL hBound]]:=@norm_class_one_compact_lipschitz R X Y NX NY hNX hNY U G F
  ((norm_class_firstP hNX hNY U F).1 hF) hGU hG.
have hInnerCompact:@compact (inner_metric_space (@euclidean_inner_productP R m)) G.
  have hh:=continuous_compact (continuous_subspaceT (homeomorphism_inverse_continuous
    (inner_own_norm_homeomorphism (@euclidean_inner_productP R m)))) hG.
  by rewrite image_id in hh.
have hRect:=compact_submanifold_rectifiable hk hS hGS hInnerCompact.
have hFinite:(@hausdorff_measure R (real_norm_metric_space hNX) gamma G< +oo)%E.
  rewrite inner_own_norm_hausdorff;exact:rectifiable_finite_hausdorff_mass hRect.
have hImage:f @` G=F @` G.
  apply/seteqP;split.
  - move=>y [x hx hValue];exists x;first exact:hx.
    rewrite -(hAgree x (hGS x hx)).2;exact:hValue.
  - move=>y [x hx hValue];exists x;first exact:hx.
    rewrite (hAgree x (hGS x hx)).2;exact:hValue.
rewrite hImage.
have hEstimate:=@hausdorff_lipschitz_on_bound R (real_norm_metric_space hNX)
  (real_norm_metric_space hNY) G F L gamma G hBound (fun x hx=>hx).
have hFiniteValue:@hausdorff_measure R (real_norm_metric_space hNX) gamma G \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative
    (@hausdorff_measure_is_measure R (real_norm_metric_space hNX) gamma) G)).
  exact:hFinite.
apply:(le_lt_trans hEstimate).
rewrite -(fineK hFiniteValue) -EFinM;exact:ltry.
Qed.

(** Source for [critical_compact_submanifold_higher_image_null]:
    gamma<=nu<tau in the last case of 3.4.2(9), p. 316.
    Finite actual H^gamma image mass and the real-dimensional
    comparison in 2.10.2 imply H^tau image nullity. *)
Theorem critical_compact_submanifold_higher_image_null (R:realType) m gamma k
    (S G:set (R_n R m)) (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (f:R_n R m->Y) (tau:R) (hTau:0<=tau):
  (1<=k)%N ->is_euclidean_submanifold gamma k S ->G `<=` S ->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) G ->
  norm_class_relative (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY S S f 1 ->
  gamma%:R<tau ->@real_hausdorff_measure R (real_norm_metric_space hNY) tau hTau
    (f @` G)=0%E.
Proof.
move=>hk hS hGS hG hf hDegree.
apply:(@real_hausdorff_finite_higher_degree_zero R (real_norm_metric_space hNY)
  gamma%:R tau (ler0n R gamma) hTau (f @` G) hDegree).
rewrite real_hausdorff_measure_natural.
exact:critical_compact_submanifold_image_finite_mass hk hS hGS hG hf.
Qed.
