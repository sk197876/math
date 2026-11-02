(** Federer (1969), 2.10.26, p. 190: supporting zero-source-mass reduction
    through 2.10.25. If the image of a null source set lies in a compact
    set, regard that image codomain as its induced metric space, which is
    boundedly compact. Apply 2.10.25 there and transfer null exceptional
    fibres back by the proved Hausdorff subspace laws. This justifies the
    target hypothesis of 2.10.25 rather than assuming the original target
    proper. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci LipschitzUP
  MetricSubsetBackground CompactMetricSubset HausdorffMetricSubset HausdorffMeasure
  HausdorffFibreCutoffs HausdorffFibreIntegralBound HausdorffFibreCost ZeroUpperIntegral
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureIntegralBounds
  MeasureUpperIntegralNonnegative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [null_hausdorff_fibres_compact_image]: supporting
    null-source case of 2.10.26, p. 190,
    when the source set has compactly contained
    image. No ambient target properness, source-set
    measurability or fibre measurability is assumed. *)
Theorem null_hausdorff_fibres_compact_image (R : realType) (X Y : metricType R)
    (f : X -> Y) (L : R) (A : set X) (K : set Y) k m :
  is_metric_lipschitz_bound setT f L -> compact K -> (f @` A) `<=` K ->
  @hausdorff_measure R X (k+m) A=0 ->
  measure_almost_everywhere (@hausdorff_measure R Y m) [set y | hausdorff_fibre_mass f A k y=0].
Proof.
move=> hf hK himage hA0.
pose U := [the metricType R of metric_subset A].
pose V := [the metricType R of metric_subset K].
have hfx (x : U) : K (f (val x)).
  apply: himage; exists (val x)=> //; exact: set_valP x.
pose g (x : U) : V := Sub (f (val x)) (mem_set (hfx x)).
have hg : is_metric_lipschitz_bound setT g L.
  split; first exact: hf.1.
  move=> x z _ _; rewrite !metric_subset_distanceE; exact: hf.2 (val x) (val z) Logic.I Logic.I.
have hsrc : @hausdorff_measure R U (k+m) setT=0.
  rewrite -hausdorff_metric_subset_measure.
  have he : (fun x : U=>(val x : X)) @` setT=A.
    apply/seteqP; split=> [x [a _ <-]|x hx]; first exact: set_valP a.
    by exists (Sub x (mem_set hx) : U).
  by rewrite he.
have hcond : hausdorff_fibre_integral_condition g setT k m.
  right; exact: compact_metric_subset_boundedly_compact hK.
have hbound := @hausdorff_lipschitz_fibre_integral_bound R U V g L k m setT hg hcond.
rewrite hsrc mule0 in hbound.
pose w := hausdorff_fibre_mass g setT k.
have hw x : 0<=w x := measure_nonnegative (@hausdorff_measure_is_measure R U k) _.
have hpos : measure_almost_everywhere (@hausdorff_measure R V m)
    (partial_extended_nonnegative_locus (partial_function_total w)).
  apply: (@measure_almost_everywhere_mono R V _ (@hausdorff_measure_is_measure R V m)
    setT _ _ (measure_almost_everywhere_true (@hausdorff_measure_is_measure R V m)))=> x _.
  exists (w x); by split.
have hzero : measure_upper_integral (@hausdorff_measure R V m) (partial_function_total w)=0.
  apply/eqP; rewrite eq_le; apply/andP; split; first exact hbound.
  exact: (@measure_upper_integral_nonnegative R V (@hausdorff_measure R V m)
    (@hausdorff_measure_is_measure R V m) (partial_function_total w) hpos).
have he := nonnegative_zero_upper_integral_almost_zero (@hausdorff_measure_is_measure R V m) hw hzero.
pose Q := ~` [set z | w z=0].
have hQ : @hausdorff_measure R V m Q=0 := he.
pose E := ~` [set y | hausdorff_fibre_mass f A k y=0].
have hEQ : E `<=` (fun z : V=>(val z : Y)) @` Q.
  move=> y hy.
  have hyK : K y.
    apply: contrapT=> hyK; apply: hy.
    have hempty : A `&` f @^-1` [set y]=set0.
      apply/seteqP; split=> [x [hx hxy]|x []]; exfalso; apply: hyK.
      rewrite -(hxy : f x=y); apply: himage; by exists x.
    change (hausdorff_fibre_mass f A k y=0).
    rewrite /hausdorff_fibre_mass hempty; exact: measure_empty (@hausdorff_measure_is_measure R X k).
  pose z : V := Sub y (mem_set hyK).
  have hsets : (fun x : U=>(val x : X)) @` (setT `&` g @^-1` [set z])=A `&` f @^-1` [set y].
    apply/seteqP; split.
    - move=> x [a [_ ha] <-]; split; first exact: set_valP a.
      have hgz : g a=z := ha.
      change (f (val a)=y).
      have heq := congr1 (fun b : V=>(val b : Y)) hgz.
      exact heq.
    - move=> x [hx hxy]; exists (Sub x (mem_set hx) : U); last by [].
      split=> //.
      change (g (Sub x (mem_set hx))=z); apply: val_inj; exact hxy.
  have hmass : hausdorff_fibre_mass f A k y=w z.
    rewrite /hausdorff_fibre_mass -hsets; exact: hausdorff_metric_subset_measure.
  exists z; last by [].
  move=> hz; apply: hy.
  change (hausdorff_fibre_mass f A k y=0); by rewrite hmass.
change (@hausdorff_measure R Y m E=0).
apply: (@measure_null_subset R Y (@hausdorff_measure R Y m) (@hausdorff_measure_is_measure R Y m)
  E ((fun z : V=>(val z : Y)) @` Q) hEQ).
by rewrite hausdorff_metric_subset_measure hQ.
Qed.
