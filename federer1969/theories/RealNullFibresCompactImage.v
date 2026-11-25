(** Federer (1969), 2.10.26, p. 190: supporting zero-source-mass reduction
    through 2.10.25. If the image of a null source set lies in a compact
    set, regard that image codomain as its induced metric space, which is
    boundedly compact. Apply 2.10.25 there and transfer null exceptional
    fibres back by the proved Hausdorff subspace laws. This justifies the
    target hypothesis of 2.10.25 rather than assuming the original target
    proper. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealHausdorffMeasure RealHausdorffNormalisation RealPowerCoverVariants MetricRealPowerCost
  RealHausdorffFibreCutoffs RealHausdorffMetricSubset RealHausdorffFibreIntegralBound ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci LipschitzUP
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

(** Source for [null_real_hausdorff_fibres_compact_image]: supporting
    null-source case of 2.10.26, p. 190,
    when the source set has compactly contained
    image. No ambient target properness, source-set
    measurability or fibre measurability is assumed. *)
Theorem null_real_hausdorff_fibres_compact_image (R : realType) (X Y : metricType R)
    (f : X -> Y) (L : R) (A : set X) (K : set Y) (k m : R) (hk : (0<=k)%R) (hm : (0<=m)%R) :
  is_metric_lipschitz_bound setT f L -> compact K -> (f @` A) `<=` K ->
  @real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A=0 ->
  measure_almost_everywhere (@real_hausdorff_measure R Y m hm) [set y | real_hausdorff_fibre_mass f A hk y=0].
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
have hsrc : @real_hausdorff_measure R U (k+m)%R (addr_ge0 hk hm) setT=0.
  rewrite -real_hausdorff_metric_subset_measure.
  have he : (fun x : U=>(val x : X)) @` setT=A.
    apply/seteqP; split=> [x [a _ <-]|x hx]; first exact: set_valP a.
    by exists (Sub x (mem_set hx) : U).
  by rewrite he.
have hcond : real_hausdorff_fibre_integral_condition g setT hk hm.
  right; exact: compact_metric_subset_boundedly_compact hK.
have hbound := @real_hausdorff_lipschitz_fibre_integral_bound R U V g L k m hk hm setT hg hcond.
rewrite hsrc mule0 in hbound.
pose w := real_hausdorff_fibre_mass g setT hk.
have hw x : 0<=w x := measure_nonnegative (@real_hausdorff_measure_is_measure R U k hk) _.
have hpos : measure_almost_everywhere (@real_hausdorff_measure R V m hm)
    (partial_extended_nonnegative_locus (partial_function_total w)).
  apply: (@measure_almost_everywhere_mono R V _ (@real_hausdorff_measure_is_measure R V m hm)
    setT _ _ (measure_almost_everywhere_true (@real_hausdorff_measure_is_measure R V m hm)))=> x _.
  exists (w x); by split.
have hzero : measure_upper_integral (@real_hausdorff_measure R V m hm) (partial_function_total w)=0.
  apply/eqP; rewrite eq_le; apply/andP; split; first exact hbound.
  exact: (@measure_upper_integral_nonnegative R V (@real_hausdorff_measure R V m hm)
    (@real_hausdorff_measure_is_measure R V m hm) (partial_function_total w) hpos).
have he := nonnegative_zero_upper_integral_almost_zero (@real_hausdorff_measure_is_measure R V m hm) hw hzero.
pose Q := ~` [set z | w z=0].
have hQ : @real_hausdorff_measure R V m hm Q=0 := he.
pose E := ~` [set y | real_hausdorff_fibre_mass f A hk y=0].
have hEQ : E `<=` (fun z : V=>(val z : Y)) @` Q.
  move=> y hy.
  have hyK : K y.
    apply: contrapT=> hyK; apply: hy.
    have hempty : A `&` f @^-1` [set y]=set0.
      apply/seteqP; split=> [x [hx hxy]|x []]; exfalso; apply: hyK.
      rewrite -(hxy : f x=y); apply: himage; by exists x.
    change (real_hausdorff_fibre_mass f A hk y=0).
    rewrite /real_hausdorff_fibre_mass hempty; exact: measure_empty (@real_hausdorff_measure_is_measure R X k hk).
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
  have hmass : real_hausdorff_fibre_mass f A hk y=w z.
    rewrite /real_hausdorff_fibre_mass -hsets; exact: real_hausdorff_metric_subset_measure.
  exists z; last by [].
  move=> hz; apply: hy.
  change (real_hausdorff_fibre_mass f A hk y=0); by rewrite hmass.
change (@real_hausdorff_measure R Y m hm E=0).
apply: (@measure_null_subset R Y (@real_hausdorff_measure R Y m hm) (@real_hausdorff_measure_is_measure R Y m hm)
  E ((fun z : V=>(val z : Y)) @` Q) hEQ).
by rewrite real_hausdorff_metric_subset_measure hQ.
Qed.
