(** Federer (1969), 3.2.3, p. 243: the two
    Lipschitz maps on a Borel piece compare its image measures.
    This supporting relative-domain version of 2.10.11 uses
    the intrinsic subset metric and ambient/subset equality. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import LipschitzUP MetricSubsetBackground HausdorffMeasure
  HausdorffLipschitzImages HausdorffMetricSubset.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_lipschitz_on_bound]: the image
    comparisons in Federer 3.2.3, p. 243, using
    2.10.11 for maps defined only on their actual subset
    domain. No extension theorem or measurability is needed. *)
Theorem hausdorff_lipschitz_on_bound (R:realType) (X Y:metricType R)
    (E:set X) (f:X->Y) (L:R) k (A:set X):
  is_metric_lipschitz_bound E f L -> A `<=` E ->
  @hausdorff_measure R Y k (f @` A)<=(L^+k)%R%:E* @hausdorff_measure R X k A.
Proof.
move=>hf hA.
pose T:=[the metricType R of metric_subset E].
pose v:=fun x:T=>(val x:X).
pose g:=fun x:T=>f (v x).
pose B:set T:=v @^-1` A.
have hval:v @` B=A.
  apply/seteqP; split=>x.
  - by move=>[z hz <-].
  - move=>hx; exists (@exist X (fun t=>t \in E) x (mem_set (hA x hx))); by [].
have hImage:g @` B=f @` A by rewrite -hval -image_comp.
have hg:is_metric_lipschitz_bound setT g L.
  split; first exact hf.1.
  move=>x y _ _; rewrite metric_subset_distanceE.
  exact (hf.2 (v x) (v y) (set_valP x) (set_valP y)).
have hh:=@hausdorff_lipschitz_image_bound R T Y g L k hg B.
rewrite hImage -(@hausdorff_metric_subset_measure R X E k B) hval in hh.
exact hh.
Qed.
