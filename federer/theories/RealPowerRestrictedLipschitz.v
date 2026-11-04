(** Federer (1969), 3.2.46, printed p. 281: supporting real-degree
    Lipschitz comparison on an actual local patch. The source map need
    only satisfy its bound on E. Use the induced subset metric, never a
    global extension or a completed-measurability preimage assumption. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import LipschitzUP MetricSubsetBackground MetricRealPowerMeasure RealPower
  RealPowerPositiveLipschitz RealPowerMetricSubset RealHausdorffMeasure
  RealHausdorffNormalisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_real_power_on_positive_lipschitz]: the real-degree image
    comparison in Federer 3.2.46, p. 281, using
    the covering argument of 2.10.11, p. 176, on the actual patch. No extension theorem or measurability is needed. *)
Theorem metric_real_power_on_positive_lipschitz (R:realType) (X Y:metricType R)
    (E:set X) (f:X->Y) (L c p:R) (A:set X):
  (0<L)%R -> (0<=c)%R -> (0<=p)%R ->
  is_metric_lipschitz_bound E f L -> A `<=` E ->
  @metric_real_power_measure R Y c p (f @` A)<=(real_power L p)%:E* @metric_real_power_measure R X c p A.
Proof.
move=> hL hc hp hf hA.
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
have hh:=@metric_real_power_positive_lipschitz R T Y g L c p hL hc hp hg B.
rewrite hImage -(@metric_real_power_metric_subset_measure R X E c p B hc hp) hval in hh.
exact hh.
Qed.

(** Source for [real_hausdorff_on_positive_lipschitz]: the actual
    Gamma-normalized local image comparison in every real degree,
    supporting Federer 3.2.46, p. 281. *)
Theorem real_hausdorff_on_positive_lipschitz (R : realType)
    (X Y : metricType R) (E : set X) (f : X -> Y) (L p : R)
    (hp : (0<=p)%R) (A : set X) :
  (0<L)%R -> is_metric_lipschitz_bound E f L -> A `<=` E ->
  @real_hausdorff_measure R Y p hp (f @` A) <=
    (real_power L p)%:E * @real_hausdorff_measure R X p hp A.
Proof.
move=> hL hf hA.
exact: (@metric_real_power_on_positive_lipschitz R X Y E f L
  (real_hausdorff_normalisation hp) p A hL
  (ltW (real_hausdorff_normalisation_positive hp)) hp hf hA).
Qed.
