(** Federer (1969), 3.4.8(11), p. 333:
    an analytic function is constant on
    each connected component of its critical set.
    Reuse the proved critical-image theorem 3.4.3
    and connected-length bound 2.10.12 rather
    than repeat differentiation in manifold charts. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormDifferentialUP NormClassOneUP NormRegularity
  NormAnalyticUP NormAnalyticLocal NormClassZeroTopology LinearRankUP
  CriticalRankDegreeComparison CriticalValueUpperTheorem RealHausdorffMeasure HausdorffMeasure
  ConnectedHausdorffNullConstancy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_critical_connected_constancy]:
    the critical-component constancy used in
    3.4.8(11), p. 333. The earlier
    critical-image theorem gives zero length at
    class n; connectedness forces a singleton
    image. The domain and actual derivative
    field remain explicit. *)
Theorem analytic_critical_connected_constancy (R:realType) n
    (A C:set (R_n R n)) (f:R_n R n->R^o) (D:R_n R n->Hom (R_n R n) R^o):
  (0<n)%N ->
  @norm_analytic R (R_n R n) R^o (inner_norm (@euclidean_inner_productP R n))
    (fun z:R^o=>`|z|) (inner_norm_real_norm (@euclidean_inner_productP R n))
    (@scalar_absolute_value_norm R) A f ->
  C `<=` A ->
  @connected (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) C ->
  (forall x,A x ->has_norm_differential (inner_norm (@euclidean_inner_productP R n))
    (fun z:R^o=>`|z|) A f x (D x)) ->
  (forall x,C x ->forall v,D x v = 0) ->
  forall x y,C x ->C y ->f x = f y.
Proof.
move=>hN hAnalytic hCA hConnected hD hZero.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNR:=@scalar_absolute_value_norm R.
have hSmooth:=norm_analytic_class_all_orders hAnalytic.
have hClassZero:=norm_class_continuous (hSmooth 0%N).
have hp:=@critical_rank_degree_nonnegative R n 0 n hN.
have hNull:=@federer_3_4_3 R n 0 n R^o (fun z:R^o=>`|z|) hNR A C f hp
  hN hN (fun x hx=>(hClassZero x hx).1) hCA (hSmooth n)
  (fun x hx=>ex_intro _ (D x) (conj (hD x (hCA x hx))
    (ex_intro _ 0%N (conj ((linear_rank_zeroP (D x)).2 (hZero x hx)) (leqnn 0))))).
have hNatNonzero:(n%:R:R)!=0 by rewrite pnatr_eq0 -lt0n.
have hDegree:(0%:R+(n-0)%:R/n%:R:R) = (1%N)%:R.
  by rewrite subn0 add0r (divff hNatNonzero).
have hNullNatural:@hausdorff_measure R (real_norm_metric_space hNR) 1 (f @` C) = 0%E.
  move:hNull;move:hp;rewrite hDegree=>hp.
  by rewrite real_hausdorff_measure_natural.
apply:(@connected_hausdorff_null_constancy R
  (Topological.clone (real_norm_metric_space hNX) _)
  (real_norm_metric_space hNR) C f hConnected _ hNullNatural).
apply:continuous_in_subspaceT=>x /asboolP hx.
exact:(@norm_class_zero_continuous_at R X R^o NX (fun z:R^o=>`|z|) hNX hNR A f x
  hClassZero (hCA x hx)).
Qed.
