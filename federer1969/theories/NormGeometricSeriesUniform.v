(** Federer (1969), 3.1.24, pp. 238–239:
    geometric domination gives uniformly convergent Banach-space
    series and the quantitative tail bound used for all orders. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP NormGeometricIncrementLimit
  NormGeometricLimitError GeometricUniformTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_geometric_series_uniform_limit]: supporting
    the differentiated series in Federer 3.1.24, pp. 238–239.
    Uniform geometric bounds for consecutive partial sums in
    a Banach space prove existence of their limits and a
    uniform error estimate. Values outside the actual parameter
    domain are irrelevant, including when that domain is empty. *)
Theorem norm_geometric_series_uniform_limit (R:realType) (T:Type) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY)
    (hcomplete:is_complete_metric_space (real_norm_metric_space hNY))
    (A:T->Prop) (S:nat->T->Y) q M :
  0<q<1 -> 0<=M ->
  (forall N x,A x -> NY (S N.+1 x-S N x)<=q^+N*M) ->
  exists G:T->Y,
    (forall x,A x -> ((fun N=>(S N x:real_norm_metric_space hNY)) @ \oo -->
      (G x:real_norm_metric_space hNY))) /\
    (forall N x,A x -> NY (G x-S N x)<=q^+N*M/(1-q)) /\
    forall eps:R,0<eps -> exists n:nat,forall N,(n<=N)%N ->
      forall x,A x -> NY (S N x-G x)<eps.
Proof.
move=>hq hM hs.
have hex x:exists z:Y,A x ->
    ((fun N=>(S N x:real_norm_metric_space hNY)) @ \oo -->
      (z:real_norm_metric_space hNY)).
  case: (pselect (A x))=>[hx|hx].
  - have [z hz]:=@norm_geometric_increments_converge R Y NY hNY hcomplete
      (fun N=>S N x) q M hq hM (fun N=>hs N x hx).
    by exists z.
  - exists 0; by move=>ha; exfalso; exact (hx ha).
have [G hG]:=choice hex.
have hb N x (hx:A x):NY (G x-S N x)<=q^+N*M/(1-q).
  exact (@norm_geometric_increments_limit_error R Y NY hNY (fun N=>S N x)
    (G x) q M hq hM (fun n=>hs n x hx) (hG x hx) N).
exists G; split; first exact hG.
split; first exact hb.
move=>eps heps.
have hd:0<=1-q by apply: ltW; rewrite subr_gt0; exact (andP hq).2.
have ha:0<=M/(1-q) by exact: divr_ge0.
have [n hn]:=geometric_uniform_tail hq ha heps.
exists n=>N hN x hx.
rewrite (real_seminorm_subtract hNY.1).
have hh:=hb N x hx; rewrite -mulrA in hh.
exact (le_lt_trans hh (hn N hN)).
Qed.
