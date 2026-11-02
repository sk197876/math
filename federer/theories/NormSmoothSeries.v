(** Federer (1969), 3.1.24, pp. 238–239:
    the normal convergence argument for a smooth series
    whose actual differential terms have uniform geometric bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP InnerConvex
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearZero ContinuousMultilinearBanach
  NormDifferentialUP NormClassOneUP NormClassHigherUP NormClassHigherRestriction
  NormHigherDifferentialUP NormHigherDifferentialLocal NormHigherDifferentialFiniteSums
  NormClassZeroPrefixSum NormUniformLimitClassZero NormGeometricSeriesUniform
  NormSequenceLimitUnique NormSmoothUniformLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_geometrically_dominated_smooth_series]: the
    induction establishing smoothness and termwise differentiation
    in Federer 3.1.24, pp. 238–239. Each higher
    differential series has an actual norm limit by Banach
    completeness, uniform tails, and continuity. The recursive
    differential limit theorem proves that these are precisely
    the higher differentials of the given function. Degree zero
    is identified by uniqueness of norm limits, not assumed. *)
Theorem norm_geometrically_dominated_smooth_series (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (hcomplete:is_complete_metric_space (real_norm_metric_space hNY))
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->X}->Hom (Z i) Y)
    (ZN:forall i,Z i->R)
    (hZ:forall i,is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A:X->Prop) (Q:nat->X->Y) (E:forall m:nat,forall i,X->Z i)
    (f:X->Y) q (M:nat->R) :
  is_inner_convex A -> (forall x,A x -> norm_domain_interior NX A x) ->
  0<q<1 -> (forall i,0<=M i) ->
  (forall m,norm_class_zero NX NY (fun _=>True) (Q m)) ->
  (forall m i x,has_norm_higher_differential NX ev ZN (fun _=>True) (Q m) i x (E m i x)) ->
  (forall m i,norm_class_zero NX (@ZN i) (fun _=>True) (E m i)) ->
  (forall i m x,A x -> @ZN i (E m i x)<=q^+m*M i) ->
  (forall eps:R,0<eps -> exists n:nat,forall N,(n<=N)%N ->
    forall x,A x -> NY ((\sum_(m<N) Q m x)-f x)<eps) ->
  exists G:forall i,X->Z i,
    norm_class_infinity NX NY ev ZN A f /\
    (forall i x,A x -> has_norm_higher_differential NX ev ZN A f i x (G i x)) /\
    forall i x,A x -> @ZN i (G i x)<=M i/(1-q).
Proof.
move=>hA hopen hq hM hQ hE hcE hb hf.
pose F N x:=\sum_(m<N) Q m x.
pose D N i x:=\sum_(m<N) E m i x.
have hsub x (_:A x):True:=Logic.I.
have hQlocal m:norm_class_zero NX NY A (Q m).
  exact (norm_class_zero_open_restriction hsub hopen (hQ m)).
have hClocal m i:norm_class_zero NX (@ZN i) A (E m i).
  exact (norm_class_zero_open_restriction hsub hopen (hcE m i)).
have hD N i x (hx:A x):has_norm_higher_differential NX ev ZN A (F N) i x (D N i x).
  apply: (@norm_higher_differential_finite_sum R X Y NX NY hNX hNY Z ev ZN hZ A hopen
    (Finite.clone 'I_N _) (fun m=>Q m) i (fun m=>E m i) _ x hx).
  move=>m y hy.
  exact ((@norm_higher_differential_open_restriction R X Y NX NY hNX hNY Z ev ZN hZ
    i (fun _=>True) A (Q m) hsub hopen y hy (E m i y)).1 (hE m i y)).
have hCD N i:norm_class_zero NX (@ZN i) A (D N i).
  exact (@norm_class_zero_prefix_sum R X (Z i) NX (@ZN i)
    (continuous_multilinear_norm_is_norm hNY (hZ i)) A (fun m=>E m i) N hopen
    (fun m _=>hClocal m i)).
have hCF N:norm_class_zero NX NY A (F N).
  exact (@norm_class_zero_prefix_sum R X Y NX NY hNY A Q N hopen (fun m _=>hQlocal m)).
have hcf:norm_class_zero NX NY A f.
  exact (@norm_uniform_limit_class_zero R X Y NX NY hNY A F f hCF hf).
have hinc i N x (hx:A x):@ZN i (D N.+1 i x-D N i x)<=q^+N*M i.
  rewrite /D big_ord_recr /= addrAC subrr add0r.
  exact (hb i N x hx).
have hex i:exists G:X->Z i,
    (forall x,A x -> ((fun N=>(D N i x:real_norm_metric_space
      (continuous_multilinear_norm_is_norm hNY (hZ i)))) @ \oo -->
      (G x:real_norm_metric_space (continuous_multilinear_norm_is_norm hNY (hZ i))))) /\
    (forall N x,A x -> @ZN i (G x-D N i x)<=q^+N*M i/(1-q)) /\
    forall eps:R,0<eps -> exists n:nat,forall N,(n<=N)%N ->
      forall x,A x -> @ZN i (D N i x-G x)<eps.
  have hZi:=@continuous_multilinear_complete_general R i X Y (Z i) NX NY hNX hNY
    (@ev i) (@ZN i) (hZ i) hcomplete.
  exact (@norm_geometric_series_uniform_limit R X (Z i) (@ZN i)
    (continuous_multilinear_norm_is_norm hNY (hZ i)) hZi A (fun N=>D N i) q (M i)
    hq (hM i) (hinc i)).
pose G i:=projT1 (cid (hex i)).
have hG i:=projT2 (cid (hex i)).
have hunif i:forall eps:R,0<eps -> exists n:nat,forall N,(n<=N)%N ->
    forall x,A x -> @ZN i (D N i x-G i x)<eps.
  exact (hG i).2.2.
have hev N x:@ev 0%N [ffun j:'I_0=>(0:X)] (D N 0%N x)= F N x.
  rewrite /D /F linear_sum; apply: eq_bigr=>m _; exact (hE m 0%N x).2.
have hbase x (hx:A x):has_norm_higher_differential NX ev ZN A f 0%N x (G 0%N x).
  split; first exact hx.
  apply: (@norm_sequence_limit_unique R Y NY hNY (fun N=>F N x)).
  - move=>eps he; have [n hn]:=hunif 0%N eps he.
    exists n=>N hN.
    have hh:=hn N hN x hx.
    rewrite (continuous_multilinear_zero_norm hNY (hZ 0%N)) linearB /= hev in hh.
    exact hh.
  - move=>eps he; have [n hn]:=hf eps he.
    exists n=>N hN; exact (hn N hN x hx).
have hlimit:=@norm_smooth_uniform_limit R X Y NX NY hNX hNY Z ev ZN hZ A F D G f
  hA hcf hD hCD hunif hbase.
exists G; split; first exact hlimit.1.
split; first exact hlimit.2.
move=>i x hx; have hh:=(hG i).2.1 0%N x hx.
by rewrite /D big_ord0 subr0 expr0 mul1r in hh.
Qed.
