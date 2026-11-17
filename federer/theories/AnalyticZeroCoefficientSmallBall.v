(** Federer (1969), 3.4.8(11), p. 334:
    the original lower Weierstrass coefficients vanish
    at zero. On a sufficiently small closed
    prefix ball their absolute sum is below
    the prescribed positive bound. Reuse class-zero
    local control and finite neighbourhood intersections. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormClassZeroTopology NormRegularity NormAnalyticUP NormAnalyticLocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_zero_coefficient_small_ball]:
    the strict coefficient bound used when
    choosing epsilon_(j-1) in 3.4.8(11),
    p. 334. The closed-ball conclusion
    retains the boundary radii needed on p. 335. *)
Theorem analytic_zero_coefficient_small_ball (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) k (U:set X) (f:'I_k->X->R^o) (c:R):
  (0<k)%N ->U 0 ->0<c ->
  (forall i,@norm_analytic R X R^o NX (fun z:R^o=>`|z|) hNX
    (@scalar_absolute_value_norm R) U (f i)) ->
  (forall i,f i 0 = 0) ->
  exists d:R,0<d /\ forall x,NX x<=d ->U x /\ (\sum_(i<k) `|f i x|)<c.
Proof.
move=>hK hU0 hC hAnalytic hZero.
pose T:=real_norm_metric_space hNX.
pose a:R:=c/k%:R.
have hKN:0<(k%:R:R) by rewrite ltr0n.
have hA:0<a by rewrite /a divr_gt0.
pose P:=fun i:'I_k=>[set x:T|U x /\ `|f i x|<a].
have hEach i:nbhs (0:T) (P i).
  have hClass:=norm_class_continuous (norm_analytic_class_all_orders (hAnalytic i) 0%N).
  have [d [hd hSmall]]:=@norm_class_zero_local_control R X R^o NX (fun z:R^o=>`|z|)
    hNX U (f i) 0 a hClass hU0 hA.
  apply:(proj2 (metricType_numDomainType.nbhs_mdistP (0:T) _)).
  exists d;first exact:hd.
  move=>x hx.
  change (is_true (NX (0-x)<d)) in hx.
  rewrite sub0r (real_seminorm_negate hNX.1) in hx.
  have hX:NX (x-0)<d by rewrite subr0.
  have [hUx hValue]:=hSmall x hX.
  split;first exact:hUx.
  by rewrite hZero subr0 in hValue.
have hAll:=@filter_forall T 'I_k P (nbhs (0:T)) (nbhs_filter (0:T)) hEach.
have hNear:nbhs (0:T) [set x|forall i,U x /\ `|f i x|<a].
  apply:(filterS _ hAll)=>x hx;exact:hx.
have [d [hd hBall]]:=(@norm_domain_interior_neighbourhood R X NX hNX
  [set x|forall i,U x /\ `|f i x|<a] 0).2 hNear.
exists (d/2);split;first by rewrite divr_gt0 // ltr0n.
move=>x hx.
have hHalf:d/2<d by lra.
have hX:NX x<d:=le_lt_trans hx hHalf.
have hAllX:=hBall x hX.
rewrite add0r in hAllX.
split;first exact:(hAllX (Ordinal hK)).1.
have hHas:has predT (enum 'I_k).
  apply/hasP;exists (@Ordinal k 0 hK);by rewrite ?mem_enum.
have hSum:(\sum_(i<k) `|f i x|)<\sum_(i:'I_k) a.
  rewrite -!big_enum;exact:ltr_sum hHas (fun i _=>(hAllX i).2).
have hKNonzero:(k%:R:R)!=0 by rewrite pnatr_eq0 -lt0n.
by rewrite sumr_const card_ord -[a *+ k]mulr_natr /a divfK // in hSum.
Qed.
