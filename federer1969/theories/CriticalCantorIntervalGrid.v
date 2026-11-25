(** Federer (1969), 3.3.20, pp. 306–309:
    every critical address is an actual original interval. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge
  EqualCostIntervalTreeUP SpecialIntervalRefinement BinaryCantorIntervalChildren
  CriticalCantorRatio CriticalCantorAddressUP FourAdicIntervalScalar RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_cantor_address_original_interval]:
    each base-four zero/three address is a member
    of the ACTUAL original interval level, with exact
    endpoints a/4^j and (a+1)/4^j. This identifies
    the finite corner offsets of 3.3.20, pp. 308–309
    with the original construction; no replacement square
    family or supplied membership certificate is assumed. *)
Theorem critical_cantor_address_original_interval (R:realType) (c:R)
    (J:compact_real_intervals R) H:
  0<c ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c*real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  forall j a,critical_cantor_address j a ->exists S:compact_real_intervals R,
    S \in H j /\val S=(`[a%:R/(4:R)^+j,(a+1)%:R/(4:R)^+j]:set (real_line_metric R)).
Proof.
move=>hc hJ hTree j a hAddress.
have hm:0<(1/2:R) by lra.
have hm1:(1/2:R)<1 by lra.
elim:hAddress=>[|k n d hN [P [hP hValue]] /orP[/eqP->|/eqP->]].
- exists J;split;first by rewrite (equal_cost_tree_root hTree) in_fset1 eqxx.
  by rewrite expr0 !divr1.
- pose r:=(4:R)^+k.
  have hr:0<r by rewrite /r exprn_gt0 // ltr0n.
  have hRN:r!= 0 by rewrite gt_eqF.
  pose lo:=(n%:R:R)/r.
  pose hi:=((n+1)%:R:R)/r.
  have hDifference:hi-lo= 1/r by rewrite /hi /lo natrD;field;by rewrite hRN.
  have hPositive:0<1/r by rewrite divr_gt0.
  have hOrder:lo<hi by rewrite -subr_gt0 hDifference.
  have [K [hK hStep]]:=equal_cost_tree_step hTree k.
  have hChildren:=@binary_cantor_interval_children R c (1/2:R) lo hi P (K P)
    hc hm hm1 hOrder hValue (hK P hP).
  rewrite critical_cantor_binary_ratio in hChildren.
  have hChildOrder:lo<=lo+(hi-lo)/4 by lra.
  have hInterval:is_compact_real_interval (`[lo,lo+(hi-lo)/4]:set (real_line_metric R)).
    by exists lo,(lo+(hi-lo)/4);split.
  pose T:compact_real_intervals R:=Sub (`[lo,lo+(hi-lo)/4]:set (real_line_metric R)) (mem_set hInterval).
  have hT:T \in K P by apply/(hChildren T);left.
  exists T;split.
  + rewrite hStep;apply/special_interval_refinement_membership;by exists P.
  + have [hLow [hHigh _]]:=@four_adic_interval_scalar_endpoints R n%:R r hr.
    change ((`[lo,lo+(hi-lo)/4]:set (real_line_metric R))=
      (`[((4 * n+0)%N)%:R/(4:R)^+k.+1,((4 * n+0+1)%N)%:R/(4:R)^+k.+1]:set (real_line_metric R))).
    have hLowWanted:((4 * n)%N)%:R/(4*r)=lo by rewrite natrM hLow.
    have hHighWanted:((4 * n+1)%N)%:R/(4*r)=lo+(hi-lo)/4.
      by rewrite natrD natrM hHigh /lo /hi natrD.
    by rewrite addn0 exprS -/r hLowWanted hHighWanted.
- pose r:=(4:R)^+k.
  have hr:0<r by rewrite /r exprn_gt0 // ltr0n.
  have hRN:r!= 0 by rewrite gt_eqF.
  pose lo:=(n%:R:R)/r.
  pose hi:=((n+1)%:R:R)/r.
  have hDifference:hi-lo= 1/r by rewrite /hi /lo natrD;field;by rewrite hRN.
  have hPositive:0<1/r by rewrite divr_gt0.
  have hOrder:lo<hi by rewrite -subr_gt0 hDifference.
  have [K [hK hStep]]:=equal_cost_tree_step hTree k.
  have hChildren:=@binary_cantor_interval_children R c (1/2:R) lo hi P (K P)
    hc hm hm1 hOrder hValue (hK P hP).
  rewrite critical_cantor_binary_ratio in hChildren.
  have hChildOrder:hi-(hi-lo)/4<=hi by lra.
  have hInterval:is_compact_real_interval (`[hi-(hi-lo)/4,hi]:set (real_line_metric R)).
    by exists (hi-(hi-lo)/4),hi;split.
  pose T:compact_real_intervals R:=Sub (`[hi-(hi-lo)/4,hi]:set (real_line_metric R)) (mem_set hInterval).
  have hT:T \in K P by apply/(hChildren T);right.
  exists T;split.
  + rewrite hStep;apply/special_interval_refinement_membership;by exists P.
  + have [_ [_ [hLow hHigh]]]:=@four_adic_interval_scalar_endpoints R n%:R r hr.
    have hNat:(4 * n+3+1= 4 * n+4)%N by rewrite -addnA.
    change ((`[hi-(hi-lo)/4,hi]:set (real_line_metric R))=
      (`[((4 * n+3)%N)%:R/(4:R)^+k.+1,((4 * n+3+1)%N)%:R/(4:R)^+k.+1]:set (real_line_metric R))).
    have hLowWanted:((4 * n+3)%N)%:R/(4*r)=hi-(hi-lo)/4.
      by rewrite natrD natrM hLow /lo /hi natrD.
    have hHighWanted:((4 * n+4)%N)%:R/(4*r)=hi.
      by rewrite natrD natrM hHigh /hi natrD.
    by rewrite hNat exprS -/r hLowWanted hHighWanted.
Qed.
