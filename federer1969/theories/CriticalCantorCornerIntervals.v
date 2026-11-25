(** Federer (1969), 3.3.20, pp. 308–309:
    original endpoint intervals at every inward corner offset. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  CriticalCantorAddressUP CriticalCantorAddressLaws CriticalCantorOppositeAddress
  CriticalCantorIntervalGrid RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_cantor_original_corner_intervals]:
    every inward offset p in {0,3,12,15} gives
    ACTUAL original intervals at both endpoints of [0,1],
    at every level j>=2. Their exact positions supply
    all four corner-square pairings in 3.3.20,
    pp. 308–309. Every auxiliary interval remains local;
    symmetry is proved through original addresses. *)
Theorem critical_cantor_original_corner_intervals (R:realType) (c:R)
    (J:compact_real_intervals R) H j (p:nat):
  0<c ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c*real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  (2<=j)%N ->p \in [::0;3;12;15] ->
  exists L U:compact_real_intervals R,L \in H j /\U \in H j /\
    val L=(`[p%:R/(4:R)^+j,(p+1)%:R/(4:R)^+j]:set (real_line_metric R)) /\
    val U=(`[1-(p+1)%:R/(4:R)^+j,1-p%:R/(4:R)^+j]:set (real_line_metric R)).
Proof.
move=>hc hJ hTree hj hp.
have hAddress:=critical_cantor_two_digit_offsets hj hp.
have [b [hB hSum]]:=critical_cantor_opposite_address hAddress.
have [L [hL hLValue]]:=@critical_cantor_address_original_interval R c J H hc hJ hTree j p hAddress.
have [U [hU hUValue]]:=@critical_cantor_address_original_interval R c J H hc hJ hTree j b hB.
pose r:=(4:R)^+j.
have hr:0<r by rewrite /r exprn_gt0 // ltr0n.
have hRN:r!=0 by rewrite gt_eqF.
have hScalar:=congr1 (fun n:nat=>(n%:R:R)) hSum.
rewrite !natrD natrX -/r in hScalar.
have hBValue:(b%:R:R)=r-p%:R-1 by lra.
have hLower:(b%:R:R)/r= 1-(p+1)%:R/r.
  rewrite hBValue natrD;field;by rewrite hRN.
have hUpper:((b+1)%:R:R)/r= 1-p%:R/r.
  rewrite natrD hBValue;field;by rewrite hRN.
exists L,U;split=>//;split=>//;split=>//.
by rewrite -/r hUpper hLower in hUValue.
Qed.
