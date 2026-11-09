(** Federer (1969), 3.3.20, p. 306:
    the two exact original endpoint intervals in Phi(J,2). *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge CompactIntervalGaugeGeometry
  EqualCostIntervalFamilyUP CantorSplitRadiusUP CantorSplitRadius PowerCantorSplit RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_cantor_interval_children]: the
    two displayed original intervals after the definition
    of E in 3.3.20, p. 306. Their actual
    length is (b-a)2^(-1/m), with exact original
    endpoints a and b. Every original Phi family
    satisfying its public laws has exactly this membership. *)
Theorem binary_cantor_interval_children (R:realType) (c m a b:R)
    (J:compact_real_intervals R) (F:{fset compact_real_intervals R}):
  0<c ->0<m ->m<1 ->a<b ->val J=(`[a,b]:set (real_line_metric R)) ->
  is_equal_cost_interval_family (fun t=>c*real_power t m) J 2 F ->
  let s:=(b-a)*real_power 2 (-m^-1) in
  forall S:compact_real_intervals R,S \in F <->
    val S=(`[a,a+s]:set (real_line_metric R)) \/
    val S=(`[b-s,b]:set (real_line_metric R)).
Proof.
move=>hc hm hm1 hab hJ [_ [u [v [s [t [hUV [hWidth [hSplit [hSpace hChildren]]]]]]]]] s0 S.
have hAB:a<=b:=ltW hab.
have hUVOrder:u<=v by lra.
have hSubAB:(`[a,b]:set (real_line_metric R)) `<=` `[u,v] by rewrite -hJ -hUV.
have hSubUV:(`[u,v]:set (real_line_metric R)) `<=` `[a,b] by rewrite -hJ -hUV.
have [hAU hBV]:=(@compact_segment_subset_endpoints R a b u v hAB).1 hSubAB.
have [hUA hVB]:=(@compact_segment_subset_endpoints R u v a b hUVOrder).1 hSubUV.
have hU:u=a by lra.
have hV:v=b by lra.
subst u;subst v.
have hs:s=s0:=@power_cantor_split_length R c m (b-a) s 2 hc hm hWidth (leqnn 2) hSplit.
have hTwo:(2:R)-1= 1 by ring.
have ht:t=b-a-s by rewrite hSpace /cantor_split_spacing /= hTwo divr1.
have hFirst:a+0%:R*t=a by rewrite mul0r addr0.
have hSecond:a+1%:R*t=b-s by rewrite mul1r ht;ring.
have hSecondEnd:a+1%:R*t+s=b by rewrite hSecond;ring.
split.
- move=>/(hChildren S)[i [hi hValue]].
  case:i hi hValue=>[|[|i]] hi hValue.
  + left;by rewrite hFirst hs in hValue.
  + right;by rewrite hSecondEnd hSecond hs in hValue.
  + by [].
- move=>[hValue|hValue];apply/(hChildren S).
  + exists 0%N;split=>//;by rewrite hFirst hs.
  + exists 1%N;split=>//;by rewrite hSecondEnd hSecond hs.
Qed.
