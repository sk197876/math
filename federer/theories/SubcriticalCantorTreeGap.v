(** Federer (1969), 3.2.40, p. 276: the actual
    interval levels have a uniform positive point separation.
    Earlier parent gaps dominate every later child gap. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge MetricDiameter
  RealPower PowerConcaveIntervalGauge RapidPowerCantorScalesUP
  RapidPowerCantorTreeScales EqualCostIntervalTreeUP EqualCostIntervalFamilyUP
  EqualCostIntervalFamilyGap EqualCostIntervalSpecial SpecialIntervalFamilyUP
  SpecialIntervalRefinement CantorSplitRadius.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [subcritical_power_cantor_tree_point_gap]: supporting
    separated packing points for the Cantor square in Federer
    3.2.40, p. 276. Distinct intervals of level j+1 have
    all their points separated by at least the actual gap
    at step j. Same-parent children use their Phi laws;
    different parents use the previous level and the proved
    decrease of gaps. No point configuration is assumed. *)
Theorem subcritical_power_cantor_tree_point_gap (R:realType) (c m:R)
    (n:nat->nat) (s:nat->R) (J:compact_real_intervals R) H:
  0<c ->0<m ->m<=1/2 ->is_rapid_power_cantor_scales c m n s ->
  val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c*real_power t m) J n H ->
  forall j S T,S \in H j.+1 ->T \in H j.+1 ->S!=T ->
    forall x y:real_line_metric R,val S x ->val T y ->
    cantor_split_spacing (s j) (n j) (s j.+1)-s j.+1<=mdist x y.
Proof.
move=>hc hm hmHalf hScales hJ hTree.
have hm1:m<1 by lra.
have hg:=power_concave_interval_gauge hc hm hm1.
have hWidth:=@rapid_power_cantor_tree_common_width R c m n s J H hc hm hm1 hScales hJ hTree.
pose g k:=cantor_split_spacing (s k) (n k) (s k.+1)-s k.+1.
have hSibling k P F S T:
    P \in H k ->S \in H k.+1 ->
    is_equal_cost_interval_family (fun t=>c*real_power t m) P (n k) F ->
    S \in F ->T \in F ->S!=T ->forall x y:real_line_metric R,
    val S x ->val T y ->g k<=mdist x y.
  move=>hP hSGlobal hPhi hS hT hDifferent x y hx hy.
  have h:=@equal_cost_interval_family_point_gap R (fun t=>c*real_power t m)
    P (n k) F S T x y hPhi hS hT hDifferent hx hy.
  change (is_true (cantor_split_spacing
    (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val P)))
    (n k) (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S)))-
    fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S))<=mdist x y)) in h.
  by rewrite (hWidth k P hP) (hWidth k.+1 S hSGlobal) in h.
have hParent k K S:
    H k.+1=special_interval_refinement (H k) K ->S \in H k.+1 ->
    exists P,P \in H k /\S \in K P.
  move=>hNext hS; apply:(@special_interval_refinement_membership R (H k) K S).1.
  by rewrite -hNext.
elim=>[S T hS hT hDifferent x y hx hy|j ih S T hS hT hDifferent x y hx hy].
- have [K [hK hNext]]:=equal_cost_tree_step hTree 0%N.
  have [P [hP hSP]]:=hParent 0%N K S hNext hS.
  have [Q [hQ hTQ]]:=hParent 0%N K T hNext hT.
  have hPJ:P=J by move:hP; rewrite (equal_cost_tree_root hTree) in_fset1=>/eqP.
  have hQJ:Q=J by move:hQ; rewrite (equal_cost_tree_root hTree) in_fset1=>/eqP.
  rewrite hPJ in hP hSP; rewrite hQJ in hTQ.
  exact:(hSibling 0%N J (K J) S T hP hS (hK J hP) hSP hTQ hDifferent x y hx hy).
- have [K [hK hNext]]:=equal_cost_tree_step hTree j.+1.
  have [P [hP hSP]]:=hParent j.+1 K S hNext hS.
  have [Q [hQ hTQ]]:=hParent j.+1 K T hNext hT.
  case:(eqVneq P Q)=>[hEqual|hParentsDifferent].
  + rewrite -hEqual in hTQ.
    exact:(hSibling j.+1 P (K P) S T hP hS (hK P hP) hSP hTQ hDifferent x y hx hy).
  + have hPhiP:=@federer_2_10_28_4_special R _ hg P (n j.+1) (K P) (hK P hP).
    have hPhiQ:=@federer_2_10_28_4_special R _ hg Q (n j.+1) (K Q) (hK Q hQ).
    have hxP:val P x:=@special_interval_subsets R _ P (K P) hPhiP S hSP x hx.
    have hyQ:val Q y:=@special_interval_subsets R _ Q (K Q) hPhiQ T hTQ y hy.
    have hOld:=ih P Q hP hQ hParentsDifferent x y hxP hyQ.
    exact:le_trans (@rapid_power_cantor_gaps_decrease R c m n s hc hm hmHalf hScales j) hOld.
Qed.
