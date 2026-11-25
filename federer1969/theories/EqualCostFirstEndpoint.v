(** Federer (1969), 3.3.20, pp. 306 and 308:
    the actual first endpoint persists in every interval level. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge CompactIntervalGaugeGeometry
  EqualCostIntervalFamilyUP EqualCostIntervalTreeUP SpecialIntervalRefinement
  SpecialIntervalFamilyUP CantorSplitRadiusUP PowerCantorPairUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equal_cost_family_first_endpoint]: the
    leftmost original child has the same first endpoint
    as its parent, from the actual Phi formula
    recalled in 3.3.20, p. 306. The local
    child is an actual member of the original family. *)
Lemma equal_cost_family_first_endpoint (R:realType) (h:R->R)
    (J:compact_real_intervals R) n (F:{fset compact_real_intervals R}) (a b:R):
  val J=(`[a,b]:set (real_line_metric R)) ->a<b ->
  is_equal_cost_interval_family h J n F ->
  exists S:compact_real_intervals R,S \in F /\exists c:R,a<c /\
    val S=(`[a,c]:set (real_line_metric R)).
Proof.
move=>hJ hab [hn [u [v [s [t [hUV [hWidth [hSplit [hSpace hChildren]]]]]]]]].
have hUVOrder:u<=v by lra.
have hAB:a<=b:=ltW hab.
have hSubset:(`[a,b]:set (real_line_metric R)) `<=` `[u,v] by rewrite -hJ -hUV.
have hSubsetBack:(`[u,v]:set (real_line_metric R)) `<=` `[a,b] by rewrite -hJ -hUV.
have [hAU hBV]:=(@compact_segment_subset_endpoints R a b u v hAB).1 hSubset.
have [hUA hVB]:=(@compact_segment_subset_endpoints R u v a b hUVOrder).1 hSubsetBack.
have hU:u=a by lra.
subst u.
have hs:0<s:=(cantor_split_radius_bounds hSplit).1.
have hI:is_compact_real_interval (`[a,a+s]:set (real_line_metric R)).
  exists a,(a+s);split=>//;lra.
pose S:compact_real_intervals R:=Sub (`[a,a+s]:set (real_line_metric R)) (mem_set hI).
exists S;split.
- apply/(hChildren S);exists 0%N;split;first exact:leq_trans (leqnSn 1) hn.
  by rewrite !mul0r !addr0.
- exists (a+s);split=>//;lra.
Qed.

(** Source for [equal_cost_tree_first_endpoint]: the
    actual first root endpoint is in every original
    level, supporting the original-corner endpoint of
    the fixed Cantor example, 3.3.20, pp. 306–308. *)
Lemma equal_cost_tree_first_endpoint (R:realType) (h:R->R)
    (J:compact_real_intervals R) n H (a b:R):
  val J=(`[a,b]:set (real_line_metric R)) ->a<b ->
  is_equal_cost_interval_tree h J n H ->forall j,
  exists S:compact_real_intervals R,S \in H j /\exists c:R,a<c /\
    val S=(`[a,c]:set (real_line_metric R)).
Proof.
move=>hJ hab hTree;elim=>[|j [S [hS [c [hac hSValue]]]]].
- exists J;split;first by rewrite (equal_cost_tree_root hTree) in_fset1 eqxx.
  exists b;by split.
- have [K [hK hStep]]:=equal_cost_tree_step hTree j.
  have [T [hT [d [had hTValue]]]]:=equal_cost_family_first_endpoint hSValue hac (hK S hS).
  exists T;split.
  + rewrite hStep;apply/special_interval_refinement_membership;by exists S.
  + exists d;by split.
Qed.

(** Source for [power_cantor_original_zero_endpoint]: the
    point zero belongs to the actual original A(m,n),
    from the original interval recursion used in
    3.3.20, p. 306. It supplies an actual
    corner, including all closed boundary endpoints. *)
Theorem power_cantor_original_zero_endpoint (R:realType) (c m:R) n
    (A:set (real_line_metric R)) (f:R->R):
  is_power_cantor_pair c m n A f ->A 0.
Proof.
move=>[J [H [hJ [hTree [hA _]]]]].
apply:(hA 0).2=>j.
have [S [hS [d [hd hValue]]]]:=@equal_cost_tree_first_endpoint R _ J n H 0 1 hJ ltr01 hTree j.
exists S;split=>//;rewrite hValue /=;apply/andP;split;first exact:lexx.
exact:ltW hd.
Qed.
