(** Federer (1969), 3.3.20, pp. 306–307: reflection of the original two children. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalFamilyUP
  BinaryCantorIntervalChildren RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_reflected_interval_children]: reflection
    interchanges the two actual endpoint children in Phi, as used in the
    square symmetries of 3.3.20, pp. 306–307. The original independent
    Phi laws determine membership; interval witnesses remain local. *)
Theorem binary_original_reflected_interval_children (R:realType) (c m a b:R)
    (P Q:compact_real_intervals R) F G (S:compact_real_intervals R):
  0<c ->0<m ->m<1 ->a<b ->val P=(`[a,b]:set (real_line_metric R)) ->
  val Q=(`[1-b,1-a]:set (real_line_metric R)) ->
  is_equal_cost_interval_family (fun t=>c * real_power t m) P 2 F ->
  is_equal_cost_interval_family (fun t=>c * real_power t m) Q 2 G ->S \in F ->
  exists T,T \in G /\forall x,val S x <->val T (1-x).
Proof.
move=>hc hm hm1 hab hP hQ hF hG hS.
pose s:=(b-a)*real_power 2 (-m^-1).
have hs:0<s by apply:mulr_gt0;[lra|exact:real_power_strictly_positive].
have hQOrder:1-b<1-a by lra.
have hWidth:(1-a)-(1-b)=b-a by ring.
have hCharP:=@binary_cantor_interval_children R c m a b P F hc hm hm1 hab hP hF S.
have hCharQ:=@binary_cantor_interval_children R c m (1-b) (1-a) Q G hc hm hm1 hQOrder hQ hG.
rewrite hWidth in hCharQ.
have hSelect d e: d<=e ->
    ((`[d,e]:set (real_line_metric R))=`[1-b,1-b+s] \/
     (`[d,e]:set (real_line_metric R))=`[1-a-s,1-a]) ->
    exists T:compact_real_intervals R,T \in G /\val T=(`[d,e]:set (real_line_metric R)).
  move=>hde hValue.
  have hInterval:is_compact_real_interval (`[d,e]:set (real_line_metric R))
    by exists d,e;split.
  pose T:compact_real_intervals R:=Sub (`[d,e]:set (real_line_metric R)) (mem_set hInterval).
  exists T;split=>//;apply/(hCharQ T);exact:hValue.
case:(hCharP.1 hS)=>hValue.
- change (val S=(`[a,a+s]:set (real_line_metric R))) in hValue.
  have [T [hT hValueT]]:=hSelect (1-a-s) (1-a) (ltac:(lra)) (or_intror erefl).
  exists T;split=>//;move=>x;rewrite hValue hValueT /= !in_itv /=.
  split=>/andP[h0 h1];apply/andP;split;lra.
- change (val S=(`[b-s,b]:set (real_line_metric R))) in hValue.
  have [T [hT hValueT]]:=hSelect (1-b) (1-b+s) (ltac:(lra)) (or_introl erefl).
  exists T;split=>//;move=>x;rewrite hValue hValueT /= !in_itv /=.
  split=>/andP[h0 h1];apply/andP;split;lra.
Qed.
