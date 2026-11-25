(** Federer (1969), 3.3.20, p. 308: the unique hit parent retains every finer hit. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  EqualCostIntervalTreeSpecial SpecialIntervalFamilyUP SpecialIntervalFamilyBasic SpecialIntervalTreeLevels
  PowerConcaveIntervalGauge BinaryCantorSquareLevelsUP EuclideanInnerProduct InnerMetric
  EuclideanIntervalRectangles FiniteCellHitMeasureUP FiniteCellHitIndicesLaws RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_cantor_single_hit_original_descendants]: supporting
    first-split reduction in 3.3.20, p. 308. If the original test set
    hits only one original level square, every later hit belongs to
    that square's actual descendants. Point witnesses and original
    ancestor laws prove the exact hit-family identity for arbitrary sets. *)
Theorem binary_cantor_single_hit_original_descendants (R:realType) (c m:R)
    (J S T:compact_real_intervals R) H G j
    (V:set (inner_metric_space (@euclidean_inner_productP R 2))):
  0<c ->0<m ->m<1 ->
  is_equal_cost_interval_tree (fun t=>c  *  real_power t m) J (fun _:nat=>2%N) H ->
  is_binary_cantor_square_levels H G ->
  finite_cell_hit_indices (G j) (fun P=>euclidean_interval_rectangle P.1 P.2) V=[fset (S,T)] ->
  forall k,finite_cell_hit_indices (G (j+k)%N)
      (fun P=>euclidean_interval_rectangle P.1 P.2) V=
    finite_cell_hit_indices
      ((special_interval_restriction (H (j+k)%N) (val S)) `*`
       (special_interval_restriction (H (j+k)%N) (val T)))%fset
      (fun P=>euclidean_interval_rectangle P.1 P.2) V.
Proof.
move=>hc hm hm1 hTree hG hSingle k.
have hSpecial:=@equal_cost_interval_tree_special R _
  (power_concave_interval_gauge hc hm hm1) J (fun _:nat=>2%N) H hTree.
apply/fsetP=>z;case:z=>U W;apply/idP/idP.
- move=>/finite_cell_hit_indices_membership[hUW [x [[hxU hxW] hxV]]].
  move:hUW;rewrite hG in_fsetM=>/andP[hU hW].
  have [P [hP hUP]]:=@special_interval_tree_ancestor R _ H hSpecial j k U hU.
  have [Q [hQ hWQ]]:=@special_interval_tree_ancestor R _ H hSpecial j k W hW.
  have hParentHit:(P,Q) \in finite_cell_hit_indices (G j)
      (fun D=>euclidean_interval_rectangle D.1 D.2) V.
    apply/finite_cell_hit_indices_membership;split.
    + by rewrite hG in_fsetM hP hQ.
    + exists x;split=>//;split;[exact:hUP _ hxU|exact:hWQ _ hxW].
  move:hParentHit;rewrite hSingle in_fset1=>/eqP hEqual.
  have hPS:P=S:=congr1 fst hEqual.
  have hQT:Q=T:=congr1 snd hEqual.
  apply/finite_cell_hit_indices_membership;split.
  + rewrite in_fsetM;apply/andP;split;apply/special_interval_restriction_membership;
      split=>//;[by rewrite -hPS|by rewrite -hQT].
  + exists x;by split=>//;split.
- move=>/finite_cell_hit_indices_membership[hUW [x [hx hxV]]].
  move:hUW;rewrite in_fsetM=>/andP[/special_interval_restriction_membership[hU _]
    /special_interval_restriction_membership[hW _]].
  apply/finite_cell_hit_indices_membership;split.
  + by rewrite hG in_fsetM hU hW.
  + exists x;by split.
Qed.
