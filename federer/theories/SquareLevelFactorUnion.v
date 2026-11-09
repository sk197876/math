(** Federer (1969), 3.3.20, pp. 306–307: actual square-level unions are products of original factor unions. *)
From mathcomp Require Import all_boot finmap boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge BinaryCantorSquareLevelsUP
  EuclideanInnerProduct InnerMetric EuclideanRealPlane EuclideanCantorProduct EuclideanIntervalRectangles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_square_level_factor_union]: the actual
    G_j union is the square of the original H_j union, supporting
    the original square symmetries in 3.3.20, pp. 306–307. *)
Lemma binary_original_square_level_factor_union (R:realType) H G:
  @is_binary_cantor_square_levels R H G ->forall j,
  (\bigcup_(P in [set` G j]) euclidean_interval_rectangle P.1 P.2)=
    euclidean_cantor_product (\bigcup_(S in [set` H j]) val S)
      (\bigcup_(T in [set` H j]) val T).
Proof.
move=>hG j;apply/seteqP;split=>x.
- move=>[P hP [hx0 hx1]];change (is_true (P \in G j)) in hP.
  move:hP;rewrite hG in_fsetM=>/andP[hS hT].
  split;[by exists P.1|by exists P.2].
- move=>[[S hS hxS] [T hT hxT]].
  exists (S,T);first by change (is_true ((S,T) \in G j));rewrite hG in_fsetM hS hT.
  by split.
Qed.
