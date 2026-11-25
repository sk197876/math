(** Federer (1969), 3.2.36, p. 273:
    exact fibres of a product tube under
    the actual first-factor distance. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  EuclideanSquaredProduct EuclideanCartesianMap CompactSetDistanceProfile CompactHausdorffMetric
  CompactSquaredProductDistance PythagoreanRadiusCutoff MetricSetDistanceUP MetricSetDistanceBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_product_tube_first_distance_fibre]:
    direct set identity underlying the second
    displayed equality of Federer 3.2.36,
    p. 273. At first-factor distance s,
    the whole radius-r product tube is
    the Cartesian product of that original
    first level and the second tube of
    radius sqrt(r^2-s^2). Actual squared
    product distance and the nonnegative root
    prove both directions, including s=0
    and either zero-dimensional coordinate block. *)
Theorem euclidean_product_tube_first_distance_fibre (R:realType) m n
    (A:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R m)))
    (B:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)))
    (d:inner_metric_space (@euclidean_inner_productP R (m+n))->R) (s r:R):
  @is_metric_set_distance R (inner_metric_space (@euclidean_inner_productP R (m+n))) (euclidean_cartesian_set (val A) (val B)) d ->0<=s ->s<r ->
  [set z:inner_metric_space (@euclidean_inner_productP R (m+n))|
    compact_set_distance_profile A (euclidean_block_split z).1=s /\d z<r]=
    euclidean_cartesian_set [set x|compact_set_distance_profile A x=s]
      [set y|compact_set_distance_profile B y<Num.sqrt (r^+2-s^+2)].
Proof.
move=>hD hs hsr.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose Z:=inner_metric_space (@euclidean_inner_productP R (m+n)).
have hSquared:=@compact_squared_product_set_distance R Z X Y
  (fun x y=>@euclidean_block_join R m n (x,y))
  (fun z=>(@euclidean_block_split R m n z).1)
  (fun z=>(@euclidean_block_split R m n z).2)
  (@euclidean_blocks_are_squared_metric_product R m n) A B d hD.
have hCutoff (z:Z):compact_set_distance_profile A (euclidean_block_split z).1=s ->
    (d z<r)=(compact_set_distance_profile B (euclidean_block_split z).2<Num.sqrt (r^+2-s^+2)).
  move=>hLevel.
  have hIdentity:=hSquared z; rewrite hLevel in hIdentity.
  exact:(@pythagorean_radius_cutoff R (d z)
    (compact_set_distance_profile B (euclidean_block_split z).2) s r
    (metric_set_distance_nonnegative hD z)
    (metric_set_distance_nonnegative (compact_set_distance_profile_specification B) _)
    hs hsr hIdentity).
apply/seteqP; split=>z [hLevel hTube]; split=>//.
- change (is_true (compact_set_distance_profile B (euclidean_block_split z).2<Num.sqrt (r^+2-s^+2))).
  by rewrite -(hCutoff z hLevel).
- change (is_true (d z<r)).
  by rewrite (hCutoff z hLevel).
Qed.
