(** Federer (1969), 3.2.36, pp. 272--273:
    the printed first-factor distance is actual
    distance to a nonempty closed cylinder. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanSquaredProduct CompactSetDistanceProfile CompactHausdorffMetric
  SquaredProductCylinderDistance MetricSetDistanceUP TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_first_cylinder_distance]:
    the actual function f(y,z)=dist(y,P)
    used for coarea in Federer 3.2.36,
    pp. 272--273. For compact P, its
    cylinder with the entire second space
    is nonempty closed, and the printed
    function satisfies the independent distance
    laws for that cylinder. Every needed
    closed-source hypothesis of 3.2.34 is
    discharged, including unbounded cylinders;
    either coordinate block may be zero. *)
Theorem euclidean_first_cylinder_distance (R:realType) m n
    (A:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R m))):
  let C:set (inner_metric_space (@euclidean_inner_productP R (m+n))):=
    [set z|val A (euclidean_block_split z).1] in
  let f:=fun z:inner_metric_space (@euclidean_inner_productP R (m+n))=>
    compact_set_distance_profile A (euclidean_block_split z).1 in
  closed C /\C!=set0 /\is_metric_set_distance C f.
Proof.
move=>C f.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose Z:=inner_metric_space (@euclidean_inner_productP R (m+n)).
have hFirst:continuous (fun z:Z=>((@euclidean_block_split R m n z).1:X)).
  move=>z; exact:continuous_comp (@euclidean_block_split_continuous R m n z)
    (@first_projection_continuous X Y (euclidean_block_split z)).
have hClosed:closed C.
  change (closed ((fun z:Z=>((@euclidean_block_split R m n z).1:X)) @^-1` val A)).
  apply:preimage_closed; first by move=>z _; exact:hFirst.
  exact:compact_closed (@metric_hausdorff R X) (set_valP A).1.
split; first exact:hClosed.
split.
- have [a ha]:=(set_valP A).2; exists (euclidean_block_join (a,0%R:Y)).
  change (val A (euclidean_block_split (euclidean_block_join (a,0%R:Y))).1).
  by rewrite euclidean_block_joinK.
- exact:(@squared_product_cylinder_distance R Z X Y
    (fun x y=>@euclidean_block_join R m n (x,y))
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2)
    (@euclidean_blocks_are_squared_metric_product R m n)
    (val A) (compact_set_distance_profile A) (compact_set_distance_profile_specification A)).
Qed.
