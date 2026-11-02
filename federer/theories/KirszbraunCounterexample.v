(** Federer (1969), 2.10.44, printed p. 202: the printed counterexample to
    dropping the inner-product norm hypothesis of 2.10.43. The public opaque
    map has exactly the three prescribed values, optimal Lipschitz constant
    one, and no extension with bound one even to the origin. The
    accompanying public norm theorem proves that the source norm is not
    induced by any inner product. Source context and the diagonal
    qualification: KirszbraunCorners.v and KirszbraunCornerDistances.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import NormMetric EuclideanInnerProduct InnerMetric PlaneSupremumNorm
  PlaneSupremumNoninner KirszbraunCorners KirszbraunCornerMapUP KirszbraunCornerMap
  KirszbraunCornerIsometry KirszbraunCornerNonextension LipschitzUP LipschitzBasic LipschitzConstant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_2_10_44_counterexample]: direct
    three-point norm counterexample in 2.10.44,
    p. 202, with the same numerical coordinates
    and actual two prescribed norm metrics. The
    separately proved supremum-norm and non-inner
    theorems identify the source norm; the map's
    three values come from its opaque specification. *)
Theorem federer_2_10_44_counterexample (R : realType) :
  exists hLip : is_metric_lipschitz (@kirszbraun_corner_source R) (@kirszbraun_corner_map R),
    metric_lipschitz_constant hLip= 1 /\
    ~ exists g : plane_supremum_metric R -> inner_metric_space (@euclidean_inner_productP R 2),
      (forall x, kirszbraun_corner_source x -> g x=kirszbraun_corner_map x) /\
      is_metric_lipschitz_bound ((@kirszbraun_corner_source R) `|` [set 0]) g 1.
Proof.
have hf := kirszbraun_corner_map_specification R.
have hLip := metric_lipschitz_of_bound (kirszbraun_corner_map_bound_one hf).
exists hLip; split.
- exact (@kirszbraun_corner_map_optimal_one R (@kirszbraun_corner_map R) hf hLip).
- exact: kirszbraun_corner_map_no_extension hf.
Qed.
