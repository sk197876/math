(** Federer (1969), 4.1.14, pp. 371–372: the
    compact support of the interval-current product is the
    exact closed time band times K. This current-independent
    compact index reuses the segment and Cartesian compactness
    laws of 4.1.8, pp. 360–362. An empty K gives
    the empty cylinder, including ambient dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanCartesianMap CurrentCartesianCompact ScalarCurrentIntervalCompact
  CurrentHomotopyUP CurrentHomotopyGeometry SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_compact_time_cylinder_carrier]:
    exactly [0,1] times the original K in the
    block coordinates of 4.1.8, p. 360, supporting
    Federer 4.1.14, pp. 371–372. *)
Definition current_compact_time_cylinder_carrier (R:realType) n
    (K:set (R_n R n)):set (R_n R (1+n)%N):=
  [set z|0<=@euclidean_one_project R (@euclidean_first_block_map R 1%N n z)<=1 /\
    K (@euclidean_last_block_map R 1%N n z)].

(** Source for [current_compact_time_cylinder_is_compact]:
    the exact original closed time band times K is
    compact by the preceding segment and Cartesian laws,
    supporting Federer 4.1.14, pp. 371–372. *)
Theorem current_compact_time_cylinder_is_compact (R:realType) n
    (K:set (R_n R n)):
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))) K->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)))
      (@current_compact_time_cylinder_carrier R n K).
Proof.
move=>hK.
change (@compact (real_norm_metric_space
  (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)))
  (@euclidean_cartesian_set R 1%N n
    [set a|0<=@euclidean_one_project R a<=1] K)).
exact:(@current_cartesian_compact R 1%N n
  [set a|0<=@euclidean_one_project R a<=1] K
  (@scalar_current_closed_interval_compact R 0 1) hK).
Qed.

(** Source for [current_compact_time_cylinder]: the exact
    original cylinder as a compact index inside A times U,
    supporting Federer 4.1.14, pp. 371–372. *)
Definition current_compact_time_cylinder (R:realType) n
    (A:set R) (U:set (R_n R n)) (hA:@is_homotopy_parameter_interval R A)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U):
    smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N))
      (@current_homotopy_product_domain R n A U).
Proof.
apply:(@Build_smooth_compact_set R (R_n R (1+n)%N)
  (inner_norm (@euclidean_inner_productP R (1+n)%N))
  (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N))
  (@current_homotopy_product_domain R n A U)
  (@current_compact_time_cylinder_carrier R n (smooth_compact_carrier K))).
- move=>z [ht hx];split.
  + apply:(@current_homotopy_closed_time_band R A hA _).
    exact:ht.
  + exact:smooth_compact_in_domain K _ hx.
- exact:current_compact_time_cylinder_is_compact (smooth_compact_is_compact K).
Defined.

(** Source for [current_compact_time_cylinder_values]: membership
    of (t,x) has exactly the original closed time-band
    and compact-support conditions, supporting Federer 4.1.14,
    pp. 371–372. *)
Lemma current_compact_time_cylinder_values (R:realType) n
    (A:set R) (U:set (R_n R n)) (hA:@is_homotopy_parameter_interval R A)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (t:R) (x:R_n R n):
  smooth_compact_carrier (@current_compact_time_cylinder R n A U hA K)
    (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x))<->
    0<=t<=1 /\smooth_compact_carrier K x.
Proof.
change ((0<=@euclidean_one_project R
  (@euclidean_block_split R 1%N n
    (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x))).1<=1 /\
  smooth_compact_carrier K (@euclidean_block_split R 1%N n
    (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x))).2)<->
      0<=t<=1 /\smooth_compact_carrier K x).
by rewrite euclidean_block_joinK euclidean_one_embedK.
Qed.
