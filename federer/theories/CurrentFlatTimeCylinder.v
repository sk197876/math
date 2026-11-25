(** Federer (1969), 4.1.14, pp. 371–372: the
    original interval current times a fixed-compact-index
    flat current is flat on the exact time cylinder.
    Use 4.1.12, p. 369, with the actual normal time
    segment as the first factor. The input current
    need not be normal or representable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanCartesianMap SmoothCompactSet ScalarCurrentIntervalCompact
  CurrentSpaces CurrentHomotopyUP CurrentHomotopyGeometry CurrentHomotopyDomain
  CurrentHomotopyTimeSegment OrientedSegmentNormal CurrentCartesianDomain
  CurrentCartesianProductSealed CurrentCompactTimeCylinder NormalCurrentsUP
  FlatCurrentsUP FlatCurrentCartesianNormalFactor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_closed_time_band_index]: the exact
    original closed time band as a compact index in A,
    supporting Federer 4.1.14, pp. 371–372. *)
Definition current_closed_time_band_index (R:realType) (A:set R)
    (hA:@is_homotopy_parameter_interval R A):
    smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R 1%N))
      (@current_homotopy_time_domain R A).
Proof.
apply:(@Build_smooth_compact_set R (R_n R 1%N)
  (inner_norm (@euclidean_inner_productP R 1%N))
  (inner_norm_real_norm (@euclidean_inner_productP R 1%N))
  (@current_homotopy_time_domain R A)
  [set t|0<=@euclidean_one_project R t<=1]).
- move=>t ht;exact:(@current_homotopy_closed_time_band R A hA
    (@euclidean_one_project R t) ht).
- exact:(@scalar_current_closed_interval_compact R 0 1).
Defined.

(** Source for [flat_current_time_cylinder]: [0,1] times
    a flat T belongs to the flat space with the exact
    compact index [0,1] times K, supporting Federer
    4.1.14, pp. 371–372. No localization to sptT
    or normality assumption on T is introduced. *)
Theorem flat_current_time_cylinder (R:realType) (h2:(1+1:R)!=0) n m
    (A:set R) (U:set (R_n R n)) (hA:@is_homotopy_parameter_interval R A)
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (T:@current_space R h2 n U hU m):
  @is_flat_current_supported_in R h2 n m U hU K T->
  @is_flat_current_supported_in R h2 (1+n)%N (1+m)%N
    (@current_homotopy_product_domain R n A U)
    (@current_cartesian_domain_open R 1%N n (@current_homotopy_time_domain R A)
      U (@current_homotopy_time_domain_open R A hA) hU)
    (@current_compact_time_cylinder R n A U hA K)
    (@CartesianCurrentProduct.value R h2 1%N n 1%N m
      (@current_homotopy_time_domain R A) U
      (@current_homotopy_time_domain_open R A hA) hU
      (@current_homotopy_time_segment R A hA h2) T).
Proof.
move=>hFlat.
pose AT:=@current_homotopy_time_domain R A.
pose hAT:=@current_homotopy_time_domain_open R A hA.
pose S:=@current_homotopy_time_segment R A hA h2.
pose KT:=@current_closed_time_band_index R A hA.
pose KP:=@current_compact_time_cylinder R n A U hA K.
have hNormal:@normal_currents_supported_in R h2 1%N AT hAT 1%N KT S.
  split.
  - exact:(@oriented_segment_current_normal R h2 1%N AT hAT
      (@euclidean_one_embed R 0) (@euclidean_one_embed R 1)
      (@current_homotopy_time_segment_domain R A hA)).
  - move=>t ht;exact:(@current_homotopy_time_segment_support R A hA h2 t ht).
have hIndex:smooth_compact_carrier KP=
    @euclidean_cartesian_set R 1%N n (smooth_compact_carrier KT) (smooth_compact_carrier K).
  by [].
exact:(@flat_current_cartesian_normal_factor R h2 1%N n 1%N m AT U hAT hU
  KT K KP hIndex S T hNormal hFlat).
Qed.
