(** Federer (1969), 4.1.14, p. 371: the
    original interval product of a locally flat
    current is locally flat. Apply the point
    criterion of 4.1.12, p. 368, replace T
    near each spatial point by one compact flat
    current, and reuse the normal-factor product
    theorem on the exact time cylinder. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockCoordinates EuclideanCartesianMap CurrentSpaces CurrentSupportGeometry SmoothCompactSet
  CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentCartesianProductBilinear CurrentCartesianSupportEquality
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTimeSegment
  FlatCurrentsUP LocallyFlatPointCriterion CurrentCompactTimeCylinder CurrentFlatTimeCylinder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [locally_flat_current_time_cylinder]:
    the actual [0,1] times T is locally
    flat on A times U, supporting the
    original Lipschitz homotopy formula in Federer
    4.1.14, p. 371. T need not have
    compact support, finite mass or a representation. *)
Theorem locally_flat_current_time_cylinder (R:realType) (h2:(1+1:R)!=0)
    n m (A:set R) (U:set (R_n R n))
    (hA:@is_homotopy_parameter_interval R A)
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m):
  @is_locally_flat_current R h2 n m U hU T->
  @is_locally_flat_current R h2 (1+n)%N (1+m)%N
    (@current_homotopy_product_domain R n A U)
    (@current_cartesian_domain_open R 1%N n (@current_homotopy_time_domain R A)
      U (@current_homotopy_time_domain_open R A hA) hU)
    (@CartesianCurrentProduct.value R h2 1%N n 1%N m
      (@current_homotopy_time_domain R A) U
      (@current_homotopy_time_domain_open R A hA) hU
      (@current_homotopy_time_segment R A hA h2) T).
Proof.
move=>hT.
pose AT:=@current_homotopy_time_domain R A.
pose hAT:=@current_homotopy_time_domain_open R A hA.
pose AU:=@current_homotopy_product_domain R n A U.
pose hAU:=@current_cartesian_domain_open R 1%N n AT U hAT hU.
pose S:=@current_homotopy_time_segment R A hA h2.
pose Product:=@CartesianCurrentProduct.value R h2 1%N n 1%N m AT U hAT hU.
apply:(@locally_flat_point_criterion R h2 (1+n)%N (1+m)%N AU hAU (Product S T)).2.
move=>z hz.
have[Q [hQ hNear]]:=(@locally_flat_point_criterion R h2 n m U hU T).1 hT
  (@euclidean_block_split R 1%N n z).2 hz.2.
have[K hQK]:=hQ.
exists (Product S Q);split.
- exists (@current_compact_time_cylinder R n A U hA K).
  exact:(@flat_current_time_cylinder R h2 n m A U hA hU K Q hQK).
have hDifference:Product S T-Product S Q=Product S (T-Q).
  exact:esym (linB ((@current_cartesian_product_bilinear R h2 1%N n
    1%N m AT U hAT hU).2 S) T Q).
move=>hSupport.
rewrite hDifference (@current_cartesian_support R h2 1%N n 1%N m
  AT U hAT hU S (T-Q)) in hSupport.
exact:hNear hSupport.2.
Qed.
