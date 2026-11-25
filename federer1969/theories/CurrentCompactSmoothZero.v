(** Federer (1969), 4.1.20, p. 378: a zero projected
    current has zero value on the smooth coordinate volume.
    Reuse the unique compact smooth-dual extension of 4.1.7,
    p. 355, and the existing linear restriction and evaluation.
    This supports the printed evaluation on a noncompact form. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentCompactExtensionUP CurrentCompactExtensionSealed
  CurrentCompactSmoothValue SmoothFunctionTopology ContinuousRealDual.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_compact_smooth_zero]: the unique smooth
    extension of a zero original current is zero, as used in
    the last two equalities of Federer 4.1.20, p. 378, by
    4.1.7, p. 355. Every actual compactness witness is allowed. *)
Theorem current_compact_smooth_zero (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m)
    (hCompact:@compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n U hU m T)):
  T=0->forall phi:@current_smooth_space R h2 n U hU m,
    @current_compact_smooth_value R h2 n m U hU T hCompact phi=0.
Proof.
move=>hZero phi.
pose E:=@current_smooth_space R h2 n U hU m.
pose O:=smooth_function_opens (@current_smooth_derivative_laws R h2 n U hU m).
pose hO:=(smooth_function_topology_laws (@current_smooth_derivative_laws R h2 n U hU m)).1.
pose L:=@CompactCurrentExtension.value R h2 n m U hU T hCompact.
have hL:L=0.
  apply:(@current_compact_extension_unique R h2 n m U hU T).
  - exact:(@CompactCurrentExtension.laws R h2 n m U hU T hCompact).
  - change (@current_smooth_dual_restriction R h2 n U hU m 0=T).
    by rewrite linear0 hZero.
change (@continuous_real_dual_evaluation R E O hO L phi=0).
by rewrite hL linear0 hom_zeroE.
Qed.
