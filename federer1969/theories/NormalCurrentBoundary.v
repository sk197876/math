(** Federer (1969), 4.1.7, pp. 356, 358:
    the positive-degree boundary of a
    normal current is normal. This supporting
    consequence uses the original boundary
    squared, integration representation and compact
    support laws, with the printed degree-zero
    convention retained. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct SmoothCompactSet CurrentSpaces CurrentBoundary
  CurrentBoundarySquared CurrentBoundarySupport CurrentSupportGeometry CurrentRepresentableLinear
  CurrentIntegrationCriterion NormalCurrentsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section NormalCurrentBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.

(** Source for [normal_current_boundary]: the
    original boundary of every positive-degree
    normal current is normal, supporting the
    boundary action on class-one forms in
    Federer 4.1.7, p. 358, by
    the preceding boundary laws on p. 356. *)
Theorem normal_current_boundary m (T:@current_space R h2 n U hU m.+1):
  @is_normal_current R h2 n U hU m.+1 T->
  @is_normal_current R h2 n U hU m (@current_boundary R h2 n m U hU T).
Proof.
move=>hNormal;split.
- split;first exact:hNormal.1.2.
  case:m T hNormal=>[|d] T hNormal;first by [].
  change (@is_integration_representable_current R h2 n d U hU
    (@current_boundary R h2 n d U hU (@current_boundary R h2 n d.+1 U hU T))).
  rewrite current_boundary_squared;exact:represented_current_zero.
- pose K:=@Build_smooth_compact_set R X NX hNX U
    (@current_support R h2 n U hU m.+1 T) (fun x hx=>hx.1) hNormal.2.
  exact:(@current_support_compact_bound R h2 n m U hU K
    (@current_boundary R h2 n m U hU T) (@current_boundary_support_subset R h2 n m U hU T)).
Qed.
End NormalCurrentBoundary.
