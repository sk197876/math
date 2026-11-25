(** Federer (1969), 4.1.7–4.1.8, pp. 356–362,
    used in the support obstruction of 4.1.12,
    p. 368: a compact one-current has boundary
    total zero. Evaluate the original boundary on
    the actual smooth constant one, whose derivative vanishes. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentBoundary
  CurrentCompactSmoothValue CurrentCompactBoundarySmooth CurrentConstantExteriorDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_compact_boundary_total_zero]:
    boundary T(1)=T(d1)=0 for every compact
    original one-current, supporting the first example of
    Federer 4.1.12, p. 368, by the actual
    smooth extension and boundary of 4.1.7–4.1.8.
    No representation or normality premise is added. *)
Theorem current_compact_boundary_total_zero (R:realType) (h2:(1+1:R)!=0) n
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU 1%N)
    (hCompact:@compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n U hU 1%N T)):
  @current_compact_total R h2 n U hU (@current_boundary R h2 n 0%N U hU T)
    (@current_compact_boundary_compact R h2 n 0%N U hU T hCompact)=0.
Proof.
rewrite /current_compact_total current_compact_boundary_smooth_value
  current_constant_form_exterior_zero.
exact:linear0.
Qed.
