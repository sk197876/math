(** Federer (1969), 4.1.7, p. 356: the
    original boundary is the transpose of the actual
    exterior derivative on test forms. All spaces
    retain Federer's literal final topology. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothTestTopology
  ContinuousRealDual ContinuousRealDualTranspose CurrentTestExteriorDerivative OpenFamilyTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation hE0 := (@current_smooth_space_laws R h2 n U hU m).
Local Notation hE1 := (@current_smooth_space_laws R h2 n U hU m.+1).
Local Notation hD0 := (@current_smooth_derivative_laws R h2 n U hU m).
Local Notation hD1 := (@current_smooth_derivative_laws R h2 n U hU m.+1).
Local Notation DT0 := (@current_test_space R h2 n U hU m).
Local Notation DT1 := (@current_test_space R h2 n U hU m.+1).
Local Notation O0 := (@current_test_opens R h2 n U hU m).
Local Notation O1 := (@current_test_opens R h2 n U hU m.+1).
Local Notation hO0 := (smooth_test_final_topology_laws hE0 hD0).1.
Local Notation hO1 := (smooth_test_final_topology_laws hE1 hD1).1.
Local Notation C0 := (@current_space R h2 n U hU m).
Local Notation C1 := (@current_space R h2 n U hU m.+1).
Local Notation d := (@current_test_exterior_derivative R h2 n m U hU).
Local Notation hd := (@current_test_exterior_derivative_continuous R h2 n m U hU).

(** Source for [current_boundary]: the actual positive-
    degree current boundary, Federer 4.1.7, p. 356. *)
Definition current_boundary:Hom C1 C0:=
  @continuous_real_dual_transpose R DT0 DT1 O0 O1 hO0 hO1 d hd.

(** Source for [current_boundary_evaluation]: the original
    equation (boundary T)(psi)=T(d psi),
    Federer 4.1.7, p. 356. *)
Theorem current_boundary_evaluation T phi:
  @current_value R h2 n U hU m (current_boundary T) phi=
    @current_value R h2 n U hU m.+1 T (d phi).
Proof. exact:continuous_real_dual_transpose_evaluation. Qed.

(** Source for [current_boundary_weak_continuous]: the
    original transpose is weakly continuous, supporting
    the current boundary of Federer 4.1.7, p. 356. *)
Theorem current_boundary_weak_continuous:
  open_family_continuous (@current_weak_opens R h2 n U hU m.+1)
    (@current_weak_opens R h2 n U hU m) current_boundary.
Proof. exact:continuous_real_dual_transpose_weak_continuous. Qed.
End CurrentBoundary.
