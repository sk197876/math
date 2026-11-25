(** Federer (1969), 4.1.7, pp. 355–356: the
    original contraction of a current with a smooth
    form, defined by its actual test action. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothTestTopology
  ContinuousRealDual ContinuousRealDualTranspose CurrentTestFormProduct OpenFamilyTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentContraction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable phi:@current_smooth_space R h2 n U hU k.
Local Notation hE := (fun m=>@current_smooth_space_laws R h2 n U hU m).
Local Notation hD := (fun m=>@current_smooth_derivative_laws R h2 n U hU m).
Local Notation DT := (fun m=>@current_test_space R h2 n U hU m).
Local Notation O := (fun m=>@current_test_opens R h2 n U hU m).
Local Notation hO := (fun m=>(smooth_test_final_topology_laws (hE m) (hD m)).1).
Local Notation C := (fun m=>@current_space R h2 n U hU m).
Local Notation P := (@current_test_form_product R h2 n k p U hU phi).
Local Notation hP := (@current_test_form_product_continuous R h2 n k p U hU phi).

(** Source for [current_contraction]: T contracted with
    the original smooth k-form, Federer 4.1.7,
    pp. 355–356. The input degree k+p retains every
    original admissible k and output degree p. *)
Definition current_contraction:Hom (C (k+p)) (C p):=
  @continuous_real_dual_transpose R (DT p) (DT (k+p))
    (O p) (O (k+p)) (hO p) (hO (k+p)) P hP.

(** Source for [current_contraction_evaluation]:
    (T contracted phi)(psi)=T(phi wedge psi),
    Federer 4.1.7, pp. 355–356. *)
Theorem current_contraction_evaluation T psi:
  @current_value R h2 n U hU p (current_contraction T) psi=
    @current_value R h2 n U hU (k+p) T (P psi).
Proof. exact:continuous_real_dual_transpose_evaluation. Qed.

(** Source for [current_contraction_weak_continuous]:
    fixed smooth contraction is weakly continuous on
    actual currents, supporting Federer 4.1.7,
    pp. 355–356. *)
Theorem current_contraction_weak_continuous:
  open_family_continuous (@current_weak_opens R h2 n U hU (k+p))
    (@current_weak_opens R h2 n U hU p) current_contraction.
Proof. exact:continuous_real_dual_transpose_weak_continuous. Qed.
End CurrentContraction.
