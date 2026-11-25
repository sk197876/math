(** Federer (1969), 4.1.7, p. 356: original
    zero-dimensional currents are scalar distributions.
    This identifies their actual continuous-dual spaces
    through the original inverse coefficient test maps. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentEvaluation CurrentScalarTestMaps
  Distributions SmoothTestTopology ContinuousRealDual ContinuousRealDualTranspose
  LinearSubspaceRepresentationUP OpenFamilyTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentScalarDistributions.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NS := (fun t:R^o=>`|t|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation TC := (@current_test_space R h2 n U hU 0%N).
Local Notation TS := (@distribution_test_space R X R^o NX NS hNX hNS U hU).
Local Notation OC := (@current_test_opens R h2 n U hU 0%N).
Local Notation OS := (@distribution_test_opens R X R^o NX NS hNX hNS U hU).
Local Notation hOC := (smooth_test_final_topology_laws
  (@current_smooth_space_laws R h2 n U hU 0%N)
  (@current_smooth_derivative_laws R h2 n U hU 0%N)).1.
Local Notation hOS := (@distribution_test_topology_laws R X R^o NX NS hNX hNS U hU).1.
Local Notation CC := (@current_space R h2 n U hU 0%N).
Local Notation DS := (@distribution_space R X R^o NX NS hNX hNS U hU).
Local Notation cvalue := (@current_value R h2 n U hU 0%N).
Local Notation svalue := (@distribution_value R X R^o NX NS hNX hNS U hU).
Local Notation a := (@current_scalar_test_coefficients R h2 n U hU).
Local Notation ha := (@current_scalar_test_coefficients_continuous R h2 n U hU).
Local Notation b := (@current_zero_form_test R h2 n U hU).
Local Notation hb := (@current_zero_form_test_continuous R h2 n U hU).

(** Source for [scalar_distribution_current]: the original
    scalar distribution as a zero-current, supporting
    Federer 4.1.7, p. 356. *)
Definition scalar_distribution_current:Hom DS CC:=
  @continuous_real_dual_transpose R TC TS OC OS hOC hOS a ha.

(** Source for [current_scalar_distribution]: the original
    zero-current as a scalar distribution, supporting
    Federer 4.1.7, p. 356. *)
Definition current_scalar_distribution:Hom CC DS:=
  @continuous_real_dual_transpose R TS TC OS OC hOS hOC b hb.

(** Source for [scalar_distribution_current_evaluation]:
    the original zero-current acts by the scalar
    coefficient test, supporting Federer 4.1.7,
    p. 356. *)
Lemma scalar_distribution_current_evaluation T phi:
  cvalue (scalar_distribution_current T) phi=svalue T (a phi).
Proof. exact:continuous_real_dual_transpose_evaluation. Qed.

(** Source for [current_scalar_distribution_evaluation]:
    the original scalar distribution acts by the
    corresponding zero-form test, supporting Federer
    4.1.7, p. 356. *)
Lemma current_scalar_distribution_evaluation T phi:
  svalue (current_scalar_distribution T) phi=cvalue T (b phi).
Proof. exact:continuous_real_dual_transpose_evaluation. Qed.

(** Source for [current_scalar_distribution_inverse]:
    the original identification returns every zero-
    current unchanged, supporting Federer 4.1.7,
    p. 356. *)
Theorem current_scalar_distribution_inverse T:
  scalar_distribution_current (current_scalar_distribution T)=T.
Proof.
apply:(@current_values_extensional R h2 n 0%N U hU)=>phi.
by rewrite scalar_distribution_current_evaluation current_scalar_distribution_evaluation
  current_scalar_test_coefficients_inverse.
Qed.

(** Source for [scalar_distribution_current_inverse]:
    the original identification returns every scalar
    distribution unchanged, supporting Federer
    4.1.7, p. 356. *)
Theorem scalar_distribution_current_inverse T:
  current_scalar_distribution (scalar_distribution_current T)=T.
Proof.
apply:(subspace_representation_injective (@continuous_real_dual_model_laws R TS OS hOS)).
apply:hom_ext=>phi.
change (svalue (current_scalar_distribution (scalar_distribution_current T)) phi=svalue T phi).
by rewrite current_scalar_distribution_evaluation scalar_distribution_current_evaluation
  current_zero_form_test_inverse.
Qed.

(** Source for [scalar_distribution_current_weak_continuous]:
    the original scalar identification preserves weak
    continuity, supporting Federer 4.1.7, p. 356. *)
Theorem scalar_distribution_current_weak_continuous:
  open_family_continuous (@distribution_weak_opens R X R^o NX NS hNX hNS U hU)
    (@current_weak_opens R h2 n U hU 0%N) scalar_distribution_current.
Proof. exact:continuous_real_dual_transpose_weak_continuous. Qed.

(** Source for [current_scalar_distribution_weak_continuous]:
    the inverse original scalar identification preserves
    weak continuity, supporting Federer 4.1.7, p. 356. *)
Theorem current_scalar_distribution_weak_continuous:
  open_family_continuous (@current_weak_opens R h2 n U hU 0%N)
    (@distribution_weak_opens R X R^o NX NS hNX hNS U hU) current_scalar_distribution.
Proof. exact:continuous_real_dual_transpose_weak_continuous. Qed.
End CurrentScalarDistributions.
