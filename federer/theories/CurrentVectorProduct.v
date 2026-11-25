(** Federer (1969), 4.1.7, pp. 355–356: actual
    multiplication of currents by smooth multivector
    fields, defined by the original test action. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentVectorSpaces SmoothTestTopology
  ContinuousRealDual ContinuousRealDualTranspose CurrentTestVectorInterior OpenFamilyTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentVectorProduct.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable xi:@current_vector_smooth_space R h2 n U hU k.
Local Notation hE := (fun m=>@current_smooth_space_laws R h2 n U hU m).
Local Notation hD := (fun m=>@current_smooth_derivative_laws R h2 n U hU m).
Local Notation DT := (fun m=>@current_test_space R h2 n U hU m).
Local Notation O := (fun m=>@current_test_opens R h2 n U hU m).
Local Notation hO := (fun m=>(smooth_test_final_topology_laws (hE m) (hD m)).1).
Local Notation C := (fun m=>@current_space R h2 n U hU m).
Local Notation P := (@current_test_vector_interior R h2 n k p U hU xi).
Local Notation hP := (@current_test_vector_interior_continuous R h2 n k p U hU xi).

(** Source for [current_vector_product]: the original
    T wedge xi, Federer 4.1.7, pp. 355–356. *)
Definition current_vector_product:Hom (C p) (C (k+p)):=
  @continuous_real_dual_transpose R (DT (k+p)) (DT p)
    (O (k+p)) (O p) (hO (k+p)) (hO p) P hP.

(** Source for [current_vector_product_evaluation]:
    (T wedge xi)(psi)=T(xi interior psi), the
    original defining equation of Federer 4.1.7,
    pp. 355–356. *)
Theorem current_vector_product_evaluation T psi:
  @current_value R h2 n U hU (k+p) (current_vector_product T) psi=
    @current_value R h2 n U hU p T (P psi).
Proof. exact:continuous_real_dual_transpose_evaluation. Qed.

(** Source for [current_vector_product_weak_continuous]:
    multiplication by a fixed smooth multivector is
    weakly continuous, supporting Federer 4.1.7,
    pp. 355–356. *)
Theorem current_vector_product_weak_continuous:
  open_family_continuous (@current_weak_opens R h2 n U hU p)
    (@current_weak_opens R h2 n U hU (k+p)) current_vector_product.
Proof. exact:continuous_real_dual_transpose_weak_continuous. Qed.
End CurrentVectorProduct.
