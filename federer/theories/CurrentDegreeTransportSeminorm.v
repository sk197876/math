(** Federer (1969), 4.1.8, p. 360: equal-degree
    identifications preserve the original test supports and
    derivative seminorms. This supporting bookkeeping applies
    to the i+j and j+i forms in the slice construction. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentSpaces
  CurrentDegreeTransport SmoothTestSpaces SmoothFunctionSupport SmoothCompactSet
  SmoothFunctionTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentDegreeTransportSeminorm.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation E := (fun d=>@current_smooth_space R h2 n U hU d).
Local Notation ev := (fun d=>@current_smooth_value R h2 n U hU d).
Local Notation hE := (fun d=>@current_smooth_space_laws R h2 n U hU d).
Local Notation D := (fun d=>@current_test_space R h2 n U hU d).

(** Source for [current_test_degree_transport_support]: the
    equal-degree identification in the original slice of Federer
    4.1.8, p. 360, preserves the actual compact support.
    This supporting equality changes no test values or domain. *)
Theorem current_test_degree_transport_support d q (e:d=q) (f:D d):
  @smooth_function_support R X (A_m X R^o q) NX hNX U (E q) (ev q)
    (smooth_test_inclusion (hE q) (@current_test_degree_transport R h2 n U hU d q e f))=
  @smooth_function_support R X (A_m X R^o d) NX hNX U (E d) (ev d)
    (smooth_test_inclusion (hE d) f).
Proof. by case:q /e. Qed.

(** Source for [current_test_degree_transport_seminorm]: every
    original derivative seminorm is unchanged by the equal-degree
    identification in Federer 4.1.8, p. 360. The
    assertion includes degree zero and the empty support index. *)
Theorem current_test_degree_transport_seminorm d q (e:d=q)
    (K:smooth_compact_set hNX U) i (f:D d):
  smooth_function_derivative_seminorm (@current_smooth_derivative_laws R h2 n U hU q) K i
    (smooth_test_inclusion (hE q) (@current_test_degree_transport R h2 n U hU d q e f))=
  smooth_function_derivative_seminorm (@current_smooth_derivative_laws R h2 n U hU d) K i
    (smooth_test_inclusion (hE d) f).
Proof. by case:q /e. Qed.
End CurrentDegreeTransportSeminorm.
