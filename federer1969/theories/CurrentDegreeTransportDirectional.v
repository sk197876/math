(** Federer (1969), 4.1.8, p. 360: equal-degree
    identifications commute with actual test differentiation.
    This supporting bookkeeping preserves the original vertical
    derivative when i+j is identified with j+i. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms
  CurrentSpaces CurrentDegreeTransport DistributionDirectionalDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentDegreeTransportDirectional.
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
Local Notation Diff := (fun d v=>@distribution_test_directional_derivative R X (A_m X R^o d)
  NX (@current_form_comass R h2 n d) hNX (@current_form_comass_real_norm R h2 n d)
  U hU (E d) (ev d) (hE d) (@current_smooth_derivatives R h2 n U hU d)
  (@current_smooth_derivative_laws R h2 n U hU d) v).

(** Source for [current_test_degree_transport_directional]:
    the equal-degree cast of the original differentiated
    test is the derivative of its cast, supporting
    Federer 4.1.8, p. 360. The original open domain,
    every direction and both zero-degree conventions are preserved. *)
Theorem current_test_degree_transport_directional d q (e:d=q) (f:D d) v:
  @current_test_degree_transport R h2 n U hU d q e (Diff d v f)=
    Diff q v (@current_test_degree_transport R h2 n U hU d q e f).
Proof. by case:q /e. Qed.
End CurrentDegreeTransportDirectional.
