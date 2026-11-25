(** Federer (1969), 4.1.12, p. 368: contraction
    by a compact test has support in that test's
    original support. This is the preceding arbitrary-
    compact contraction support bound of 4.1.7, applied
    to the compact test support itself. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothCompactSet SmoothTestSpaces SmoothTestEvaluation CurrentSupportGeometry
  CurrentContraction CurrentContractionCompactSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentTestContractionSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation hE := (@current_smooth_space_laws R h2 n U hU k).
Variable gamma:@current_test_space R h2 n U hU k.

(** Source for [current_contraction_test_support_subset]:
    spt(T contracted gamma) is contained in the
    original spt gamma, supporting the exact compact
    index in Federer 4.1.12, p. 368. This
    locality assertion holds for arbitrary currents. *)
Theorem current_contraction_test_support_subset (T:@current_space R h2 n U hU (k+p)):
  @current_support R h2 n U hU p
    (@current_contraction R h2 n k p U hU (smooth_test_inclusion hE gamma) T) `<=`
    @current_test_support R h2 n k U hU gamma.
Proof.
pose K:=@Build_smooth_compact_set R X NX hNX U
  (@current_test_support R h2 n k U hU gamma) (fun x hx=>hx.1)
  (smooth_test_support_compact hE gamma).
exact:(@current_contraction_support_compact_bound R h2 n k p U hU K
  (smooth_test_inclusion hE gamma) T (fun x hx=>hx)).
Qed.
End CurrentTestContractionSupport.
