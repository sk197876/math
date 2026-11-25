(** Federer (1969), 4.1.7, p. 356: the
    original contraction identity for an arbitrary
    zero-current. No integral representation or
    additional regularity of the current is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentVectorSpaces CurrentDegreeTransport
  CurrentEvaluation CurrentContraction CurrentVectorProduct CurrentTestFormProduct CurrentTestVectorInterior
  SmoothCurrentVectorContraction CurrentZeroTestVectorContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentZeroVectorContraction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation C := (fun m=>@current_space R h2 n U hU m).
Local Notation E := (fun m=>@current_smooth_space R h2 n U hU m).
Local Notation V := (fun m=>@current_vector_smooth_space R h2 n U hU m).
Local Notation P := (@current_contraction R h2 n k p U hU).
Local Notation W := (fun m=>@current_vector_product R h2 n m 0 U hU).
Local Notation L := (@smooth_current_vector_contraction R h2 n k p U hU).
Local Notation Tr := (fun m=>@current_degree_transport R h2 n U hU (m+0) m (addn0 m)).

(** Source for [current_zero_vector_contraction]:
    (T wedge xi) contracted phi equals
    T wedge (xi contracted phi) when
    dim T=0, Federer 4.1.7, p. 356,
    seventh displayed identity. The parameterisation
    dim xi=k+p retains every permitted degree. *)
Theorem current_zero_vector_contraction (T:C 0) (xi:V (k+p)) (phi:E k):
  P phi (Tr (k+p) (W (k+p) xi T))=Tr p (W p (L xi phi) T).
Proof.
apply:(@current_values_extensional R h2 n p U hU)=>psi.
rewrite current_contraction_evaluation !current_degree_transport_evaluation.
rewrite !current_vector_product_evaluation.
congr (@current_value R h2 n U hU 0 T _).
exact:current_zero_test_vector_contraction.
Qed.
End CurrentZeroVectorContraction.
