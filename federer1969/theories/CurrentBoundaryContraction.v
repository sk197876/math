(** Federer (1969), 4.1.7, p. 356: the
    original boundary–contraction identity, obtained
    from the actual graded Leibniz rule on tests. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentEvaluation CurrentBoundary
  CurrentContraction CurrentDegreeTransport CurrentTestFormProduct CurrentTestExteriorDerivative
  CurrentTestExteriorLeibniz SmoothCurrentExteriorDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentBoundaryContraction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation C := (fun m=>@current_space R h2 n U hU m).
Local Notation P := (fun a b=>@current_contraction R h2 n a b U hU).
Local Notation bd := (fun m=>@current_boundary R h2 n m U hU).
Local Notation d := (fun m=>@smooth_current_exterior_derivative R h2 n m U hU).
Local Notation Tr := (fun m q (h:m=q)=>@current_degree_transport R h2 n U hU m q h).

(** Source for [current_boundary_contraction]:
    (boundary T) contracted phi equals T contracted
    d phi plus (-1)^degree(phi) times the boundary
    of T contracted phi, Federer 4.1.7, p. 356.
    Equal positive input degrees are transported
    explicitly; every original admissible k is retained. *)
Theorem current_boundary_contraction (T:C (k+p).+1) phi:
  P k p phi (bd (k+p) T)=
    P k.+1 p (d k phi) (Tr _ _ (esym (addSn k p)) T)+
      (-1:R)^+k*:bd p (P k p.+1 phi (Tr _ _ (esym (addnS k p)) T)).
Proof.
apply:(@current_values_extensional R h2 n p U hU)=>psi.
rewrite current_contraction_evaluation current_boundary_evaluation.
rewrite linearD linearZ !hom_addE !hom_scaleE.
rewrite current_contraction_evaluation current_boundary_evaluation current_contraction_evaluation.
rewrite !current_degree_reverse_evaluation.
by rewrite current_test_exterior_leibniz linearD linearZ.
Qed.
End CurrentBoundaryContraction.
