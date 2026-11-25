(** Federer (1969), 4.1.11, p. 365: identify equal
    positive input degrees and their matching lower degrees in
    the original four join boundary formulas. Reuse only the
    already proved current transport and actual boundary. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary CurrentDegreeTransport
  CurrentDegreeTransportIdentity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_boundary_degree_transport]: the
    original positive-degree boundary commutes with identification
    of equal natural degrees, supporting Federer 4.1.11, p. 365.
    No boundary of a zero-degree current is introduced. *)
Theorem current_boundary_degree_transport
    (R : realType) (h2 : (1+1:R)!=0) n (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    k l (e : k=l) (T : @current_space R h2 n U hU k.+1) :
  @current_degree_transport R h2 n U hU k l e
    (@current_boundary R h2 n k U hU T) =
  @current_boundary R h2 n l U hU
    (@current_degree_transport R h2 n U hU k.+1 l.+1
      (congr1 (fun r : nat => r.+1) e) T).
Proof.
case: l / e.
by rewrite !current_degree_transport_identity.
Qed.
