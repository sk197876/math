(** Federer (1969), 4.1.11, pp. 364–366: linear operations
    on S times [0,1] times T support the original boundary and
    simplicial formulas. Reuse both original Cartesian linearity
    laws of 4.1.8, p. 361, and the public degree transport. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentCartesianProductBilinear CurrentDegreeTransport
  CurrentJoinDomain CurrentJoinSourceChain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CurrentJoinSourceLinear.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n i j : nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _ : X => True).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x : X) (_ : True) =>
  @norm_full_domain_interior R X NX x).
Local Notation C := (fun k => @current_space R h2 n Full hFull k).
Local Notation Chain := (@current_join_source_chain R h2 n i j).

(** Source for [current_join_source_first_linear]: the
    original ordered source product is linear in S, supporting
    Federer 4.1.11, pp. 364–366. Arbitrary currents are allowed. *)
Theorem current_join_source_first_linear c (S U : C i) (T : C j) :
  Chain (c*:S+U) T = c*:Chain S T + Chain U T.
Proof.
rewrite /current_join_source_chain current_cartesian_product_first_linear.
exact: hom_linear.
Qed.

(** Source for [current_join_source_second_linear]: the
    original ordered source product is linear in T, supporting
    Federer 4.1.11, pp. 364–366. No representation is assumed. *)
Theorem current_join_source_second_linear c (S : C i) (T U : C j) :
  Chain S (c*:T+U) = c*:Chain S T + Chain S U.
Proof.
rewrite /current_join_source_chain !current_cartesian_product_second_linear.
exact: hom_linear.
Qed.
End CurrentJoinSourceLinear.
