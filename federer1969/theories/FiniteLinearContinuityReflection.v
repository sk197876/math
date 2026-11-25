(** Federer (1969), 3.4.8(5), p. 328:
    finitely many derivative coordinates detect continuity
    in the actual form norm. This background lemma uses
    the project's finite norm comparison, 2.7.16, p. 134. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP RealSeminormOperations NormMetric LinearBasis
  FiniteNormEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_injective_linear_continuity_reflection]:
    finite derivative coordinates determine the original norm
    topology, supporting the joint continuity used in
    3.4.8(5), p. 328. The injection induces a
    genuine norm; finite norm comparison proves the inverse
    estimate. No continuity of an inverse is assumed. *)
Theorem finite_injective_linear_continuity_reflection
    (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) n (b:'I_n->X) (hb:is_basis b)
    (L:Hom X Y) (hL:injective L) (P:topologicalType) (f:P->X):
  continuous (fun p:P=>(L (f p):real_norm_metric_space hNY)) ->
  continuous (fun p:P=>(f p:real_norm_metric_space hNX)).
Proof.
move=>hF.
pose NP:=fun x:X=>NY (L x).
have hNP:is_real_norm NP:=@real_norm_injective_precompose R X Y NY hNY
  (hom_as_linear L) hL.
have [C hC hBound]:=@finite_norm_comparison R X NP NX hNP hNX n b hb.
move=>p U hU.
have [epsilon hEpsilon hBall]:=proj1
  (metricType_numDomainType.nbhs_mdistP (f p:real_norm_metric_space hNX) U) hU.
pose delta:R:=epsilon/C.
have hDelta:0<delta by rewrite /delta divr_gt0.
have hBallY:nbhs (L (f p):real_norm_metric_space hNY)
    [set y:real_norm_metric_space hNY|NY (L (f p)-y)<delta].
  apply:(proj2 (metricType_numDomainType.nbhs_mdistP (L (f p):real_norm_metric_space hNY) _)).
  by exists delta.
have hNear:=hF p _ hBallY.
change (nbhs p (fun q:P=>NY (L (f p)-L (f q))<delta)) in hNear.
change (nbhs p (fun q:P=>U (f q))).
apply:filterS hNear=>q hq;apply:hBall.
change (is_true (NX (f p-f q)<epsilon)).
apply:le_lt_trans (hBound (f p-f q)) _.
rewrite /NP linearB /=.
by move:hq;rewrite /delta ltr_pdivlMr // mulrC.
Qed.
