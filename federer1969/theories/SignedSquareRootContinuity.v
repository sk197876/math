(** Federer (1969), 3.2.7, p. 246:
    continuity of the signed square-root parameter,
    including its singular derivative point zero.
    The proof uses the abstract norm law and actual
    finite derivatives elsewhere. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import RealMetricBackground SignedSquareRootUP SignedSquareRootSealed SignedSquareRootLaws
  SignedSquareRootDerivative RealDerivativeContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [signed_root_continuous]: supporting
    continuous change of parameter for the third
    example of Federer 3.2.7, p. 246.
    At zero, the exact square-root norm gives the
    epsilon-squared radius; elsewhere use actual differentiability. *)
Theorem signed_root_continuous (R:realType):
  continuous (@SignedSquareRoot.value R:real_line_metric R->real_line_metric R).
Proof.
move=>a; case:(eqVneq a 0)=>[->|ha].
- move=>U /nbhs_ballP[e he hU].
  rewrite signed_root_zero in hU.
  have hDelta:0<e^+2 by rewrite exprn_gt0.
  change (nbhs (0:real_line_metric R) [set y|U (SignedSquareRoot.value y)]).
  apply/nbhs_ballP; exists (e^+2); first exact hDelta.
  move=>y hy; apply:hU.
  have hy':`|y|<e^+2 by move:hy; rewrite /ball /= sub0r normrN.
  have hRoot:Num.sqrt `|y|<Num.sqrt (e^+2) by rewrite (@ltr_sqrt R `|y| (e^+2) hDelta).
  rewrite sqrtr_sqr (ger0_norm (ltW he)) in hRoot.
  by rewrite /ball /= sub0r normrN signed_root_absolute_value.
- exact (real_derivative_continuous_at (@signed_root_actual_derivative R a ha)).
Qed.
