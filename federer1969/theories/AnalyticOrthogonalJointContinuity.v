(** Federer (1969), 3.4.8(5), p. 328:
    original orthogonal pullback is jointly continuous in
    the actual germ metric and O(n). The finite linear
    family theorem applies to the actual orthogonal maps,
    whose evaluations are continuous in the existing group topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm InnerMetric
  HilbertFormCompactness LinearBasis FiniteNormEquivalence
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure HomInner HomSpaceTopology
  AnalyticGermUP AnalyticGermMetric AnalyticOrthogonalPullback
  AnalyticLinearFamilyJointContinuity TopologicalProductMaps ContinuousCommonPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OrthogonalContinuity.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Hypothesis hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation E:=(inner_metric_space hB).
Local Notation H:=(inner_metric_space (hom_inner_productP hB hB he)).
Local Notation L:=(fun g:O=>@orthogonal_element_map R X B hB n e he g).

(** Source for [orthogonal_germ_fixed_vector_continuous]: the
    original orthogonal group topology makes g(x) continuous
    for every x, supporting 3.4.8(5), p. 328. *)
Lemma orthogonal_germ_fixed_vector_continuous (x:X):
  continuous (fun g:O=>(L g x:real_norm_metric_space hNX)).
Proof.
have hPair:continuous (fun g:O=>((L g,x):H*E)).
  exact:(@continuous_common_domain_pair O H E L (fun _=>x)
    (@orthogonal_element_continuous R X B hB n e he) (@cst_continuous O E x)).
have hInner:continuous (fun g:O=>(L g x:E)).
  move=>g;exact:(continuous_comp (hPair g)
    (@hom_evaluation_continuous R X X B B hB hB n e he (L g,x))).
move=>g U hU;apply:hInner.
exact:(proj2 (@inner_real_norm_same_nbhs R X B hB (L g x) U) hU).
Qed.

(** Source for [analytic_orthogonal_germ_map_jointly_continuous]:
    the actual joint continuity of orthogonal pullback
    used in 3.4.8(5), p. 328. Both the germ
    and the original orthogonal map vary. Individual
    continuity alone is not used as a substitute. *)
Theorem analytic_orthogonal_germ_map_jointly_continuous:
  continuous (fun p:(@analytic_germ_metric R X NX hNX 0)*O=>
    (@analytic_orthogonal_germ_map R X B hB n e he p.2 p.1:
      @analytic_germ_metric R X NX hNX 0)).
Proof.
exact:(@analytic_linear_family_pullback_jointly_continuous R X X NX NX hNX hNX 0 0
  n e he O L (fun g:O=>@analytic_orthogonal_germ_map R X B hB n e he g)
  (fun g=>@analytic_orthogonal_germ_map_specification R X B hB n e he g)
  (fun g=>@orthogonal_germ_coordinate_zero R X B hB n e he g)
  orthogonal_germ_fixed_vector_continuous).
Qed.
End OrthogonalContinuity.
