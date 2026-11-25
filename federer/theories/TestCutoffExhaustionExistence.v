(** Federer (1969), 4.1.2, p. 348: existence
    of the actual test cutoff exhaustion for every
    open U, reusing the original compact exhaustion
    and smooth compact cutoffs from 4.1.1. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP LinearBasis NormRegularity NormRegularityOperations
  CompactSupportFunctionUP SmoothCompactSet SmoothCompactExhaustionUP SmoothCompactExhaustionSealed
  SmoothCompactCutoffUP SmoothCompactCutoffSealed SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation
  SmoothTestRepresentation TestCutoffExhaustionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [test_cutoff_exhaustion_exists]: the omega_j
    of Federer 4.1.2, p. 348, exist
    as actual members of D(U,R), including
    empty U and zero-dimensional source. *)
Theorem test_cutoff_exhaustion_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (b:'I_n->X) (hb:is_basis b)
    (U:set X) (hU:forall x,U x ->norm_domain_interior NX U x)
    (E:lmodType R) (ev:E->X->R^o)
    (hE:is_smooth_function_space hNX (@scalar_absolute_value_norm R) U ev):
  exists omega:nat->smooth_test_space hE,@is_test_cutoff_exhaustion R X NX hNX U E ev hE omega.
Proof.
pose K:=@SmoothCompactExhaustion.value R X NX hNX n b hb U hU.
have hK:=@SmoothCompactExhaustion.laws R X NX hNX n b hb U hU.
pose chi j:=@SmoothCompactCutoff.value R X NX hNX n b hb U (K j) hU.
have hChi j:=@SmoothCompactCutoff.laws R X NX hNX n b hb U (K j) hU.
have hFor j:exists w:smooth_test_space hE,forall x,U x ->smooth_test_value hE w x=chi j x.
  pose C:=@Build_smooth_compact_set R X NX hNX U
    (@real_function_support R (real_norm_metric_space hNX) (chi j))
    (smooth_cutoff_support_in_domain (hChi j)) (smooth_cutoff_compact (hChi j)).
  have hClass:norm_class_all_orders hNX (@scalar_absolute_value_norm R) U (chi j).
    move=>k; exact:(@norm_class_open_restriction R X R^o NX (fun t:R^o=>`|t|)
      hNX (@scalar_absolute_value_norm R) (fun _=>True) U (chi j) k
      (fun _ _=>Logic.I) hU (smooth_cutoff_class (hChi j) k)).
  apply:(@smooth_test_represents_compact_function R X R^o NX (fun t:R^o=>`|t|)
    hNX (@scalar_absolute_value_norm R) U E ev hE C (chi j) hClass)=>x hx.
  case:(pselect (chi j x=0))=>// hne.
  exfalso; apply:hx; exact:(@subset_closure (real_norm_metric_space hNX) _ x hne).
have[omega hOmega]:=choice hFor.
exists omega=>C.
have[v [W [hW [hCW hWK]]]]:=smooth_compact_exhaustion_neighbourhood hK C.
exists v.+1; split; first exact: ltn0Sn.
move=>j hj x hx.
have hVj:(v<=j)%N:=leq_trans (leqnSn v) hj.
have hXK:smooth_compact_carrier (K j) x.
  apply:(smooth_compact_exhaustion_monotone hK hVj); exact:(@hWK x (@hCW x hx)).
have[V [hV [hKV hOne]]]:=smooth_cutoff_neighbourhood_plateau (hChi j).
rewrite (hOmega j x (smooth_compact_in_domain C x hx)); exact:(@hOne x (@hKV x hXK)).
Qed.
