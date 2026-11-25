(** Federer (1969), 4.1.12, pp. 367–369: flat
    convergence implies convergence on every original
    test. This supporting estimate uses the exact
    finite dual bound, not a different test topology
    or an imposed representation of the current. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentPointEvaluation SmoothCompactSet
  CurrentFlatNorm CurrentFlatFormSeminormLaws CurrentFlatDualSeminormBasic FlatCurrentSpaces
  NormSequenceConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FlatCurrentConvergenceEvaluation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:X->Prop.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation W := (@flat_current_space R h2 n m U hU K).
Local Notation N := (@flat_current_norm R h2 n m U hU K).
Local Notation hN := (@flat_current_norm_is_norm R h2 n m U hU K).
Local Notation inc := (@flat_current_inclusion R h2 n m U hU K).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation Flat := (@current_flat_test_seminorm R h2 n m U hU K).

(** Source for [flat_current_convergence_evaluation]:
    convergence in the original F_K norm gives
    convergence of T_N(phi) for every actual test phi,
    supporting both series in Federer 4.1.12,
    pp. 368–369, by the dual bound on p. 367. *)
Theorem flat_current_convergence_evaluation (u:nat->W) z:
  ((fun k=>(u k:real_norm_metric_space hN)) @ \oo -->
    (z:real_norm_metric_space hN))->
  forall phi:DT,forall epsilon:R,0<epsilon->exists k,forall M,(k<=M)%N->
    `|action (inc (u M)) phi-action (inc z) phi|<epsilon.
Proof.
move=>hConvergence phi epsilon hEpsilon.
pose b:=Flat phi.
have hb:0<=b:=real_seminorm_nonnegative (@current_flat_test_is_seminorm R h2 n m U hU K) phi.
have hDenominator:0<b+1 by lra.
pose delta:=epsilon/(b+1).
have hDelta:0<delta by rewrite /delta divr_gt0.
have [k hk]:=(@norm_sequence_convergence_epsilon R W N hN u z).1 hConvergence delta hDelta.
exists k=>M hKM.
have hNormSmall:=hk M hKM.
have hValue:=@flat_current_norm_value R h2 n m U hU K (u M-z).
have hAction:=@current_flat_dual_finite_bound R h2 n m U hU K
  (action (inc (u M-z))) (N (u M-z)) hValue phi.
pose E:=@current_point_evaluation R h2 n m U hU phi.
have hDifference:action (inc (u M-z)) phi=action (inc (u M)) phi-action (inc z) phi.
  change (E (inc (u M-z))=E (inc (u M))-E (inc z)).
  by rewrite (linB (hom_linear inc)) (linB (hom_linear E)).
rewrite hDifference [N (u M-z)*Flat phi]mulrC in hAction.
apply:(le_lt_trans hAction).
have hFirst:=ler_wpM2l hb (ltW hNormSmall).
have hStrict:b * delta<(b+1) * delta.
  rewrite (ltr_pM2r hDelta);lra.
have hEndpoint:(b+1) * delta=epsilon.
  by rewrite /delta mulrC divfK ?gt_eqF.
rewrite hEndpoint in hStrict;exact:le_lt_trans hFirst hStrict.
Qed.
End FlatCurrentConvergenceEvaluation.
