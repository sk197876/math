(** Federer (1969), 4.1.12, p. 368: an
    original flat chain admits normal approximants with
    its original compact index and convergence on every
    original test. The previously proved finite flat
    action bound turns the defining approximation into
    the required testwise convergence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal lra ring.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentPointEvaluation SmoothCompactSet
  CurrentFlatNorm CurrentFlatFormSeminormLaws CurrentFlatDualSeminormBasic NormalCurrentsUP FlatCurrentsUP
  CurrentWeakSequenceLimit GeometricUniformTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FlatCurrentNormalWeakApproximation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set hNX U.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation F := (@current_flat_norm R h2 n m U hU K).
Local Notation f := (@current_flat_test_seminorm R h2 n m U hU K).
Local Notation hF := (@current_flat_test_is_seminorm R h2 n m U hU K).
Local Notation normalK := (@normal_currents_supported_in R h2 n U hU m K).

(** Source for [flat_current_normal_weak_approximation]:
    every original F_(m,K) chain has normal approximants
    in K with F_K(T-u_k)<2^(-k) and convergence on
    every original test, supporting the closure comparison
    and series arguments of Federer 4.1.12, p. 368.
    No measure representation is imposed on the limit. *)
Theorem flat_current_normal_weak_approximation (T:C):
  @is_flat_current_supported_in R h2 n m U hU K T->
  exists u:nat->C,
    (forall k,normalK (u k)) /\
    (forall k,(F ((T-u k)%R)<((1/2:R)^+k)%:E)%E) /\
    @is_current_weak_sequence_limit R h2 n m U hU u T.
Proof.
move=>hFlat.
pose q:R:=1/2.
have hq:0<q<1 by rewrite /q;apply/andP;split;lra.
have hApproximant k:exists Q:C,normalK Q /\(F ((T-Q)%R)<(q^+k)%:E)%E.
  exact:(hFlat (q^+k) (exprn_gt0 k (andP hq).1)).
have[u hu]:=choice hApproximant.
exists u;split;first by move=>k;exact:(hu k).1.
split;first by move=>k;exact:(hu k).2.
move=>phi epsilon hEpsilon.
have hPhi:0<=f phi:=real_seminorm_nonnegative hF phi.
have[k hk]:=@geometric_uniform_tail R q (f phi) epsilon hq hPhi hEpsilon.
exists k=>L hKL.
have hFinite:(F ((T-u L)%R)< +oo)%E:=lt_trans (hu L).2 (ltry _).
have[c [hc hValue]]:=@current_flat_dual_finite_value R h2 n m U hU K
  (action (T-u L)) hFinite.
have hReal:c<q^+L by move:(hu L).2;rewrite /current_flat_norm hValue lte_fin.
have hBound:=@current_flat_dual_finite_bound R h2 n m U hU K (action (T-u L)) c hValue phi.
pose E:=@current_point_evaluation R h2 n m U hU phi.
have hDifference:action (u L) phi-action T phi= -action (T-u L) phi.
  change (E (u L)-E T= -E (T-u L)).
  rewrite (linB (hom_linear E));ring.
rewrite hDifference normrN.
apply:(le_lt_trans hBound).
exact:(le_lt_trans (ler_wpM2r hPhi (ltW hReal)) (hk L hKL)).
Qed.
End FlatCurrentNormalWeakApproximation.
