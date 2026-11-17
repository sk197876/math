(** Supporting Federer (1969), 3.4.8(5), p. 328:
    a germ in the metric closure of an original
    ideal agrees to every prescribed finite order
    with a member of that same ideal. The proof
    uses actual finite-jet continuity and the proved
    closed finite-dimensional ideal image. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric LinearBasis AnalyticGermRing
  AnalyticGermMetric AnalyticGermJetsSealed CommutativeIdealUP AnalyticFiniteJetsUP
  AnalyticFiniteJetsSealed AnalyticFiniteJetsLaws AnalyticFiniteJetsContinuity
  AnalyticFiniteJetIdealClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_ideal_closure_finite_jet_agreement]:
    exact finite derivative agreement with an original
    ideal member, supporting the expanded ideal-closedness
    proof for 3.4.8(5), p. 328, in the
    original metric of 3.4.5, p. 319. Neither
    finite-jet agreement nor adic approximation is assumed. *)
Theorem analytic_ideal_closure_finite_jet_agreement (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) n (b:'I_n->X) (hb:is_basis b) a
  (I:set (@analytic_germ_ring R X NX hNX a)) (hI:is_commutative_ideal I)
  (alpha:@analytic_germ_ring R X NX hNX a):
  @closure (@analytic_germ_metric R X NX hNX a) I alpha ->
  forall m,exists beta,I beta /\forall i,(i<m)%N ->
    @AnalyticGermJets.value R X NX hNX a i alpha = @AnalyticGermJets.value R X NX hNX a i beta.
Proof.
move=>hAlpha m.
pose M:=@analytic_germ_metric R X NX hNX a.
pose T:=real_norm_metric_space (@analytic_finite_jet_norm_laws R X NX hNX m).
pose f:=fun beta:M=>(@AnalyticFiniteJets.map R X NX hNX m a beta:T).
have hF:continuous f:=@analytic_finite_jet_map_continuous R X NX hNX m a.
have hImage:@closed T (f @` I):=@analytic_finite_jet_ideal_image_closed R X NX hNX n b hb m a I hI.
have hPre:@closed M (f @^-1` (f @` I)).
  apply:preimage_closed;last exact:hImage.
  move=>beta _;exact:hF beta.
have hContains:I `<=` f @^-1` (f @` I).
  move=>beta hBeta;exists beta=>//.
have hMembership:(f @` I) (f alpha).
  apply:hPre;exact:(@closureS M I (f @^-1` (f @` I)) hContains alpha hAlpha).
have [beta hBeta hEqual]:=hMembership.
exists beta;split=>//.
exact:(@analytic_finite_jet_equality R X NX hNX m a alpha beta).1 (esym hEqual).
Qed.
