(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(5), p. 328:
    a germ in the metric closure of an original
    ideal agrees to every prescribed finite order
    with a member of that same ideal. The proof
    uses actual finite-jet continuity and the proved
    closed finite-dimensional ideal image. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm RealNormUP NormMetric LinearBasis HolomorphicGermRing
  HolomorphicGermMetric HolomorphicGermJetsSealed CommutativeIdealUP HolomorphicFiniteJetsUP
  HolomorphicFiniteJetsSealed HolomorphicFiniteJetsLaws HolomorphicFiniteJetsContinuity
  HolomorphicFiniteJetIdealClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_ideal_closure_finite_jet_agreement]:
    exact finite derivative agreement with an original
    ideal member, supporting the expanded ideal-closedness
    proof for 3.4.8(5), p. 328, in the
    original metric of 3.4.5, p. 319. Neither
    finite-jet agreement nor adic approximation is assumed. *)
Theorem holomorphic_ideal_closure_finite_jet_agreement (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:is_complex_norm NX) n (b:'I_n->(restricted_space (ComplexScalars.embed R) X)) (hb:is_basis b) a
  (I:set (@holomorphic_germ_ring R X NX (complex_norm_real hNX) a)) (hI:is_commutative_ideal I)
  (alpha:@holomorphic_germ_ring R X NX (complex_norm_real hNX) a):
  @closure (@holomorphic_germ_metric R X NX (complex_norm_real hNX) a) I alpha ->
  forall m,exists beta,I beta /\forall i,(i<m)%N ->
    @HolomorphicGermJets.value R X NX (complex_norm_real hNX) a i alpha = @HolomorphicGermJets.value R X NX (complex_norm_real hNX) a i beta.
Proof.
move=>hAlpha m.
pose M:=@holomorphic_germ_metric R X NX (complex_norm_real hNX) a.
pose T:=real_norm_metric_space (@holomorphic_finite_jet_norm_laws R X NX hNX m).
pose f:=fun beta:M=>(@HolomorphicFiniteJets.map R X NX hNX m a beta:T).
have hF:continuous f:=@holomorphic_finite_jet_map_continuous R X NX hNX m a.
have hImage:@closed T (f @` I):=@holomorphic_finite_jet_ideal_image_closed R X NX hNX n b hb m a I hI.
have hPre:@closed M (f @^-1` (f @` I)).
  apply:preimage_closed;last exact:hImage.
  move=>beta _;exact:hF beta.
have hContains:I `<=` f @^-1` (f @` I).
  move=>beta hBeta;exists beta=>//.
have hMembership:(f @` I) (f alpha).
  apply:hPre;exact:(@closureS M I (f @^-1` (f @` I)) hContains alpha hAlpha).
have [beta hBeta hEqual]:=hMembership.
exists beta;split=>//.
exact:(@holomorphic_finite_jet_equality R X NX hNX m a alpha beta).1 (esym hEqual).
Qed.
