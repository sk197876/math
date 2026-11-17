(** Federer (1969), 3.4.12, p. 339, extending 3.4.5,
    p. 319: every original holomorphic germ growth class is
    compact in finite complex source dimension. Use the proved
    compact coefficient set, actual realisation and the original
    derivative metric's finite-coordinate control. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology fingroup perm.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm
  NormMetric LinearBasis ComplexOrderedBases ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  MultilinearFamilyAlgebra FiniteArgumentPermutation HolomorphicGermUP HolomorphicGermOperationsUP
  HolomorphicGermTaylorInjective HolomorphicGermJetsSealed HolomorphicGermJetsComplex HolomorphicGermJetSymmetry
  HolomorphicGermMetric HolomorphicGermGrowthUP HolomorphicGermGrowthSealed HolomorphicFormalJetUP
  HolomorphicFormalJetRealisation HolomorphicJetCoefficientCompact JetSequenceMetricUP JetMetricFiniteControl.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Compactness.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Local Notation C:=(ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation NC:=(@complex_modulus R).
Local Notation hNC:=(@complex_modulus_real_norm R).

(** Source for [holomorphic_germ_growth_class_compact]: the original
    all-order growth classes are compact, extending 3.4.5,
    p. 319. Dimension zero and zero growth indices remain;
    every realised germ has exactly the prescribed original jets. *)
Theorem holomorphic_germ_growth_class_compact a n (b:'I_n->X) (hb:is_basis b) s t:
  @compact (@holomorphic_germ_metric R X NX hNXR a)
    (@HolomorphicGermGrowth.value R X NX hNXR a s t).
Proof.
pose Z i:=@ContinuousMultilinear.space R i XR CR NX NC hNXR hNC.
pose ev i:=@ContinuousMultilinear.evaluation R i XR CR NX NC hNXR hNC.
pose N i:=@ContinuousMultilinear.norm R i XR CR NX NC hNXR hNC.
pose hN i:=continuous_multilinear_norm_is_norm hNC
  (@ContinuousMultilinear.laws R i XR CR NX NC hNXR hNC).
pose T i:=Topological.clone (real_norm_metric_space (hN i)) _.
pose P:=prod_topology T.
pose M:=@holomorphic_germ_metric R X NX hNXR a.
pose jet:=@HolomorphicGermJets.value R X NX hNXR a.
pose d:=@holomorphic_germ_distance R X NX hNXR a.
have hd:=@holomorphic_germ_distance_formula R X NX hNXR a.
pose K:set P:=fun w=>@is_holomorphic_formal_jet R X NX hNX s t w.
have hK:compact K:=@bounded_holomorphic_jet_coefficients_compact R X NX hNX
  (n+n)%N (@ordered_real_basis R X n b) (@ordered_real_basisP R X n b hb) s t.
have hex w:K w ->exists alpha:M,forall i,jet i alpha=w i.
  exact:(@holomorphic_formal_jet_realisation R X NX hNX a s t w).
pose pick (w:P):M:=if pselect (K w) is left h then projT1 (cid (hex w h))
  else @holomorphic_germ_zero R X NX hNXR a.
have hp w (hw:K w):forall i,jet i (pick w)=w i.
  rewrite /pick;case:pselect=>[h|h];last by exfalso;exact:h hw.
  exact:(projT2 (cid (hex w h))).
have hContinuous:{within K,continuous pick}.
  apply/subspace_continuousP=>w hw U hU.
  have [epsilon hEpsilon hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP (pick w) U) hU.
  have [k [delta [hDelta hControl]]]:=@jet_metric_finite_coordinate_control R
    (holomorphic_germ_space hNXR a) Z N hN jet d hd epsilon hEpsilon.
  have hNear (i:'I_k):nbhs w [set v:P|N i (w i-v i)<delta].
    have hBallN:nbhs (w i:T i) [set z:T i|N i (w i-z)<delta].
      apply:(proj2 (metricType_numDomainType.nbhs_mdistP (w i:T i) _)).
      exists delta;first exact:hDelta.
      by move=>z hz.
    exact:(@proj_continuous _ T i w _ hBallN).
  have hAll:=@filter_forall P (Finite.clone 'I_k _) _ (nbhs w) (nbhs_filter w) hNear.
  change (nbhs w [set v:P|K v ->U (pick v)]).
  apply:filterS hAll=>v hv hKv;apply:hBall.
  change (is_true (d (pick w) (pick v)<epsilon)).
  apply:hControl=>i hi;rewrite (hp w hw) (hp v hKv);exact:(hv (Ordinal hi)).
have hClasses:=@HolomorphicGermGrowth.laws R X NX hNXR a s t.
have hImage:pick @` K=(@HolomorphicGermGrowth.value R X NX hNXR a s t:set M).
  apply/seteqP;split.
  - move=>alpha [w hw <-];apply/(holomorphic_germ_growth_membership hClasses _)=>i.
    change (is_true (N i (jet i (pick w))<=s%:R*t%:R^+i*(i`!)%:R)).
    rewrite (hp w hw);exact:(@holomorphic_formal_jet_growth R X NX hNX s t w hw i).
  - move=>alpha hAlpha.
    pose w:P:=fun i=>jet i alpha.
    have hw:K w.
      constructor.
      + move=>i sigma u;exact:(@holomorphic_germ_jet_symmetric R X NX hNXR a i alpha sigma u).
      + exact:((holomorphic_germ_growth_membership hClasses alpha).1 hAlpha).
      + move=>i u j c x;exact:(@multilinear_family_scale C i (fun _=>X) C^o
          (fun v=>ev i v (w i)) (@holomorphic_germ_jet_complex R X NX hNX a alpha i) u j c x).
    exists w;first exact:hw.
    apply:(@holomorphic_germ_jets_injective R X NX hNXR a)=>i.
    exact:(hp w hw i).
rewrite -hImage;exact:(continuous_compact hContinuous hK).
Qed.
End Compactness.
