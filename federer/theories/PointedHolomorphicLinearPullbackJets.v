(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(5), p. 328:
    the actual germ derivative transforms by applying the
    original linear map in every argument. Actual linewise
    Taylor comparison and polarization prove the full rule. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicLinear Hom RealNormUP TensorFamilyUP FamilyUpdate
  ContinuousMultilinearUP ContinuousMultilinearSealed FiniteArgumentPermutation
  HolomorphicGermUP HolomorphicGermJetsSealed HolomorphicGermJetSymmetry
  PointedHolomorphicPullbackUP PointedHolomorphicLinearPullbackDiagonal
  SymmetricMultilinearDiagonalExtensional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [pointed_holomorphic_linear_pullback_jets]: the
    actual full derivative transformation used in the joint
    pullback continuity of 3.4.8(5), p. 328.
    Every derivative order and every actual argument tuple
    remain; the action on derivatives is a conclusion. *)
Theorem pointed_holomorphic_linear_pullback_jets
    (R:realType) (X Y:lmodType (ComplexScalars.C R)) (NX:X->R) (NY:Y->R)
    (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY) (a:X) (b:Y)
    (L:Hom X Y) (P:holomorphic_germ_space hNY b->holomorphic_germ_space hNX a):
  is_pointed_holomorphic_germ_pullback L P ->L a=b ->
  forall k (alpha:holomorphic_germ_space hNY b) (u:{ffun 'I_k->restricted_space (ComplexScalars.embed R) X}),
    @ContinuousMultilinear.evaluation R k (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX
      (@complex_modulus_real_norm R) u
      (@HolomorphicGermJets.value R X NX hNX a k (P alpha))=
    @ContinuousMultilinear.evaluation R k (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NY (@complex_modulus R) hNY
      (@complex_modulus_real_norm R) [ffun i=>L (u i)]
      (@HolomorphicGermJets.value R Y NY hNY b k alpha).
Proof.
move=>hP hab k alpha u.
pose N:=@complex_modulus R.
pose hN:=@complex_modulus_real_norm R.
pose ez:=@ContinuousMultilinear.evaluation R k (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX N hNX hN.
pose ew:=@ContinuousMultilinear.evaluation R k (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NY N hNY hN.
pose z:=@HolomorphicGermJets.value R X NX hNX a k (P alpha).
pose w:=@HolomorphicGermJets.value R Y NY hNY b k alpha.
pose f:=fun v:{ffun 'I_k->restricted_space (ComplexScalars.embed R) X}=>ez v z.
pose g:=fun v:{ffun 'I_k->restricted_space (ComplexScalars.embed R) X}=>ew [ffun i=>L (v i)] w.
have hF:multilinear f:=continuous_multilinear_evaluation
  (@ContinuousMultilinear.laws R k (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX N hNX hN) z.
have hG:multilinear g.
  change (multilinear (fun v:{ffun 'I_k->restricted_space (ComplexScalars.embed R) X}=>ew (family_map (fun _:'I_k=>complex_hom_real L) v) w)).
  move=>v i c x y;rewrite !family_map_with (linearP (complex_hom_real L)) /=.
  exact:(continuous_multilinear_evaluation (@ContinuousMultilinear.laws R k (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NY N hNY hN) w).
have hFS s v:f (finite_argument_permutation s v)=f v.
  exact:(@holomorphic_germ_jet_symmetric R X NX hNX a k (P alpha) s v).
have hGS s v:g (finite_argument_permutation s v)=g v.
  have hArgs:[ffun i=>L (finite_argument_permutation s v i)]=
      finite_argument_permutation s [ffun i=>L (v i)].
    by apply/ffunP=>i;rewrite /finite_argument_permutation !ffunE.
  rewrite /g hArgs.
  exact:(@holomorphic_germ_jet_symmetric R Y NY hNY b k alpha s _).
have hDiagonal x:f [ffun _:'I_k=>x]=g [ffun _:'I_k=>x].
  have hArgs:[ffun i=>L ([ffun _:'I_k=>x] i)]=[ffun _:'I_k=>L x].
    by apply/ffunP=>i;rewrite !ffunE.
  rewrite /g hArgs.
  exact:(@pointed_holomorphic_linear_pullback_diagonal R X Y NX NY hNX hNY a b L P hP hab k alpha x).
exact:(@symmetric_multilinear_diagonal_extensional R k (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) f g hF hG hFS hGS hDiagonal u).
Qed.
