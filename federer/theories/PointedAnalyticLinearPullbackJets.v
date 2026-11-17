(** Federer (1969), 3.4.8(5), p. 328:
    the actual germ derivative transforms by applying the
    original linear map in every argument. Actual linewise
    Taylor comparison and polarization prove the full rule. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP TensorFamilyUP FamilyUpdate
  ContinuousMultilinearUP ContinuousMultilinearSealed FiniteArgumentPermutation
  AnalyticGermUP AnalyticGermJetsSealed AnalyticGermJetSymmetry
  PointedAnalyticPullbackUP PointedAnalyticLinearPullbackDiagonal
  SymmetricMultilinearDiagonalExtensional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [pointed_analytic_linear_pullback_jets]: the
    actual full derivative transformation used in the joint
    pullback continuity of 3.4.8(5), p. 328.
    Every derivative order and every actual argument tuple
    remain; the action on derivatives is a conclusion. *)
Theorem pointed_analytic_linear_pullback_jets
    (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (a:X) (b:Y)
    (L:Hom X Y) (P:analytic_germ_space hNY b->analytic_germ_space hNX a):
  is_pointed_analytic_germ_pullback L P ->L a=b ->
  forall k (alpha:analytic_germ_space hNY b) (u:{ffun 'I_k->X}),
    @ContinuousMultilinear.evaluation R k X R^o NX (fun t=>`|t|) hNX
      (@scalar_absolute_value_norm R) u
      (@AnalyticGermJets.value R X NX hNX a k (P alpha))=
    @ContinuousMultilinear.evaluation R k Y R^o NY (fun t=>`|t|) hNY
      (@scalar_absolute_value_norm R) [ffun i=>L (u i)]
      (@AnalyticGermJets.value R Y NY hNY b k alpha).
Proof.
move=>hP hab k alpha u.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose ez:=@ContinuousMultilinear.evaluation R k X R^o NX N hNX hN.
pose ew:=@ContinuousMultilinear.evaluation R k Y R^o NY N hNY hN.
pose z:=@AnalyticGermJets.value R X NX hNX a k (P alpha).
pose w:=@AnalyticGermJets.value R Y NY hNY b k alpha.
pose f:=fun v:{ffun 'I_k->X}=>ez v z.
pose g:=fun v:{ffun 'I_k->X}=>ew [ffun i=>L (v i)] w.
have hF:multilinear f:=continuous_multilinear_evaluation
  (@ContinuousMultilinear.laws R k X R^o NX N hNX hN) z.
have hG:multilinear g.
  change (multilinear (fun v:{ffun 'I_k->X}=>ew (family_map (fun _:'I_k=>L) v) w)).
  move=>v i c x y;rewrite !family_map_with linearP /=.
  exact:(continuous_multilinear_evaluation (@ContinuousMultilinear.laws R k Y R^o NY N hNY hN) w).
have hFS s v:f (finite_argument_permutation s v)=f v.
  exact:(@analytic_germ_jet_symmetric R X NX hNX a k (P alpha) s v).
have hGS s v:g (finite_argument_permutation s v)=g v.
  have hArgs:[ffun i=>L (finite_argument_permutation s v i)]=
      finite_argument_permutation s [ffun i=>L (v i)].
    by apply/ffunP=>i;rewrite /finite_argument_permutation !ffunE.
  rewrite /g hArgs.
  exact:(@analytic_germ_jet_symmetric R Y NY hNY b k alpha s _).
have hDiagonal x:f [ffun _:'I_k=>x]=g [ffun _:'I_k=>x].
  have hArgs:[ffun i=>L ([ffun _:'I_k=>x] i)]=[ffun _:'I_k=>L x].
    by apply/ffunP=>i;rewrite !ffunE.
  rewrite /g hArgs.
  exact:(@pointed_analytic_linear_pullback_diagonal R X Y NX NY hNX hNY a b L P hP hab k alpha x).
exact:(@symmetric_multilinear_diagonal_extensional R k X R^o f g hF hG hFS hGS hDiagonal u).
Qed.
