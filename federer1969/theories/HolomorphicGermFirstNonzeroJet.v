(** Federer (1969), 3.4.12, p. 339, extending 3.4.7, pp. 324–325:
    a nonzero analytic germ has a finite first nonzero
    derivative. Actual Taylor injectivity proves this assertion;
    an order or a regular direction is not supplied
    as an extra hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  HolomorphicGermUP HolomorphicGermOperationsUP HolomorphicGermJetsSealed HolomorphicGermJetZeroNegate HolomorphicGermTaylorInjective.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_germ_first_nonzero_jet]: the
    finite infimum of nonzero derivative orders in 3.4.7,
    p. 324. The order may be zero when
    the germ has nonzero value at its centre. *)
Theorem holomorphic_germ_first_nonzero_jet (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a
    (alpha:holomorphic_germ_space hNX a):
  alpha<>@holomorphic_germ_zero R X NX hNX a ->
  exists k,
    @HolomorphicGermJets.value R X NX hNX a k alpha<>0 /\
    forall i,(i<k)%N ->@HolomorphicGermJets.value R X NX hNX a i alpha = 0.
Proof.
move=>hAlpha.
pose jet:=@HolomorphicGermJets.value R X NX hNX a.
have hExists:exists m,jet m alpha!=0.
  apply:contrapT=>hNo;apply:hAlpha.
  apply:(@holomorphic_germ_jets_injective R X NX hNX a)=>m.
  rewrite holomorphic_germ_jet_zero.
  case:(eqVneq (jet m alpha) 0)=>[h|h];first exact:h.
  exfalso;apply:hNo;by exists m.
have [k hk hMinimal]:=ex_minnP hExists.
exists k;split;first exact/eqP.
move=>i hi;case:(eqVneq (jet i alpha) 0)=>[h|h];first exact:h.
have hki:=hMinimal i h.
have hContradiction:=leq_ltn_trans hki hi.
by rewrite ltnn in hContradiction.
Qed.
