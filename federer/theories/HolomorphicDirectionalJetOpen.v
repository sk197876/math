(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(2),(5), pp. 326, 328:
    the original positive directional derivative test is
    open in the exact holomorphic germ metric. Actual jet
    continuity and bounded fixed-tuple evaluation prove the assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm HolomorphicGermFormsSealed Hom RealNormUP NormMetric ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm ContinuousMultilinearEvaluationBound NormBoundedLinearTopology
  HolomorphicGermUP HolomorphicGermJetsSealed HolomorphicGermMetric HolomorphicGermJetContinuity
  HolomorphicReductionLociUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_directional_jet_nonzero_open]: each
    fixed-order nonzero directional test defining B_j is
    open, supporting 3.4.8(5), p. 328. No
    unit-direction or lower-order vanishing hypothesis is used. *)
Theorem holomorphic_directional_jet_nonzero_open (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:is_complex_norm NX) (a:X) k (v:X):
  @open (@holomorphic_germ_metric R X NX (complex_norm_real hNX) a)
    [set alpha|@ContinuousMultilinear.evaluation R k (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_norm_real hNX)
      (@complex_modulus_real_norm R) [ffun _:'I_k=>v]
      (@HolomorphicGermJets.value R X NX (complex_norm_real hNX) a k alpha)<>0].
Proof.
pose N:=@complex_modulus R.
pose hN:=@complex_modulus_real_norm R.
pose M:=@holomorphic_germ_metric R X NX (complex_norm_real hNX) a.
pose Z:=@ContinuousMultilinear.space R k (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX N (complex_norm_real hNX) hN.
pose NZ:=@ContinuousMultilinear.norm R k (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX N (complex_norm_real hNX) hN.
pose ev:=@ContinuousMultilinear.evaluation R k (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX N (complex_norm_real hNX) hN.
pose hZ:=@ContinuousMultilinear.laws R k (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX N (complex_norm_real hNX) hN.
pose hNZ:=continuous_multilinear_norm_is_norm hN hZ.
pose F:=fun alpha:M=>(ev [ffun _:'I_k=>v]
  (@HolomorphicGermJets.value R X NX (complex_norm_real hNX) a k alpha):real_norm_metric_space hN).
have hEval:=@norm_bounded_linear_continuous R Z (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NZ N hNZ hN
  (ev [ffun _:'I_k=>v]) (continuous_multilinear_evaluation_bounded (complex_norm_real hNX) hZ [ffun _:'I_k=>v]).
have hF:continuous F.
  move=>alpha;exact:(continuous_comp (@holomorphic_germ_jet_continuous R X NX (complex_norm_real hNX) a k alpha)
    (hEval _)).
have hClosed:@closed (real_norm_metric_space hN) [set (0:ComplexScalars.C R)].
  apply:accessible_closed_set1;apply:hausdorff_accessible;exact:metric_hausdorff.
have hPre:@closed M (F @^-1` [set (0:ComplexScalars.C R)]).
  apply:(@preimage_closed M (real_norm_metric_space hN) F [set (0:ComplexScalars.C R)]);last exact:hClosed.
  by move=>alpha _;exact:hF alpha.
exact:(closed_openC hPre).
Qed.

(** Source for [holomorphic_positive_directional_jet_open]: the
    full original positive-order test in B_j is open,
    as used in 3.4.8(5), p. 328. All positive
    natural orders occur in the union. *)
Corollary holomorphic_positive_directional_jet_open (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:is_complex_norm NX) (v:X):
  @open (@holomorphic_germ_metric R X NX (complex_norm_real hNX) 0)
    [set alpha|has_nonzero_holomorphic_directional_jet hNX alpha v].
Proof.
have hSame:[set alpha:@holomorphic_germ_metric R X NX (complex_norm_real hNX) 0|
    has_nonzero_holomorphic_directional_jet hNX alpha v]=
    \bigcup_(k in [set k:nat|(0<k)%N])
      [set alpha:@holomorphic_germ_metric R X NX (complex_norm_real hNX) 0|
        @ContinuousMultilinear.evaluation R k (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_norm_real hNX)
          (@complex_modulus_real_norm R) [ffun _:'I_k=>v]
          (@HolomorphicGermJets.value R X NX (complex_norm_real hNX) 0 k alpha)<>0].
  apply/seteqP;split.
  - move=>alpha [k [hk hNonzero]];exists k;first exact:hk.
    have hTuple:[ffun i=>tnth [tuple v|_<k] i]=[ffun _:'I_k=>v]
      by apply/ffunP=>i;rewrite !ffunE tnth_mktuple.
    by move:hNonzero;rewrite (@HolomorphicGermForms.laws R X NX hNX 0 k) hTuple.
  - move=>alpha [k hk hNonzero];exists k;split;first exact:hk.
    rewrite (@HolomorphicGermForms.laws R X NX hNX 0 k).
    have hTuple:[ffun i=>tnth [tuple v|_<k] i]=[ffun _:'I_k=>v]
      by apply/ffunP=>i;rewrite !ffunE tnth_mktuple.
    by rewrite hTuple.
rewrite hSame;apply:bigcup_open=>k hk;exact:holomorphic_directional_jet_nonzero_open.
Qed.
