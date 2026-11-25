(** Federer (1969), 3.4.8(2),(5), pp. 326, 328:
    the original positive directional derivative test is
    open in the exact analytic germ metric. Actual jet
    continuity and bounded fixed-tuple evaluation prove the assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm ContinuousMultilinearEvaluationBound NormBoundedLinearTopology
  AnalyticGermUP AnalyticGermJetsSealed AnalyticGermMetric AnalyticGermJetContinuity
  AnalyticReductionLociUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_directional_jet_nonzero_open]: each
    fixed-order nonzero directional test defining B_j is
    open, supporting 3.4.8(5), p. 328. No
    unit-direction or lower-order vanishing hypothesis is used. *)
Theorem analytic_directional_jet_nonzero_open (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) k (v:X):
  @open (@analytic_germ_metric R X NX hNX a)
    [set alpha|@ContinuousMultilinear.evaluation R k X R^o NX (fun t=>`|t|) hNX
      (@scalar_absolute_value_norm R) [ffun _:'I_k=>v]
      (@AnalyticGermJets.value R X NX hNX a k alpha)<>0].
Proof.
pose N:=fun r:R^o=>`|r|.
pose hN:=@scalar_absolute_value_norm R.
pose M:=@analytic_germ_metric R X NX hNX a.
pose Z:=@ContinuousMultilinear.space R k X R^o NX N hNX hN.
pose NZ:=@ContinuousMultilinear.norm R k X R^o NX N hNX hN.
pose ev:=@ContinuousMultilinear.evaluation R k X R^o NX N hNX hN.
pose hZ:=@ContinuousMultilinear.laws R k X R^o NX N hNX hN.
pose hNZ:=continuous_multilinear_norm_is_norm hN hZ.
pose F:=fun alpha:M=>(ev [ffun _:'I_k=>v]
  (@AnalyticGermJets.value R X NX hNX a k alpha):real_norm_metric_space hN).
have hEval:=@norm_bounded_linear_continuous R Z R^o NZ N hNZ hN
  (ev [ffun _:'I_k=>v]) (continuous_multilinear_evaluation_bounded hNX hZ [ffun _:'I_k=>v]).
have hF:continuous F.
  move=>alpha;exact:(continuous_comp (@analytic_germ_jet_continuous R X NX hNX a k alpha)
    (hEval _)).
have hClosed:@closed (real_norm_metric_space hN) [set (0:R^o)].
  apply:accessible_closed_set1;apply:hausdorff_accessible;exact:metric_hausdorff.
have hPre:@closed M (F @^-1` [set (0:R^o)]).
  apply:(@preimage_closed M (real_norm_metric_space hN) F [set (0:R^o)]);last exact:hClosed.
  by move=>alpha _;exact:hF alpha.
exact:(closed_openC hPre).
Qed.

(** Source for [analytic_positive_directional_jet_open]: the
    full original positive-order test in B_j is open,
    as used in 3.4.8(5), p. 328. All positive
    natural orders occur in the union. *)
Corollary analytic_positive_directional_jet_open (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (v:X):
  @open (@analytic_germ_metric R X NX hNX 0)
    [set alpha|has_nonzero_analytic_directional_jet alpha v].
Proof.
have hSame:[set alpha:@analytic_germ_metric R X NX hNX 0|
    has_nonzero_analytic_directional_jet alpha v]=
    \bigcup_(k in [set k:nat|(0<k)%N])
      [set alpha:@analytic_germ_metric R X NX hNX 0|
        @ContinuousMultilinear.evaluation R k X R^o NX (fun t=>`|t|) hNX
          (@scalar_absolute_value_norm R) [ffun _:'I_k=>v]
          (@AnalyticGermJets.value R X NX hNX 0 k alpha)<>0].
  apply/seteqP;split.
  - move=>alpha [k [hk hNonzero]];by exists k.
  - move=>alpha [k hk hNonzero];exists k;by split.
rewrite hSame;apply:bigcup_open=>k hk;exact:analytic_directional_jet_nonzero_open.
Qed.
