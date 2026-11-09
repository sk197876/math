(** Federer (1969), 3.4.5, p. 319: finitely
    many actual derivative differences are small throughout
    a neighbourhood for the original germ metric. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  AnalyticGermUP AnalyticGermRing AnalyticGermMetric AnalyticGermJetsSealed AnalyticGermGrowthUP
  AnalyticGermJetContinuity AnalyticGermJetDifference.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_finite_coordinate_neighbourhood]:
    finite-coordinate neighbourhoods for the original derivative
    metric in 3.4.5, p. 319. Every coordinate
    difference uses the actual germ-ring subtraction. *)
Theorem analytic_germ_finite_coordinate_neighbourhood (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) m
    (alpha0:@analytic_germ_metric R X NX hNX a) (delta:R):
  0<delta ->nbhs alpha0
    [set alpha:@analytic_germ_metric R X NX hNX a|
      forall i,(i<=m)%N ->@analytic_germ_jet_norm R X NX hNX a i
        ((alpha:[the comNzRingType of (@analytic_germ_ring R X NX hNX a)])-(alpha0:[the comNzRingType of (@analytic_germ_ring R X NX hNX a)]))<delta].
Proof.
move=>hDelta.
pose M:=@analytic_germ_metric R X NX hNX a.
pose N i:=@ContinuousMultilinear.norm R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R).
pose hN i:=continuous_multilinear_norm_is_norm (@scalar_absolute_value_norm R)
  (@ContinuousMultilinear.laws R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)).
pose jet:=@AnalyticGermJets.value R X NX hNX a.
have hNear (i:'I_m.+1):nbhs alpha0 [set alpha:M|
    @analytic_germ_jet_norm R X NX hNX a i
      ((alpha:[the comNzRingType of (@analytic_germ_ring R X NX hNX a)])-(alpha0:[the comNzRingType of (@analytic_germ_ring R X NX hNX a)]))<delta].
  have hBall:nbhs (jet i alpha0:real_norm_metric_space (hN i))
      [set z:real_norm_metric_space (hN i)|N i (z-jet i alpha0)<delta].
    apply:(proj2 (metricType_numDomainType.nbhs_mdistP (jet i alpha0:real_norm_metric_space (hN i)) _)).
    exists delta;first exact:hDelta.
    move=>z hz.
    change (is_true (N i (jet i alpha0-z)<delta)) in hz.
    change (is_true (N i (z-jet i alpha0)<delta)).
    rewrite /N (real_seminorm_subtract (hN i).1);exact:hz.
  have hh:=@analytic_germ_jet_continuous R X NX hNX a i alpha0 _ hBall.
  change (nbhs alpha0 (fun alpha:M=>N i (jet i alpha-jet i alpha0)<delta)) in hh.
  apply:filterS hh=>alpha hAlpha.
  change (is_true (N i (jet i ((alpha:[the comNzRingType of (@analytic_germ_ring R X NX hNX a)])-(alpha0:[the comNzRingType of (@analytic_germ_ring R X NX hNX a)])))<delta)).
  have hDifference:=@analytic_germ_jet_difference R X NX hNX a i alpha alpha0.
  rewrite /jet hDifference;exact:hAlpha.
have hAll:=@filter_forall M (Finite.clone 'I_m.+1 _) _ (nbhs alpha0) (nbhs_filter alpha0) hNear.
apply:filterS hAll=>alpha hAlpha i hi.
have hi':(i<m.+1)%N by rewrite ltnS.
exact:hAlpha (Ordinal hi').
Qed.
