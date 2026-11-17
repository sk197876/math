(** Supporting Federer (1969), 3.4.8(5), p. 328:
    the actual finite derivative prefix is continuous
    for the original germ metric. The proof uses
    each actual derivative's continuity from 3.4.5,
    p. 319, and the abstract finite-product topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormedFamilyUP NormedFamilySealed
  NormedFamilyContinuousAssembly ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm AnalyticGermRing AnalyticGermMetric AnalyticGermJetsSealed AnalyticGermJetContinuity
  AnalyticFiniteJetsUP AnalyticFiniteJetsSealed AnalyticFiniteJetsLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [analytic_finite_jet_map_continuous]: the
    finite-prefix map for the actual metric of
    3.4.5, p. 319, is continuous, supporting the
    expanded ideal-closedness proof for 3.4.8(5), p. 328. *)
Theorem analytic_finite_jet_map_continuous (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) m a:
  continuous (fun alpha:@analytic_germ_metric R X NX hNX a=>
    (@AnalyticFiniteJets.map R X NX hNX m a alpha:
      real_norm_metric_space (@analytic_finite_jet_norm_laws R X NX hNX m))).
Proof.
pose Z:=fun i:'I_m=>@ContinuousMultilinear.space R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R).
pose N:=fun i:'I_m=>@ContinuousMultilinear.norm R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R).
pose hN:=fun i:'I_m=>continuous_multilinear_norm_is_norm (@scalar_absolute_value_norm R)
  (@ContinuousMultilinear.laws R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)).
apply:(@normed_family_continuous_assembly R m Z N hN
  (@analytic_finite_jet_space R X NX hNX m)
  (@analytic_finite_jet_coordinate R X NX hNX m)
  (@analytic_finite_jet_norm R X NX hNX m)
  (@NormedFamily.laws R m Z N)
  [the topologicalType of (@analytic_germ_metric R X NX hNX a)]
  (@AnalyticFiniteJets.map R X NX hNX m a))=>i.
have hEquation:(fun alpha:@analytic_germ_metric R X NX hNX a=>
    @analytic_finite_jet_coordinate R X NX hNX m i (@AnalyticFiniteJets.map R X NX hNX m a alpha)) =
    (fun alpha:@analytic_germ_metric R X NX hNX a=>@AnalyticGermJets.value R X NX hNX a i alpha).
  apply:funext=>alpha;exact:(@AnalyticFiniteJets.laws R X NX hNX m a alpha i).
rewrite hEquation;exact:(@analytic_germ_jet_continuous R X NX hNX a i).
Qed.
