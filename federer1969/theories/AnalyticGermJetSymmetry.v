(** Federer (1969), 3.4.5, p. 319: actual
    germ derivatives are symmetric coefficients, by 3.1.11,
    p. 220. This supplies the reverse inclusion in the
    coefficient description of each growth class. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals fingroup perm.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialSymmetry FiniteArgumentPermutation
  AnalyticGermUP AnalyticGermRingLaws AnalyticGermJetsUP AnalyticGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_germ_jet_symmetric]: each actual
    D^m(alpha) has the original permutation symmetry, as
    required for compactness in 3.4.5, p. 319. *)
Lemma analytic_germ_jet_symmetric (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) m (alpha:analytic_germ_space hNX a)
    (sigma:'S_m) (u:{ffun 'I_m->X}):
  @ContinuousMultilinear.evaluation R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)
    (finite_argument_permutation sigma u) (@AnalyticGermJets.value R X NX hNX a m alpha)=
  @ContinuousMultilinear.evaluation R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)
    u (@AnalyticGermJets.value R X NX hNX a m alpha).
Proof.
have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
exact:(@norm_higher_differential_symmetric R X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)
  (fun i=>@ContinuousMultilinear.space R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R))
  (fun i=>@ContinuousMultilinear.evaluation R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R))
  (fun i=>@ContinuousMultilinear.norm R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R))
  (fun i=>@ContinuousMultilinear.laws R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R))
  setT _ m a _ (@AnalyticGermJets.laws R X NX hNX a m alpha f hf) sigma u).
Qed.
