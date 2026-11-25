(** Federer (1969), 3.4.5, p. 319: the zeroth
    derivative of a germ is the value of any original
    representative at its centre. Its norm is the absolute value. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearZero NormHigherDifferentialUP AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermJetsUP AnalyticGermJetsSealed AnalyticGermGrowthUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [analytic_germ_zeroth_norm]: the m=0
    term of the original germ metric, 3.4.5, p. 319,
    retains the actual function value. *)
Lemma analytic_germ_zeroth_norm (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (alpha:analytic_germ_space hNX a) (f:@analytic_representative_type R X NX hNX a):
  analytic_germ f=alpha ->@analytic_germ_jet_norm R X NX hNX a 0%N alpha=
    `|analytic_representative_value f a|.
Proof.
move=>hf.
have hActual:=@AnalyticGermJets.laws R X NX hNX a 0%N alpha f hf.
rewrite /analytic_germ_jet_norm
  (continuous_multilinear_zero_norm (@scalar_absolute_value_norm R)
    (@ContinuousMultilinear.laws R 0%N X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R))).
by rewrite hActual.2.
Qed.
