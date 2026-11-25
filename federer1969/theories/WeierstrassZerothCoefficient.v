(** Federer (1969), 3.4.6(2), p. 322: the
    actual zeroth mixed coefficient is the original value
    of every analytic representative at the origin. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearZero NormHigherDifferentialUP AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermJetsSealed WeierstrassCoefficientUP WeierstrassAxisCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_zeroth_coefficient_value]:
    the coefficient Q_(0,0) is Q(0), as used to prove
    Q(0) is nonzero in 3.4.6(2), p. 322.
    Every original representative gives the same value. *)
Lemma weierstrass_zeroth_coefficient_value (R:realType) (X K:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (alpha:analytic_germ_space hNX (0:X))
    (v:X) (inclusion:Hom K X) (C:K->R)
    (f:analytic_representative_type hNX (0:X)):
  is_weierstrass_split_coefficient alpha v inclusion 0%N 0%N C ->analytic_germ f=alpha ->
  forall z,C z=analytic_representative_value f 0.
Proof.
move=>hC hRep z.
rewrite (weierstrass_axis_coefficient_value hC z) /= invr1 mul1r.
have hEmpty:[ffun _:'I_0=>v]=[ffun _:'I_0=>(0:X)]:=zero_arity_arguments_unique _ _.
rewrite hEmpty.
exact:(@AnalyticGermJets.laws R X NX hNX 0 0%N alpha f hRep).2.
Qed.
