(** Federer (1969), 3.4.6, pp. 322–323: the
    actual mixed divided Taylor coefficients on the original
    transverse space. Their defining equations precede existence. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP SymmetricForms PolynomialTaylorTerms HomogeneousPolynomialFunctions
  ContinuousMultilinearUP ContinuousMultilinearSealed AnalyticGermUP AnalyticGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_weierstrass_split_coefficient]: the original
    coefficient f_(i,j) is the actual (i+j)th derivative
    contracted with v^i/i! and the included z^j/j!,
    3.4.6, p. 322. The contraction operation is
    the one already specified in 1.10.4, p. 46.
    This law applies to every actual symmetric-form representative. *)
Definition is_weierstrass_split_coefficient (R:realType) (X K:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (alpha:analytic_germ_space hNX (0:X))
    (v:X) (inclusion:Hom K X) (i j:nat) (C:K->R):Prop:=
  forall F:S_m X R^o (i+j),
    (forall t,F t=@ContinuousMultilinear.evaluation R (i+j)%N X R^o NX (fun r=>`|r|)
      hNX (@scalar_absolute_value_norm R) [ffun s=>tnth t s]
      (@AnalyticGermJets.value R X NX hNX 0 (i+j)%N alpha)) ->
    forall z,C z=sform_polynomial_value (symmetric_taylor_term j F v) (inclusion z).
