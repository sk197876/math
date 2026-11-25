(** Federer (1969), 3.4.6, p. 322: the original
    mixed divided coefficient is exactly the corresponding
    grouped evaluation of the actual analytic germ derivative. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed MultilinearArguments
  AnalyticGermUP AnalyticGermJetsSealed AnalyticGermCoefficientForms WeierstrassCoefficientUP
  WeierstrassMixedFormValue WeierstrassMixedArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_split_coefficient_value]: the
    original f_(i,j)(z) is D^(i+j)(f)(0) on
    i copies of v and j copies of the actual
    included z, divided by i!j!, 3.4.6, p. 322. *)
Theorem weierstrass_split_coefficient_value (R:realType) (X K:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (alpha:analytic_germ_space hNX (0:X))
    (v:X) (inclusion:Hom K X) i j (C:K->R):
  is_weierstrass_split_coefficient alpha v inclusion i j C ->
  forall z,C z=((i`!)%:R*(j`!)%:R)^-1*
    @ContinuousMultilinear.evaluation R (i+j)%N X R^o NX (fun r=>`|r|)
      hNX (@scalar_absolute_value_norm R)
      (multilinear_arguments_join [ffun _:'I_i=>v] [ffun _:'I_j=>inclusion z])
      (@AnalyticGermJets.value R X NX hNX 0 (i+j)%N alpha).
Proof.
move=>hC z.
have [F [hF _]]:=@analytic_germ_coefficient_forms_exists R X NX hNX 0 alpha.
have hArguments:=@weierstrass_joined_arguments_tuple X i j [ffun _:'I_i=>v] [ffun _:'I_j=>inclusion z].
have hLeft:[tuple [ffun _:'I_i=>v] r |r<i]=[tuple v |r<i].
  by apply:eq_from_tnth=>r;rewrite !tnth_mktuple ffunE.
have hRight:[tuple [ffun _:'I_j=>inclusion z] r |r<j]=[tuple inclusion z |r<j].
  by apply:eq_from_tnth=>r;rewrite !tnth_mktuple ffunE.
rewrite hLeft hRight in hArguments.
by rewrite (hC (F (i+j)%N) (hF (i+j)%N) z) weierstrass_mixed_form_value hF -hArguments.
Qed.
