(** Federer (1969), 3.4.6, p. 323: subtraction
    of actual analytic germs subtracts their original mixed
    coefficients, as used for R=psi-Q*phi. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermUP AnalyticGermSealed AnalyticGermJetArithmetic AnalyticGermJetZeroNegate
  WeierstrassCoefficientUP WeierstrassCoefficientValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_split_coefficient_difference]:
    the actual coefficients of alpha-beta are the
    differences of the original coefficients, supporting the
    remainder equations in 3.4.6, p. 323. *)
Lemma weierstrass_split_coefficient_difference (R:realType) (X K:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (alpha beta:analytic_germ_space hNX (0:X))
    (v:X) (inclusion:Hom K X) i j (A B C:K->R):
  is_weierstrass_split_coefficient alpha v inclusion i j A ->
  is_weierstrass_split_coefficient beta v inclusion i j B ->
  is_weierstrass_split_coefficient (@AnalyticGerms.add R X NX hNX 0 alpha
    (@AnalyticGerms.opp R X NX hNX 0 beta)) v inclusion i j C ->
  forall z,C z=A z-B z.
Proof.
move=>hA hB hC z.
rewrite (weierstrass_split_coefficient_value hC z)
  analytic_germ_jet_add analytic_germ_jet_negate.
have hEvaluation:forall (L:Hom (@ContinuousMultilinear.space R (i+j)%N X R^o NX
    (fun r=>`|r|) hNX (@scalar_absolute_value_norm R)) R^o) a b,L (a+ -b)=L a-L b.
  move=>L a b;exact:linearB.
rewrite hEvaluation mulrBr.
by rewrite -(weierstrass_split_coefficient_value hA z) -(weierstrass_split_coefficient_value hB z).
Qed.
