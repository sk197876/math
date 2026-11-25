(** Federer (1969), 3.4.6, p. 323: the actual
    Taylor coefficients of the grouped double series, specified
    before proving an analytic realisation. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermUP AnalyticGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_weierstrass_grouped_germ]: each actual
    homogeneous Taylor polynomial equals the original finite
    total-degree grouping, 3.4.6, p. 323.
    This law neither assumes a sum's existence nor gives
    any division or preparation conclusion. *)
Definition is_weierstrass_grouped_germ (R:realType) (X K:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (xi:Hom X R^o) (projection:Hom X K)
    (q:nat->nat->K->R) (alpha:analytic_germ_space hNX (0:X)):Prop:=
  forall m x,(\sum_(i<m.+1) (xi x)^+i*q i (m-i)%N (projection x))=
    ((m`!)%:R)^-1*@ContinuousMultilinear.evaluation R m X R^o NX (fun r=>`|r|)
      hNX (@scalar_absolute_value_norm R) [ffun _:'I_m=>x]
      (@AnalyticGermJets.value R X NX hNX 0 m alpha).
