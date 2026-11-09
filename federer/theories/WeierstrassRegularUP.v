(** Federer (1969), 3.4.6, pp. 321–322: the actual
    directional order of a scalar analytic germ. The predicate
    records the printed vanishing and nonvanishing conditions,
    before any preparation or division theorem is proved. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermUP AnalyticGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_weierstrass_regular_germ]: k is positive,
    the actual directional derivatives below k vanish at the
    original centre, and the kth directional derivative is
    nonzero, as in 3.4.6, p. 321. *)
Definition is_weierstrass_regular_germ (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (alpha:analytic_germ_space hNX (0:X)) k (v:X):Prop:=
  (0<k)%N /\
  (forall i,(i<k)%N ->
    @ContinuousMultilinear.evaluation R i X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
      [ffun _:'I_i=>v] (@AnalyticGermJets.value R X NX hNX 0 i alpha)=0) /\
  @ContinuousMultilinear.evaluation R k X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
    [ffun _:'I_k=>v] (@AnalyticGermJets.value R X NX hNX 0 k alpha)<>0.
