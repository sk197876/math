(** Federer (1969), 3.4.7, p. 324, referring
    to 3.4.6, pp. 321–322: the actual
    directional order at an arbitrary original centre.
    The vanishing and nonvanishing laws are specified
    before the almost-everywhere consequence. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermUP AnalyticGermJetsSealed WeierstrassRegularUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_analytic_germ_direction_regular_at]:
    the hypothesis of 3.4.6 at the original
    centre a, as used in 3.4.7, p. 324.
    The order is positive, all smaller actual
    directional derivatives vanish, and the kth does not. *)
Definition is_analytic_germ_direction_regular_at (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a (alpha:analytic_germ_space hNX a) k v:Prop:=
  (0<k)%N /\
  (forall i,(i<k)%N ->@ContinuousMultilinear.evaluation R i X R^o NX (fun t=>`|t|)
    hNX (@scalar_absolute_value_norm R) [ffun _:'I_i=>v]
      (@AnalyticGermJets.value R X NX hNX a i alpha) = 0) /\
  @ContinuousMultilinear.evaluation R k X R^o NX (fun t=>`|t|)
    hNX (@scalar_absolute_value_norm R) [ffun _:'I_k=>v]
      (@AnalyticGermJets.value R X NX hNX a k alpha)<>0.

(** Source for [analytic_germ_direction_regular_origin]:
    the arbitrary-centre condition reduces to exactly
    the original 3.4.6 regularity interface at zero,
    supporting 3.4.7, p. 324. *)
Lemma analytic_germ_direction_regular_origin (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (alpha:analytic_germ_space hNX (0:X)) k v:
  is_analytic_germ_direction_regular_at alpha k v <->is_weierstrass_regular_germ alpha k v.
Proof. by []. Qed.
