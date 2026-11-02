(** Federer (1969), 3.1.24, pp. 237–240: the
    analytic conditions depend only on values in a neighbourhood
    contained in the actual function domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormDifferentialUP NormRegularity NormRegularityOperations NormHigherDifferentialUP
  NormHigherDifferentialLocal NormHigherDifferentialUnique NormLinearDomainLaws
  NormAnalyticUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [norm_analytic_at_domain_enlargement]: supporting
    the local analytic definition in Federer 3.1.24,
    p. 237. An analytic neighbourhood contained in A also
    lies in any larger domain B; the same witness proves
    analyticity there. Values away from that neighbourhood do
    not enter the definition. *)
Lemma norm_analytic_at_domain_enlargement (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A B:set X) (f:X->Y) a :
  A `<=` B -> @norm_analytic_at R X Y NX NY hNX hNY A f a ->
  @norm_analytic_at R X Y NX NY hNX hNY B f a.
Proof.
move=>hAB [U [c [ha [hUA [hc hb]]]]].
exists U,c; split; first exact ha.
split; first by move=>x hx; exact (hAB x (hUA x hx)).
by split.
Qed.

(** Source for [norm_analytic_at_open_restriction]: restricting
    to an open subdomain containing the centre preserves the
    local analytic conditions, Federer 3.1.24, pp. 237–238.
    Actual higher differentials on the intersection are identified
    with the originals by the open-restriction and uniqueness laws. *)
Lemma norm_analytic_at_open_restriction (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A B:set X) (f:X->Y) a :
  B a -> (forall x,B x -> norm_domain_interior NX B x) ->
  @norm_analytic_at R X Y NX NY hNX hNY A f a ->
  @norm_analytic_at R X Y NX NY hNX hNY (fun x=>A x /\ B x) f a.
Proof.
move=>haB hB [U [c [ha [hUA [hc hb]]]]].
pose C:=fun x=>U x /\ B x.
have hOpen x (hx:C x):norm_domain_interior NX C x.
  exact (norm_domain_intersection_interior ((hc 0%N).1 x hx.1).1 (hB x hx.2)).
exists C,c; split; first by split.
split; first by move=>x hx; split; [exact (hUA x hx.1)|exact hx.2].
split.
- move=>k; exact (@norm_class_open_restriction R X Y NX NY hNX hNY U C f k
    (fun x hx=>hx.1) hOpen (hc k)).
- move=>m hm x hx z hz.
  have hh:=(@norm_higher_differential_open_restriction R X Y NX NY hNX hNY
    (fun i=>@ContinuousMultilinear.space R i X Y NX NY hNX hNY)
    (fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY)
    (fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY)
    (fun i=>@ContinuousMultilinear.laws R i X Y NX NY hNX hNY)
    m U C f (fun x hx=>hx.1) hOpen x hx z).2 hz.
  exact (hb m hm x hx.1 z hh).
Qed.

(** Source for [norm_analytic_at_domain_agreement]: the local
    analytic conditions in Federer 3.1.24, pp. 237–238,
    depend only on the function's values on its actual domain.
    Class laws and every exact higher differential are transported
    by the proved agreement theorems. *)
Lemma norm_analytic_at_domain_agreement (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f g:X->Y) a :
  (forall x,A x -> f x=g x) ->
  @norm_analytic_at R X Y NX NY hNX hNY A f a ->
  @norm_analytic_at R X Y NX NY hNX hNY A g a.
Proof.
move=>heq [U [c [ha [hUA [hc hb]]]]].
have hOpen x (hx:U x):norm_domain_interior NX U x:=((hc 0%N).1 x hx).1.
exists U,c; split; first exact ha.
split; first exact hUA.
split.
- move=>k; exact (@norm_class_domain_agreement R X Y NX NY hNX hNY U f g k
    (fun x hx=>heq x (hUA x hx)) (hc k)).
- move=>m hm x hx z hz.
  have hh:=(@norm_higher_differential_local_agreement R X Y NX NY hNX hNY
    (fun i=>@ContinuousMultilinear.space R i X Y NX NY hNX hNY)
    (fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY)
    (fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY)
    (fun i=>@ContinuousMultilinear.laws R i X Y NX NY hNX hNY)
    m U U U f g hOpen (fun x hx=>iff_refl _) (fun x hx _=>heq x (hUA x hx)) x hx z).2 hz.
  exact (hb m hm x hx z hh).
Qed.
