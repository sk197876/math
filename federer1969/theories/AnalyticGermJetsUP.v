(** Federer (1969), 3.4.5, p. 319: actual higher
    differentials at the centre are specified independently of a representative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP AnalyticGermRepresentatives AnalyticGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_analytic_germ_jet]: the statement that
    the actual m-th differential is determined by the analytic
    germ, 3.4.5, p. 319. The predicate requires the
    actual differential for every representative and assumes no
    derivative existence, metric property or Taylor uniqueness. *)
Definition is_analytic_germ_jet (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) m
    (alpha:analytic_germ_space hNX a)
    (z:@ContinuousMultilinear.space R m X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)):=
  forall f:@analytic_representative_type R X NX hNX a,
    analytic_germ f=alpha ->
    has_norm_higher_differential NX
      (fun i=>@ContinuousMultilinear.evaluation R i X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R))
      (fun i=>@ContinuousMultilinear.norm R i X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R))
      setT (analytic_representative_value f) m a z.
