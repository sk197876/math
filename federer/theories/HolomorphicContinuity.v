(** Federer (1969), 3.4.12, pp. 338–339: every original
    holomorphic map is continuous at each point of its actual domain.
    Apply the project's real analytic class-zero continuity theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed RealNormUP NormMetric
  NormRegularity NormAnalyticLocal NormClassZeroTopology HolomorphicUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(** Source for [holomorphic_continuous_at]: the original complex
    analytic definition retains real analytic continuity on its original
    domain, 3.4.12, pp. 338–339. *)
Theorem holomorphic_continuous_at (R:realType)
    (X Y:lmodType (ComplexScalars.C R)) (NX:X->R) (NY:Y->R)
    (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX)
    (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
    (A:X->Prop) (f:X->Y):
  @is_holomorphic R X Y NX NY hNX hNY A f ->forall a,A a ->
    {for a,continuous (fun x:real_norm_metric_space hNX=>(f x:real_norm_metric_space hNY))}.
Proof.
move=>hF a ha.
have hClass:=norm_analytic_class_all_orders hF.1 0%N.
exact:(@norm_class_zero_continuous_at R (restricted_space (ComplexScalars.embed R) X)
  (restricted_space (ComplexScalars.embed R) Y) NX NY hNX hNY A f a (norm_class_continuous hClass) ha).
Qed.
