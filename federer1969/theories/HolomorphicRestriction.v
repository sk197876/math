(** Federer (1969), 3.4.12, pp. 338–339:
    the original holomorphic condition is local on its
    actual open domain and ignores values outside that
    domain. Reuse real analytic restriction and derivative uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed RealNormUP
  NormDifferentialUP NormDifferentialLocal NormDifferentialDirectional NormAnalyticOperations
  HolomorphicUP HolomorphicDifferentialUP HolomorphicDifferentialExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Restriction.
Variable R:realType.
Variables X Y:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Variable NX:XR->R.
Variable NY:YR->R.
Variable hNX:is_real_norm NX.
Variable hNY:is_real_norm NY.
Variables A U:X->Prop.

(** Source for [holomorphic_open_restriction]: restrict
    the original holomorphic function to any open subdomain,
    supporting the neighbourhood germ definition in 3.4.12,
    p. 339. *)
Theorem holomorphic_open_restriction (f:X->Y):
  (forall x,U x ->A x) ->
  (forall x,U x ->norm_domain_interior NX U x) ->
  is_holomorphic hNX hNY A f ->is_holomorphic hNX hNY U f.
Proof.
move=>hUA hOpen hF;split;first exact:(@norm_analytic_open_restriction R XR YR NX NY hNX hNY A U f hUA hOpen hF.1).
move=>a L ha hActual.
have [D [M [hM hD]]]:=holomorphic_differential_exists hF (hUA a ha).
have hRestricted:=@norm_differential_restrict R XR YR NX NY A U f a M
  hUA (hOpen a ha) hM.
have hEqual:=norm_differential_unique hNX hNY hActual hRestricted.
rewrite hEqual;exact:hF.2 a M (hUA a ha) hM.
Qed.

(** Source for [holomorphic_domain_agreement]: changing
    a total function outside the original domain changes
    no holomorphic germ, 3.4.12, p. 339.
    Every derivative remains the actual ordinary derivative. *)
Theorem holomorphic_domain_agreement (f g:X->Y):
  (forall x,A x ->f x=g x) ->
  is_holomorphic hNX hNY A f ->is_holomorphic hNX hNY A g.
Proof.
move=>hValues hF;split;first exact:(@norm_analytic_domain_agreement R XR YR NX NY hNX hNY A f g hValues hF.1).
move=>a L ha hActual.
have [D [M [hM hD]]]:=holomorphic_differential_exists hF ha.
have hMG:=@norm_differential_domain_agreement R XR YR NX NY hNX A f g a M hValues hM.
have hEqual:=norm_differential_unique hNX hNY hActual hMG.
rewrite hEqual;exact:hF.2 a M ha hM.
Qed.
End Restriction.
