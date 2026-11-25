(** Federer (1969), 3.4.12, pp. 338–339: the actual
    analytic inverse theorem retains the holomorphic condition.
    Reuse the real analytic inverse majorant and actual inverse
    differential identities; no inverse complex linearity is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP RealNormUP ScalarRestriction ComplexScalarSealed
  NormDifferentialUP NormDifferentialInverseIdentities NormRegularity NormAnalyticInverse
  HolomorphicUP HolomorphicDifferentialUP HolomorphicDifferentialExistence ComplexLinearInverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Inverse.
Variable R:realType.
Variables X Y:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Variables (NX:XR->R) (NY:YR->R).
Variables (hNX:is_real_norm NX) (hNY:is_real_norm NY).
Variables (A:X->Prop) (B:Y->Prop) (f:X->Y) (g:Y->X).

(** Source for [holomorphic_inverse_from_first]: an actual class-one
    inverse of an original holomorphic map is holomorphic,
    extending 3.1.24, pp. 239–240, under 3.4.12, p. 339.
    Completeness and finite dimension are not added. *)
Theorem holomorphic_inverse_from_first:
  (forall x,A x ->B (f x)) ->(forall y,B y ->A (g y)) ->
  (forall x,A x ->g (f x)=x) ->(forall y,B y ->f (g y)=y) ->
  norm_class hNX hNY A f 1%N ->is_holomorphic hNY hNX B g ->is_holomorphic hNX hNY A f.
Proof.
move=>hAB hBA hGF hFG hClass hG.
split;first exact:(@norm_analytic_inverse_from_first R XR YR NX NY hNX hNY A B f g
  hAB hBA hGF hFG hClass hG.1).
move=>a L ha hL.
have [D [M [hM hD]]]:=holomorphic_differential_exists hG (hAB a ha).
have hFirst:=@norm_differentials_left_inverse R XR YR NX NY hNX hNY A B f g a L M
  hAB hGF hL hM.
have hAt:has_norm_differential NX NY A f (g (f a)) L by rewrite hGF.
have hSecond:=@norm_differentials_left_inverse R YR XR NY NX hNY hNX B A g f (f a) M L
  hBA hFG hM hAt.
have hML x:M (L x)=x.
  have h:=congr1 (fun K:Hom XR XR=>K x) hFirst.
  exact:h.
have hLM y:L (M y)=y.
  have h:=congr1 (fun K:Hom YR YR=>K y) hSecond.
  exact:h.
exact:(complex_linear_real_inverse hML hLM (hG.2 (f a) M (hAB a ha) hM)).
Qed.
End Inverse.
