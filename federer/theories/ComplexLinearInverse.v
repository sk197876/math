(** Federer (1969), 3.4.12, pp. 338–339: the inverse
    of an invertible complex-linear differential is complex linear.
    The original real operators and both inverse identities suffice. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed ComplexRealLinearMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [complex_linear_real_inverse]: the scalar law
    required when applying the real analytic inverse theorem
    to original holomorphic coordinates, extending 3.1.24, p. 240,
    under 3.4.12, p. 339. *)
Lemma complex_linear_real_inverse (R:realFieldType) (X Y:lmodType (ComplexScalars.C R))
    (L:Hom (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) Y))
    (M:Hom (restricted_space (ComplexScalars.embed R) Y) (restricted_space (ComplexScalars.embed R) X)):
  (forall x,M (L x)=x) ->(forall y,L (M y)=y) ->
  is_complex_linear_real_map M ->is_complex_linear_real_map L.
Proof.
move=>hML hLM hComplex c x.
have hInjective:injective M:=can_inj hLM.
apply:hInjective.
change (M (L (c*:(x:X)))=M (c*:(L x:Y))).
by rewrite hML hComplex hML.
Qed.
