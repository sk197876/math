(** Federer (1969), 2.1.2, p. 54: an injective
    image map commutes with restriction to the actual image
    of the source set. Supporting completed product coordinates
    and fibre weights in 3.2.48, p. 284. *)
From mathcomp Require Import all_boot all_algebra reals boolp classical_sets constructive_ereal.
From Federer Require Import MeasureUP MeasureRestriction MeasurePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [injective_restriction_pushforward]: supporting
    image-measure identity from 2.1.2, p. 54, used
    in the original-coordinate integrals of 3.2.48,
    p. 284. Equality holds on arbitrary test subsets;
    neither the restricted set nor its image need be Borel. *)
Lemma injective_restriction_pushforward (R:realType) (X Y:choiceType)
    (mu:set X->\bar R) (f:X->Y) (A:set X):
  injective f ->measure_pushforward f (measure_restrict mu A)=
    measure_restrict (measure_pushforward f mu) (f @` A).
Proof.
move=>hf; apply:funext=>T.
have hPre:f @^-1` (f @` A)=A.
  apply/seteqP; split=>x.
  - move=>[y hy hSame]; have hEq:y=x:=hf _ _ hSame.
    by rewrite -hEq.
  - move=>hx; by exists x.
by rewrite /measure_pushforward /measure_restrict preimage_setI hPre.
Qed.
