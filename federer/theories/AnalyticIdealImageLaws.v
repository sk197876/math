(** Federer (1969), 3.4.8(2), p. 326:
    the actual invertible orthogonal ring map carries
    the original ideal to an ideal and preserves its
    properness. These generic algebraic laws use the
    separately proved inverse of the actual action. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeIdealUP AnalyticRotatedIdealUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section IdealImages.
Variables A B:comNzRingType.
Variable M:{rmorphism A->B}.
Variables (I:set A) (J:set B).
Hypothesis hImage:is_analytic_ideal_image M I J.

(** Source for [analytic_ideal_image_ideal]: an onto ring
    map carries the original ideal to an ideal,
    supporting I_g in 3.4.8(2), p. 326. *)
Theorem analytic_ideal_image_ideal:
  (forall y:B,exists x:A,M x=y) ->is_commutative_ideal I ->is_commutative_ideal J.
Proof.
move=>hOnto hI;constructor.
- apply/(hImage 0);exists 0;split;[exact:commutative_ideal_zero hI|exact:rmorph0].
- move=>x y /(hImage x)[a [ha <-]] /(hImage y)[b [hb <-]].
  apply/(hImage (M a+M b));exists (a+b);split.
  + exact:(commutative_ideal_add hI ha hb).
  + exact:rmorphD.
- move=>x /(hImage x)[a [ha <-]].
  apply/(hImage (-M a));exists (-a);split.
  + exact:(commutative_ideal_opp hI ha).
  + exact:rmorphN.
- move=>x y hy;have [a ha]:=hOnto x.
  have [b [hb hB]]:=(hImage y).1 hy.
  apply/(hImage (x*y));exists (a*b);split.
  + exact:(@commutative_ideal_mul A I hI a b hb).
  + by rewrite rmorphM ha hB.
Qed.

(** Source for [analytic_ideal_image_proper]: an injective
    ring map preserves the original proper-ideal condition,
    supporting 3.4.8(2), p. 326. *)
Lemma analytic_ideal_image_proper:
  injective M ->~I 1 ->~J 1.
Proof.
move=>hInjective hProper /(hImage 1)[a [ha hOne]].
have hA : a = 1 by apply:hInjective;by rewrite rmorph1.
apply:hProper;by rewrite -hA.
Qed.
End IdealImages.
