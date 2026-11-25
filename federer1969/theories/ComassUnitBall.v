(** Federer (1969), 1.8.3, p. 40: the displayed convex set consists of
    covectors with comass at most one. The ensuing question asks for its
    extreme points; it asserts no classification. The May 1987 erratum
    contains no correction to this item. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import InnerProductUP AlternatingCoordinates AlternatingPairing
  SimpleUnitBall ComassUP ComassBounds InnerConvex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Ball.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable m : nat.
Variable kappa : A_m V R^o m -> R.
Hypothesis hk : forall phi, is_comass h2 hB phi (kappa phi).

(** Source for [comass_unit_ball]: Federer 1.8.3, p. 40,
    the displayed set of alternating covectors phi with ||phi||<=1.
    The definition is intrinsic; R^n is a particular ambient space. *)
Definition comass_unit_ball : set (A_m V R^o m) := fun phi => kappa phi <= 1.

(** Source for [comass_unit_ball_evaluations]: Federer 1.8.3,
    p. 40, supporting description as the intersection of the
    half-spaces <x,phi><=1 over simple unit-ball vectors x. *)
Theorem comass_unit_ball_evaluations phi : comass_unit_ball phi <->
  forall x, simple_unit_ball h2 hB x -> pairing x phi <= 1.
Proof.
split.
- move=> hp x hx; exact: le_trans (comass_upper_law (hk phi) hx) hp.
- move=> hp; exact (@comass_least_upper_bound R h2 V B hB m phi (kappa phi) (hk phi) 1 hp).
Qed.

(** Source for [comass_unit_ball_convex]: Federer 1.8.3,
    p. 40, the displayed sets are convex. The proof uses the
    supremum laws directly and does not require positive degree. *)
Theorem comass_unit_ball_convex : is_inner_convex comass_unit_ball.
Proof.
move=> phi psi hp hq t ht0 ht1; apply/comass_unit_ball_evaluations => x hx.
have hp' := proj1 (comass_unit_ball_evaluations phi) hp x hx.
have hq' := proj1 (comass_unit_ball_evaluations psi) hq x hx.
rewrite (bilDr (@pairing_bilinear R V R^o m))
  !(bilZr (@pairing_bilinear R V R^o m)).
change (is_true ((1-t) * pairing x phi + t * pairing x psi <= 1)).
have hmt : 0 <= 1-t by rewrite subr_ge0.
have hh := lerD (ler_wpM2l hmt hp') (ler_wpM2l ht0 hq').
by rewrite !mulr1 subrK in hh.
Qed.

(** Source for [comass_unit_ball_zero]: Federer 1.8.3,
    p. 40, supporting nonemptiness of the convex set: the zero
    covector belongs to it, also with the literal degree-zero convention. *)
Lemma comass_unit_ball_zero : comass_unit_ball 0.
Proof.
apply/comass_unit_ball_evaluations => x hx.
rewrite (bil0r (@pairing_bilinear R V R^o m)); exact: ler01.
Qed.
End Ball.

(** Source for [is_extreme_point]: Federer 1.8.3, p. 40,
    terminology in the question about extreme points. A point of C
    is extreme when every open segment in C containing it has both
    endpoints equal to it. This definition asserts no classification. *)
Definition is_extreme_point (R : realFieldType) (V : lmodType R)
    (C : set V) (z : V) : Prop :=
  C z /\ forall x y, C x -> C y -> forall t : R, 0 < t -> t < 1 ->
    z = (1-t) *: x + t *: y -> x=z /\ y=z.

(** Source for [singleton_extreme_point]: Federer 1.8.3,
    p. 40, supporting boundary interpretation of the question:
    the sole member of a singleton convex set is extreme. This
    is not a classification of the general comass balls. *)
Lemma singleton_extreme_point (R : realFieldType) (V : lmodType R) (z : V) :
  is_extreme_point (fun x => x=z) z.
Proof. split=> // x y hx hy t ht ht1 he; by split. Qed.
