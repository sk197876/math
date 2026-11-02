(** Federer (1969), 2.4.12, p. 86: the Hahn–Banach
    theorem for the book's possibly infinite seminorms. Public
    consequences use only the sealed extension laws. Source
    editions: ExtendedSeminormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedSeminormUP ExtendedSeminormLaws PartialLinearMap ExtendedHahnBanachSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [extended_seminorm_hahn_banach]: direct formalisation
    of the italicised extension theorem in Federer 2.4.12,
    p. 86. A linear graph represents a linear functional
    on an arbitrary vector subspace. No finiteness restriction
    is placed on the ambient seminorm. *)
Theorem extended_seminorm_hahn_banach (R : realType) (V : lmodType R)
    (N : V -> \bar R) (hN : is_extended_seminorm N) (G : V -> R^o -> Prop)
    (hG : linear_graph G) (hdom : forall x a, G x a -> (a%:E <= N x)%E) :
  exists f : {linear V -> R^o}, (forall x a, G x a -> f x=a) /\
    (forall x, ((f x)%:E <= N x)%E).
Proof.
exists (@ExtendedHahnBanach.extension R V N hN G hG hdom); split.
- exact: ExtendedHahnBanach.agreement.
- exact: ExtendedHahnBanach.bound.
Qed.

(** Source for [extended_dominated_functional_absolute_bound]:
    supporting symmetric bound from the domination in Federer
    2.4.12, p. 86. Evaluate the linear functional
    at x and -x and use the seminorm's symmetry. *)
Lemma extended_dominated_functional_absolute_bound (R : realType) (V : lmodType R)
    (N : V -> \bar R) (hN : is_extended_seminorm N) (f : {linear V -> R^o}) :
  (forall x, ((f x)%:E <= N x)%E) -> forall x, (`|f x|%:E <= N x)%E.
Proof.
move=> h x; have [hx|hx] := leP 0 (f x).
- rewrite (ger0_norm hx); exact: h.
- rewrite (ltr0_norm hx); have hn := h (-x).
  by rewrite linearN (extended_seminorm_negate hN) in hn.
Qed.
