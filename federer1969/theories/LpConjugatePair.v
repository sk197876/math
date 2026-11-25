(** Federer (1969), 2.5.7, p. 98: the three exponent pairs (p,p/(p-1)),
    (1,infinity), and (infinity,1). The predicate below specifies only
    conjugacy; the additional countable-measurability and
    increasing-continuity hypotheses of the representation theorem remain
    separate. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ConjugateExponents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [is_lp_conjugate_pair]: direct exponent alternatives in
    Federer 2.5.7, p. 98 This predicate alone does not assert the hypotheses
    or conclusion of the representation theorem. *)
Definition is_lp_conjugate_pair (R : realType) (p q : \bar R) :=
  (exists a : R, (1 < a)%R /\ p=a%:E /\ q=(finite_conjugate_exponent a)%:E) \/
  (p = 1 /\ q=+oo) \/ (p=+oo /\ q = 1).

(** Source for [finite_conjugate_exponent_involutive]: supporting symmetry
    of the finite exponent pair in Federer 2.5.7, p. 98 *)
Lemma finite_conjugate_exponent_involutive (R : realType) (p : R) :
  (1 < p)%R -> finite_conjugate_exponent (finite_conjugate_exponent p)=p.
Proof.
move=> hp; apply: invr_inj; apply: (addrI ((finite_conjugate_exponent p)^-1)%R).
rewrite (finite_conjugate_exponent_reciprocals (finite_conjugate_exponent_strict hp)).
by rewrite addrC (finite_conjugate_exponent_reciprocals hp).
Qed.

(** Source for [lp_conjugate_pair_admissible]: supporting domain check for
    the norms in Federer 2.5.7, p. 98 *)
Lemma lp_conjugate_pair_admissible (R : realType) (p q : \bar R) :
  is_lp_conjugate_pair p q -> 1 <= p /\ 1 <= q.
Proof.
move=> [[a [ha [-> ->]]]|[[-> ->]|[-> ->]]]; try by split; rewrite ?leey.
by split; rewrite lee_fin; [exact: ltW ha|exact: ltW (finite_conjugate_exponent_strict ha)].
Qed.

(** Source for [lp_conjugate_pair_symmetric]: supporting exchange of the
    pairing factors in Federer 2.5.7, pp. 98–99 Both infinity endpoints are
    retained in the symmetric predicate. *)
Lemma lp_conjugate_pair_symmetric (R : realType) (p q : \bar R) :
  is_lp_conjugate_pair p q -> is_lp_conjugate_pair q p.
Proof.
move=> [[a [ha [-> ->]]]|[[-> ->]|[-> ->]]].
- left; exists (finite_conjugate_exponent a); split; first exact: finite_conjugate_exponent_strict ha.
  split=> //; by rewrite finite_conjugate_exponent_involutive.
- by right; right.
- by right; left.
Qed.
