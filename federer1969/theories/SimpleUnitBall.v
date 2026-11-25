(** Federer (1969), 1.8.1, p. 38: S is the set of simple multivectors of
    Euclidean norm at most one. With literal empty products, the symmetry
    and zero-membership below require positive degree. The local May 1987
    erratum has no correction to this passage. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
From Federer Require Import InnerProductUP ExteriorNorm ExteriorGrading
  FiniteExteriorPowers AssociatedSubspace SimpleElementary.
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

(** Source for [simple_unit_ball]: Federer 1.8.1, p. 38,
    displayed set S: simple m-vectors with induced norm at most one. *)
Definition simple_unit_ball : set (exterior_power V m) :=
  fun x => simple x /\ exterior_norm h2 hB x <= 1.

(** Source for [simple_unit_ball_zero]: Federer 1.8.1, p. 38, supporting
    nonemptiness of S. Positive degree is required by the literal product
    definition, consistently. *)
Lemma simple_unit_ball_zero : (0 < m)%N -> simple_unit_ball 0.
Proof.
move=> hm; split; last by rewrite exterior_norm_zero; exact: ler01.
have hs := @simple_scale R V m (e_lambda (fun _ : 'I_m => (0 : V))
  (ord_tuple m)) 0 hm (product_simple _).
by rewrite scale0r in hs.
Qed.

(** Source for [simple_unit_ball_scale]: Federer 1.8.1, p. 38,
    supporting balance of S: scalar multiplication of absolute value
    at most one preserves S in positive degree. *)
Lemma simple_unit_ball_scale c x : (0 < m)%N -> `|c| <= 1 ->
  simple_unit_ball x -> simple_unit_ball (c *: x).
Proof.
move=> hm hc [hs hn]; split; first exact: simple_scale hm hs.
rewrite exterior_norm_scale.
apply: (le_trans (ler_wpM2l (normr_ge0 c) hn)).
by rewrite mulr1.
Qed.

(** Source for [simple_unit_ball_opp]: Federer 1.8.1, p. 38,
    supporting symmetry used to turn the printed supremum into a norm.
    This assertion is false in degree zero with literal empty products. *)
Lemma simple_unit_ball_opp x : (0 < m)%N ->
  simple_unit_ball x -> simple_unit_ball (-x).
Proof.
move=> hm hx; rewrite -scaleN1r.
apply: simple_unit_ball_scale hm _ hx; by rewrite normrN normr1.
Qed.
End Ball.
