(** Federer (1969), 2.3.3, p. 76: connecting the characteristic-weight sums
    with the abstract scalar recurrence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import GreedyScalarExpansionUP GreedyScalarSeries GreedyMeasurableSets
  CharacteristicFunctionUP WeightedCharacteristicExpansionUP NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [greedy_characteristic_term]: supporting equality of selected
    weights with r_n g_n in Federer 2.3.3, p. 76 *)
Lemma greedy_characteristic_term (R : realType) (X : Type)
    (r : nat -> R) (f : X -> \bar R) (s : nat -> X -> R) (g : nat -> X -> R) :
  (forall n, is_characteristic_function (greedy_expansion_set r f s n) (g n)) ->
  forall n x, (r n * g n x)%R = greedy_scalar_term r (f x) (fun i => s i x) n.
Proof.
move=> hg n x; rewrite /greedy_scalar_term; case: ifP=> hx.
- rewrite (characteristic_on_set (hg n) hx); exact: mulr1.
- have hn : ~ greedy_expansion_set r f s n x by move=> ha; move/negP: hx; apply.
  rewrite (characteristic_off_set (hg n) hn); exact: mulr0.
Qed.

(** Source for [greedy_characteristic_prefix]: direct finite weighted-sum
    identity in the recursion of Federer 2.3.3, p. 76 *)
Lemma greedy_characteristic_prefix (R : realType) (X : Type)
    (r : nat -> R) (f : X -> \bar R) (s : nat -> X -> R) (g : nat -> X -> R) :
  (forall x, is_greedy_scalar_expansion r (f x) (fun n => s n x)) ->
  (forall n, is_characteristic_function (greedy_expansion_set r f s n) (g n)) ->
  forall n x, (\sum_(j < n) r j * g j x)%R = s n x.
Proof.
move=> hs hg n x; elim: n=> [|n IH].
- by rewrite big_ord0 (greedy_scalar_initial (hs x)).
- rewrite big_ord_recr /= IH (@greedy_characteristic_term R X r f s g hg n x)
    (greedy_scalar_step (hs x)) /greedy_scalar_term.
  by case: ifP=> _; rewrite ?addr0.
Qed.

(** Source for [greedy_characteristic_threshold]: the printed
    threshold formula in Federer 2.3.3, p. 76, obtained
    from the abstract scalar recurrence and characteristic laws. *)
Lemma greedy_characteristic_threshold (R : realType) (X : Type)
    (r : nat -> R) (f : X -> \bar R) (s : nat -> X -> R) (g : nat -> X -> R) :
  (forall x, is_greedy_scalar_expansion r (f x) (fun n => s n x)) ->
  (forall n, is_characteristic_function (greedy_expansion_set r f s n) (g n)) ->
  is_greedy_characteristic_expansion f r (greedy_expansion_set r f s) g.
Proof.
move=> hs hg n x; rewrite (@greedy_characteristic_prefix R X r f s g hs hg n x).
by rewrite /greedy_expansion_set addrC.
Qed.
