(** Federer (1969), 2.10.22, pp. 184–185: downstream covering-cost bounds
    for the abstract positive-cost enumeration. Use only its four laws; no
    greedy state or choice witness is imported. Nonnegative-sum reindexing
    is the background of 2.1.1(9), p. 53. Source context and the cost-order
    proof route: SummablePositiveMaximum.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import SummableCostEnumerationUP NonnegativeSum NonnegativeSumSupport
  NonnegativeSumRestriction NonnegativeSumProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [cost_enumeration_nonnegative]: supporting
    nonnegativity of the extracted optional cover
    costs in 2.10.22, pp. 184–185. *)
Lemma cost_enumeration_nonnegative (R : realType) (I : choiceType)
    (G : set I) (w : I -> R) (M : R) (u : nat -> option I)
    (hu : is_summable_cost_enumeration G w M u) n :
  (0<=optional_generator_cost w (u n))%R.
Proof.
case hn: (u n)=> [x|]; last exact: lexx.
exact: ltW (@cost_enumeration_member_law R I G w M u hu n x hn).2.
Qed.

(** Source for [cost_enumeration_sum_bound]: supporting
    nonincrease of the full covering cost when
    extracting positive members in 2.10.22,
    pp. 184–185. Inactive indices have zero
    auxiliary cost, and active members occur once. *)
Theorem cost_enumeration_sum_bound (R : realType) (I : choiceType)
    (G : set I) (w : I -> R) (M : R) (u : nat -> option I)
    (hu : is_summable_cost_enumeration G w M u) :
  (forall x, G x -> (0<=w x)%R) ->
  nonnegative_sum setT (fun n=>(optional_generator_cost w (u n))%:E)<=
    nonnegative_sum G (fun x=>(w x)%:E).
Proof.
move=> hw.
pose A : set nat := [set n | exists x, u n=Some x].
pose f (n : nat) := (optional_generator_cost w (u n))%:E.
pose c (o : option I) := (optional_generator_cost w o)%:E.
have hf n : 0<=f n by rewrite /f lee_fin; exact: (@cost_enumeration_nonnegative R I G w M u hu n).
have hz : nonnegative_sum (setT `\` A) f=0.
  apply: nonnegative_sum_zero=> n [hn hnot].
  rewrite /f; case he: (u n)=> [x|] //.
  exfalso; apply: hnot; by exists x.
have he : nonnegative_sum setT f=nonnegative_sum A f.
  by rewrite (@nonnegative_sum_split R [the choiceType of (nat : Type)] setT A f (fun n _=>hf n)) setTI hz adde0.
have hinj n m : A n -> A m -> u n=u m -> n=m.
  move=> [x hx] [y hy] hnm.
  have hyx : u m=Some x by rewrite -hnm.
  exact: (@cost_enumeration_injective_law R I G w M u hu n m x hx hyx).
have hsub : u @` A `<=` Some @` G.
  move=> o [n [x hx] <-].
  have hG := (@cost_enumeration_member_law R I G w M u hu n x hx).1.
  exists x=> //; exact: esym hx.
have hsi := @nonnegative_sum_injective_image R [the choiceType of (nat : Type)]
  [the choiceType of option I] A u c hinj (fun n _=>hf n).
have hsome : nonnegative_sum (Some @` G) c=nonnegative_sum G (fun x=>(w x)%:E).
  apply: nonnegative_sum_injective_image.
  - by move=> x y hx hy [].
  - move=> x hx; rewrite /c /optional_generator_cost lee_fin; exact: hw x hx.
rewrite /f in he; rewrite he -hsi -hsome.
exact: nonnegative_sum_subset hsub.
Qed.
