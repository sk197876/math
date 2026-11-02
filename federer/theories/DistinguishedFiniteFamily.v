(** Finite cardinal contradiction in Federer (1969), 2.8.12, p. 149: one
    remaining pair and 2 zeta+1 distinct selected witnesses cannot together
    have cardinality at most 2 zeta+1. This is supporting set theory *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality.
From Federer Require Import CardinalInjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [distinguished_finite_family_exceeds_bound]: the
    card P=2 zeta+2 contradiction in Federer 2.8.12, p. 149,
    in general finite-cardinal form. An injectively indexed family
    of N members and a distinct extra member cannot have cardinal
    bound N. The auxiliary result includes N=0. *)
Lemma distinguished_finite_family_exceeds_bound (T : choiceType)
    (N : nat) (p : T) (b : 'I_N -> T) :
  injective b -> (forall i, b i <> p) ->
  ~ (([set p] `|` (b @` setT)) #<= [set: 'I_N]).
Proof.
move=> hi hp hbound.
pose f (i : 'I_N.+1) := if unlift ord0 i is Some j then b j else p.
have hf0 : f ord0 = p by rewrite /f unlift_none.
have hfS j : f (lift ord0 j) = b j by rewrite /f liftK.
have hf : injective f.
  move=> i j; case: (unliftP ord0 i)=> [u ->|->];
    case: (unliftP ord0 j)=> [v ->|->]; rewrite ?hfS ?hf0.
  - by move=> /hi ->.
  - by move=> /hp.
  - by move=> he; exfalso; apply: (hp v); exact: esym he.
  - by [].
have hcard : [set: 'I_N.+1] #<= [set p] `|` (b @` setT).
  apply: (@cardinal_bound_of_injection [the choiceType of 'I_N.+1] T
    setT ([set p] `|` (b @` setT)) f).
  - move=> i _; case: (unliftP ord0 i)=> [u ->|->].
    + rewrite hfS; right; by exists u.
    + rewrite hf0; by left.
  - by move=> i j _ _; exact: hf.
have hbad := card_le_trans hcard hbound.
by move: hbad; rewrite -(card_le_eql (@card_II N.+1))
  -(card_le_eqr (@card_II N)) card_le_II ltnn.
Qed.
