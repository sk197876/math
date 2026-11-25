(** Supporting algebra for Federer (1969), 3.4.8(5), p. 328:
    a proved one-block ideal-power inclusion iterates to every
    block. Reuse the original opaque power and product laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeIdealPowersSealed CommutativeIdealPowersLaws
  CommutativeIdealProductSealed CommutativeIdealProductLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [commutative_ideal_power_block_inclusion]: supporting
    original coefficient/quotient filtration for Federer 3.4.8(5),
    p. 328. The original inclusion M^K subset J implies
    M^(K*q) subset J^q for every natural q, including zero. *)
Theorem commutative_ideal_power_block_inclusion (A:comNzRingType)
    (M J:set A) K:
  @CommutativeIdealPowers.value A M K `<=` J ->forall q,
  @CommutativeIdealPowers.value A M (K*q)%N `<=`
    @CommutativeIdealPowers.value A J q.
Proof.
move=>hBlock;elim=>[|q ih].
- by rewrite muln0 !commutative_ideal_power_zeroE.
- rewrite mulnS commutative_ideal_power_add commutative_ideal_power_successorE.
  exact:(commutative_ideal_product_monotone hBlock ih).
Qed.
