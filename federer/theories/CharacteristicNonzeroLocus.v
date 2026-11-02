(** Federer (1969), 2.6.3(1), p. 117: the characteristic function is not
    countably measurable precisely because its nonzero locus is the
    diagonal. This supporting identity uses the definition in 2.3.4, p. 76. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  CharacteristicFunctionUP CountablyMeasurableUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_characteristic_nonzero_locus]: the
    nonzero locus of a characteristic function is its set,
    supporting the last conclusions of Federer 2.6.3(1),
    p. 117. This includes empty sets and empty carriers. *)
Lemma extended_characteristic_nonzero_locus (R : realType) (X : Type)
    (A : set X) (s : X -> R) :
  is_characteristic_function A s ->
  partial_function_nonzero_locus (0 : extended_real_line R)
    (partial_function_total (fun x => (s x)%:E : extended_real_line R)) = A.
Proof.
move=> hs; apply/seteqP; split=> x.
- move=> [z [<- hn]]; apply: contrapT=> hx.
  apply: hn; by rewrite (characteristic_off_set hs hx).
- move=> hx; exists (s x)%:E; split=> //.
  rewrite (characteristic_on_set hs hx)=> he.
  have h10 : (1 : R)%R = 0%R by injection he.
  by move: h10; move/eqP; rewrite oner_eq0.
Qed.
