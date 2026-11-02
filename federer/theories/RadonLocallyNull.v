(** Federer (1969), 2.5.14, p. 108: local almost uniqueness of the vector
    density. For the Radon measure, compact exceptional-set tests are
    equivalent to all finite tests by the countable compact covers used in
    2.5.10, p. 101. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureAlmostBasic RadonMeasureUP RadonCountableCompactCover
  LocallyNullMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radon_locally_null_compact_iff]: precise compact
    interpretation of local nullity for the Radon modification
    in Federer 2.5.14, p. 108. Finite tests need not be
    measurable; 2.5.10, p. 101, covers them almost by compacts. *)
Theorem radon_locally_null_compact_iff (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu) (N : set X) :
  measure_locally_null mu N <-> (forall K, compact K -> mu (K `&` N)=0).
Proof.
split.
- move=> h K hK; exact: h K (radon_compact_finite hr hK).
- move=> h A hA; have [K [hK hrest]] := @radon_finite_countable_compact_cover R X mu hm hr A hA.
  have hunion : mu (\bigcup_n (K n `&` N))=0.
    apply: (@measure_null_countable_union R X [the choiceType of (nat : Type)] mu hm setT
      (fun n => K n `&` N)); first exact: countableP.
    move=> n _.
    exact: h (K n) (hK n).
  have hnull := measure_null_union hm hrest hunion.
  apply: (@measure_null_subset R X mu hm _ _ _ hnull)=> x [hx hn].
  case: (pselect ((\bigcup_n K n) x))=> [[n _ hnx]|hout].
  + right; exists n=> //; by split.
  + left; by split.
Qed.
