(** Federer (1969), 3.4.7, p. 324: the
    polar argument chooses a positive radius outside
    a null exceptional set. This supporting measure
    lemma extracts a good point from positive outer mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_almost_positive_set_witness]: the
    good-radius choice in the use of 3.2.13
    in 3.4.7, p. 324. A set of
    nonzero outer mass meets every conull truth set;
    no measurability premise is needed. *)
Lemma measure_almost_positive_set_witness (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hMu:is_measure mu) (A P:set X):
  mu A<>0 ->measure_almost_everywhere mu P ->exists x,A x /\P x.
Proof.
move=>hMass hAlmost;apply:contrapT=>hNo;apply:hMass.
apply:(@measure_null_subset R X mu hMu A (~` P));last exact:hAlmost.
move=>x hx hP;apply:hNo;by exists x.
Qed.
