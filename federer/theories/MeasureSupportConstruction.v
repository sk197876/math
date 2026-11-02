(** Federer (1969), 2.2.1, p. 60: private existence construction of support
    as the complement of the union of open null sets. Public proofs use only
    the support specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureSupportUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_support_exists]: Federer 2.2.1,
    p. 60: the printed complement is closed because the union
    is open, and it obeys the neighborhood specification. The
    construction works for any extended-real set function; later
    positivity consequences require the measure laws. *)
Lemma measure_support_exists (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) : exists S, is_measure_support mu S.
Proof.
pose N := \bigcup_(U in [set U | open U /\ mu U = 0]) U.
exists (~` N); constructor.
- apply: open_closedC; apply: bigcup_open=> U [ho _]; exact ho.
- move=> x; split.
  + move=> hn U ho hu hz; apply: hn; exists U=> //; by split.
  + move=> h [U [ho hz] hu]; exact: h U ho hu hz.
Qed.
