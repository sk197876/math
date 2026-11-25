(** Federer (1969), 2.2.1, p. 60: public support interface. All consequences
    use the sealed neighborhood specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureSupportUP MeasureSupportLaws MeasureSupportSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_support]: Federer 2.2.1, p. 60,
    the support set, exposed through its abstract laws. *)
Definition measure_support (R : realType) (T : topologicalType) (mu : set T -> \bar R) :=
  MeasureSupport.value mu.

(** Source for [measure_support_specification]: Federer 2.2.1,
    p. 60, support obeys closedness and the neighborhood criterion. *)
Lemma measure_support_specification (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) : is_measure_support mu (measure_support mu).
Proof. exact: MeasureSupport.laws. Qed.

(** Source for [measure_support_closed]: Federer 2.2.1,
    p. 60, support is a closed subset of the measured space. *)
Lemma measure_support_closed (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) : closed (measure_support mu).
Proof. exact: measure_support_closed_law (measure_support_specification mu). Qed.

(** Source for [measure_support_formula]: Federer 2.2.1,
    p. 60, recover the printed open-null-set union formula from
    the public abstract interface. *)
Lemma measure_support_formula (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) :
  measure_support mu = ~` (\bigcup_(U in [set U | open U /\ mu U = 0]) U).
Proof. exact: measure_support_specification_formula (measure_support_specification mu). Qed.

(** Source for [measure_support_zero]: Federer 2.2.1,
    p. 60, supporting boundary case: the identically zero set
    function has empty support because the whole space is open and null. *)
Lemma measure_support_zero (R : realType) (T : topologicalType) :
  measure_support (fun _ : set T => (0 : \bar R)) = set0.
Proof.
apply/seteqP; split=> [x hx|x []].
have h := proj1 (measure_support_neighborhood_law (measure_support_specification _) x) hx.
exact: h setT openT Logic.I (erefl _).
Qed.
