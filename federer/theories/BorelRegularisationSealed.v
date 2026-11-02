(** Federer (1969), 2.2.3, p. 62, final paragraph: regularisation by the
    infimum over Borel supersets. The construction is sealed; mathematical
    consequences use its greatest-lower-bound laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import TopologicalBorel BorelRegularisationUP BorelRegularisationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Module Type BorelRegularisationSignature.
(** Source for [value]: Federer 2.2.3, p. 62;
    abstract operator assigning regularised set functions. *)
Parameter value : forall (R : realType) (I : topologicalType),
  (set I -> \bar R) -> set I -> \bar R.
(** Source for [laws]: Federer 2.2.3, p. 62;
    the exposed value satisfies the greatest-lower-bound specification. *)
Parameter laws : forall (R : realType) (I : topologicalType) (mu : set I -> \bar R),
  is_borel_regularisation mu (@value R I mu).
End BorelRegularisationSignature.

Module BorelRegularisation : BorelRegularisationSignature.
(** Source for [value]: Federer 2.2.3, p. 62;
    private selection of the proved infimum witness. *)
Definition value (R : realType) (I : topologicalType) (mu : set I -> \bar R) :=
  projT1 (cid (borel_regularisation_exists mu)).
(** Source for [laws]: Federer 2.2.3, p. 62;
    selected witness obeys the abstract specification. *)
Lemma laws (R : realType) (I : topologicalType) (mu : set I -> \bar R) :
  is_borel_regularisation mu (value mu).
Proof. exact: projT2 (cid (borel_regularisation_exists mu)). Qed.
End BorelRegularisation.
