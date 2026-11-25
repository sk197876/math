(** Federer (1969), 4.1.18, p. 376: supporting
    repeated selection of one admissible successor at
    each integer stage. This elementary set-theoretic
    existence proof exposes only the sequence relation. *)
From mathcomp Require Import all_boot boolp.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section SuccessiveSelection.
Variable X:Type.
Variable x0:X.
Variable P:nat->X->X->Prop.
Hypothesis hStep:forall k x,exists y,P k x y.

(** Source for [successive_selection_step]: a private
    successor witness supporting the repeated choices
    in Federer 4.1.18, p. 376. *)
Local Definition successive_selection_step k x:X:=
  sval (constructive_indefinite_description (hStep k x)).
(** Source for [successive_selection_step_law]: each chosen
    successor satisfies the original relation, supporting
    Federer 4.1.18, p. 376. *)
Local Lemma successive_selection_step_law k x:
  P k x (successive_selection_step k x).
Proof. exact:svalP (constructive_indefinite_description (hStep k x)). Qed.
(** Source for [successive_selection_sequence_witness]: a
    private recursive existence witness; the public result
    does not identify the chosen sequence, supporting
    Federer 4.1.18, p. 376. *)
Local Fixpoint successive_selection_sequence_witness k:X:=
  if k is j.+1 then successive_selection_step j (successive_selection_sequence_witness j)
  else x0.

(** Source for [successive_selection_sequence_exists]: the
    simultaneous original choices exist at every stage,
    supporting Federer 4.1.18, p. 376. *)
Theorem successive_selection_sequence_exists:
  exists s:nat->X,s 0=x0 /\forall k,P k (s k) (s k.+1).
Proof.
exists successive_selection_sequence_witness;split;first reflexivity.
move=>k;exact:successive_selection_step_law.
Qed.
End SuccessiveSelection.
