(** Public finite-selection exhaustion interface supporting Federer (1969),
    2.8.2, pp. 142–143. Source context and exact specification:
    ContractionCoverUP.v. The state recursion and finite-choice
    implementation are sealed. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP ContractionCoverUP CoverContractionExhaustionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section Interface.
Variable R : realType.
Variable X : metricType R.
Variable mu : set X -> \bar R.
Variable hm : is_measure mu.
Variable F : set (set X).
Variable A : nat -> set X.
Variable sigma : nat -> R.
Variable hF : forall B, F B -> closed B.
Variable ho : forall U, open U -> measure_measurable mu U.
Variable hf : forall n, mu (A n) < +oo.
Variable hs : forall n, (0 < sigma n < 1)%R.
Variable hl : forall n, has_local_cover_contraction mu F (A n) (sigma n).
Variable V : set X.
Variable hV : open V.

(** Source for [cover_contraction_exhaustion]: the two
    sequences chosen in Federer 2.8.2, pp. 142–143,
    supplied through their sealed abstract laws. *)
Definition cover_contraction_exhaustion :=
  @CoverContractionExhaustion.value R X mu hm F A sigma hF ho hf hs hl V hV.

(** Source for [cover_contraction_exhaustion_specification]:
    the finite-selection and remainder laws of Federer
    2.8.2, pp. 142–143. *)
Theorem cover_contraction_exhaustion_specification :
  is_cover_contraction_exhaustion mu F A (fun n => Num.sqrt (sigma n)) V
    cover_contraction_exhaustion.1 cover_contraction_exhaustion.2.
Proof. exact: CoverContractionExhaustion.laws. Qed.
End Interface.
