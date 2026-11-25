(** Opaque exhaustion witness for Federer (1969), 2.8.2, pp. 142–143. Source
    context, square-root factors and the corrected initial-index convention:
    ContractionCoverUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP ContractionCoverUP
  CoverContractionExhaustionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Module Type CoverContractionExhaustionSignature.
(** Source for [value]: the open remainders and finite
    selected families of Federer 2.8.2, pp. 142–143,
    exposed only through their abstract exhaustion laws. *)
Parameter value : forall (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (F : set (set X)) (A : nat -> set X) (sigma : nat -> R),
  (forall B, F B -> closed B) ->
  (forall U, open U -> measure_measurable mu U) ->
  (forall n, mu (A n) < +oo) ->
  (forall n, (0 < sigma n < 1)%R) ->
  (forall n, has_local_cover_contraction mu F (A n) (sigma n)) ->
  forall V : set X, open V -> ((nat -> set X) * (nat -> set (set X)))%type.
(** Source for [laws]: eligibility, finite disjoint selections,
    open remainders and contraction bounds in the construction
    of Federer 2.8.2, pp. 142–143. *)
Parameter laws : forall (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (F : set (set X)) (A : nat -> set X) (sigma : nat -> R)
    (hF : forall B, F B -> closed B)
    (ho : forall U, open U -> measure_measurable mu U)
    (hf : forall n, mu (A n) < +oo)
    (hs : forall n, (0 < sigma n < 1)%R)
    (hl : forall n, has_local_cover_contraction mu F (A n) (sigma n))
    (V : set X) (hV : open V),
  let p := @value R X mu hm F A sigma hF ho hf hs hl V hV in
  is_cover_contraction_exhaustion mu F A (fun n => Num.sqrt (sigma n)) V p.1 p.2.
End CoverContractionExhaustionSignature.

Module CoverContractionExhaustion : CoverContractionExhaustionSignature.
(** Source for [value]: private choice of the proved
    exhaustion witness in Federer 2.8.2, pp. 142–143.
    Both selected sequences are hidden by opaque ascription. *)
Definition value (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (F : set (set X)) (A : nat -> set X) (sigma : nat -> R)
    (hF : forall B, F B -> closed B)
    (ho : forall U, open U -> measure_measurable mu U)
    (hf : forall n, mu (A n) < +oo)
    (hs : forall n, (0 < sigma n < 1)%R)
    (hl : forall n, has_local_cover_contraction mu F (A n) (sigma n))
    (V : set X) (hV : open V) :=
  let h := @cover_contraction_exhaustion_exists R X mu hm F A sigma hF ho hf hs hl V hV in
  (projT1 (cid h), projT1 (cid (projT2 (cid h)))).
(** Source for [laws]: the selected witness satisfies the
    abstract specification for Federer 2.8.2, pp. 142–143. *)
Lemma laws (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (F : set (set X)) (A : nat -> set X) (sigma : nat -> R)
    (hF : forall B, F B -> closed B)
    (ho : forall U, open U -> measure_measurable mu U)
    (hf : forall n, mu (A n) < +oo)
    (hs : forall n, (0 < sigma n < 1)%R)
    (hl : forall n, has_local_cover_contraction mu F (A n) (sigma n))
    (V : set X) (hV : open V) :
  let p := @value R X mu hm F A sigma hF ho hf hs hl V hV in
  is_cover_contraction_exhaustion mu F A (fun n => Num.sqrt (sigma n)) V p.1 p.2.
Proof.
exact: projT2 (cid (projT2 (cid (@cover_contraction_exhaustion_exists
  R X mu hm F A sigma hF ho hf hs hl V hV)))).
Qed.
End CoverContractionExhaustion.
