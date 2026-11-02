(** Private existence proof of the successive finite selections in Federer
    (1969), 2.8.2, pp. 142–143 The state is an open remainder. At each step
    the proved finite-selection theorem supplies the next family, and its
    closed union is removed. Downstream arguments use only the abstract
    exhaustion specification. Source context and the corrected initial empty
    step: ContractionCoverUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP ContractionCoverUP FiniteContractionSelection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section Construction.
Variable R : realType.
Variable X : metricType R.
Variable mu : set X -> \bar R.
Variable hm : is_measure mu.
Variable F : set (set X).
Variable A : nat -> set X.
Variable sigma : nat -> R.
Variable hF : forall B, F B -> closed B.
Variable hopen : forall U, open U -> measure_measurable mu U.
Variable hfinite : forall n, mu (A n) < +oo.
Variable hsigma : forall n, (0 < sigma n < 1)%R.
Variable hlocal : forall n, has_local_cover_contraction mu F (A n) (sigma n).

(** Source for [finite_selection_at_open]: private selection
    of the finite family G_j for an open W_j in Federer
    2.8.2, pp. 142–143. Existence was proved without a
    measurability hypothesis on the target A_j. *)
Definition finite_selection_at_open n (s : {U : set X | open U}) :=
  projT1 (cid (@finite_contraction_cover_selection R X mu hm F (A n) (sigma n)
    hF hopen (hfinite n) (hsigma n) (hlocal n) (sval s) (svalP s))).

(** Source for [finite_selection_at_open_laws]: the selected
    family is finite and satisfies the square-root contraction
    laws, Federer 2.8.2, pp. 142–143. *)
Lemma finite_selection_at_open_laws n (s : {U : set X | open U}) :
  finite_set (finite_selection_at_open n s) /\
  is_contraction_cover_selection mu F (A n) (sval s) (Num.sqrt (sigma n))
    (finite_selection_at_open n s).
Proof.
exact: projT2 (cid (@finite_contraction_cover_selection R X mu hm F (A n) (sigma n)
  hF hopen (hfinite n) (hsigma n) (hlocal n) (sval s) (svalP s))).
Qed.

(** Source for [cover_exhaustion_next_state]: remove the
    finite selected closed union from the current open set,
    Federer 2.8.2, pp. 142–143. The next state's openness
    is proved, not postulated. *)
Definition cover_exhaustion_next_state n (s : {U : set X | open U}) :
    {U : set X | open U} :=
  exist open (sval s `\` \bigcup_(B in finite_selection_at_open n s) B)
    (@finite_selection_open_remainder R X mu F (A n) (sval s)
      (Num.sqrt (sigma n)) (finite_selection_at_open n s) hF
      (finite_selection_at_open_laws n s).1 (finite_selection_at_open_laws n s).2 (svalP s)).

Variable V : set X.
Variable hV : open V.

(** Source for [cover_exhaustion_state]: inductive open
    remainders of Federer 2.8.2, pp. 142–143. Index zero
    begins after the initial empty selection, as explained in
    ContractionCoverUP.v with the erratum p. 3, book p. 142 line 33. *)
Fixpoint cover_exhaustion_state n : {U : set X | open U} :=
  match n with
  | 0%N => exist open V hV
  | m.+1 => cover_exhaustion_next_state m (cover_exhaustion_state m)
  end.

(** Source for [cover_contraction_exhaustion_exists]: proved existence of
    the finite-selection exhaustion in Federer 2.8.2, pp. 142–143 This is
    the private witness theorem behind the sealed interface; no
    implementation is exported downstream. *)
Theorem cover_contraction_exhaustion_exists : exists W G,
  is_cover_contraction_exhaustion mu F A (fun n => Num.sqrt (sigma n)) V W G.
Proof.
exists (fun n => sval (cover_exhaustion_state n)),
  (fun n => finite_selection_at_open n (cover_exhaustion_state n)); constructor.
- by [].
- move=> n; exact: svalP.
- move=> n; exact: (finite_selection_at_open_laws n (cover_exhaustion_state n)).1.
- move=> n; exact: (finite_selection_at_open_laws n (cover_exhaustion_state n)).2.
- by move=> n.
Qed.
End Construction.
