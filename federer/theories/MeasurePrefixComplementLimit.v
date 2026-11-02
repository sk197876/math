(** Federer (1969), 2.2.2, p. 61, second displayed limit in the
    closed-approximation proof. This restriction is essential: the set A
    below need not itself be measurable. Source context:
    ClosedApproximationUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit MeasureUP MeasureBasic
  MeasureRestriction MeasureFiniteClosure MeasureSequencePrefixes
  MeasureContinuityAbove SetSequenceDisjointification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_prefix_complement_limit]: Federer
    2.2.2, p. 61, supporting limit for an arbitrary A minus
    increasing finite unions of measurable C_n. Finiteness of the
    whole measure permits decreasing continuity after restriction
    to A; no measurability hypothesis on A is introduced. *)
Theorem measure_prefix_complement_limit (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (A : set I) (C : nat -> set I) :
  mu setT < +oo -> (forall n, measure_measurable mu (C n)) ->
  extended_decreases_to (fun n => mu (A `\` set_sequence_prefix C n))
    (mu (A `\` \bigcup_n C n)).
Proof.
move=> hf hC; pose nu := measure_restrict mu A.
pose E n := ~` set_sequence_prefix C n.
have hn : is_measure nu := measure_restrict_is_measure hm A.
have hE n : measure_measurable nu (E n).
  apply: (@measure_restrict_measurable R I mu A (E n)).
  apply: (@measure_measurable_complement R I mu).
  exact: (@measure_sequence_prefix_measurable R I mu hm C hC n).
have hmono n m : (n <= m)%N -> E m `<=` E n.
  move=> hnm x hx hn0; apply: hx.
  exact: (@set_sequence_prefix_mono I C n m hnm x hn0).
have hfin : nu (E 0%N) < +oo.
  rewrite /nu /E /measure_restrict set_sequence_prefix_zero setC0 setIT.
  apply: le_lt_trans _ hf; apply: (@measure_mono R I mu hm A setT)=> x _; exact Logic.I.
have hlim := @measure_continuity_above R I nu hn E hE hmono hfin.
have he : (\bigcap_n E n) = ~` (\bigcup_n C n).
  apply/seteqP; split.
  - move=> x hx [n _ hcn]; apply: (hx n.+1 Logic.I).
    exists n=> //; exact: ltnSn.
  - move=> x hx n _ [k _ hck]; apply: hx; by exists k.
rewrite he /nu /measure_restrict /E -!setDE in hlim.
exact hlim.
Qed.
