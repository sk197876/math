(** Federer (1969), 2.2.9, p. 65, the displayed finite continued fraction
    whose limit defines the classical map. This module keeps the ordinary
    successive digits; no grouping appears in the definition of a
    convergent. Natural codes represent positive digits by adding one.
    Bell2016, section 2, p. 2, calls these truncations convergents. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ContinuedFractionBranches ContinuedFractionBlocks SequenceSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_continued_fraction]: direct finite
    nested expression displayed in Federer 2.2.9, p. 65.
    A prescribed tail replaces the innermost zero, allowing
    concatenation of prefixes. The empty prefix returns that tail. *)
Fixpoint finite_continued_fraction (R : realType) (a : seq nat) (t : R) : R :=
  if a is j :: s then continued_fraction_branch j (finite_continued_fraction s t) else t.

(** Source for [finite_continued_fraction_cat]: supporting
    concatenation of ordinary digit prefixes in Federer 2.2.9,
    p. 65; it follows directly from the nested expression. *)
Lemma finite_continued_fraction_cat (R : realType) a b (t : R) :
  finite_continued_fraction (a ++ b) t =
  finite_continued_fraction a (finite_continued_fraction b t).
Proof. by elim: a=> [|j a IH] /=; rewrite ?IH. Qed.

(** Source for [finite_continued_fraction_unit]: supporting
    closed-unit-interval bounds for all finite truncations of
    the displayed fraction in Federer 2.2.9, p. 65. *)
Lemma finite_continued_fraction_unit (R : realType) a (t : R) :
  0 <= t -> t <= 1 ->
  0 <= finite_continued_fraction a t /\ finite_continued_fraction a t <= 1.
Proof.
move=> ht ht1; elim: a=> [|j a [hl hu]] /=; first by split.
have [hp h1] := continued_fraction_branch_unit_bounds j hl.
by split; first exact: ltW hp.
Qed.

(** Source for [quadruple_digits]: supporting list of four
    consecutive ordinary digits for the grouping proof associated
    with Federer 2.2.9, p. 65. *)
Definition quadruple_digits (q : (nat * nat) * (nat * nat)) : seq nat :=
  [:: q.1.1; q.1.2; q.2.1; q.2.2].

(** Source for [finite_continued_fraction_block]: supporting
    agreement of the four-digit shorthand with the literal
    nested fraction in Federer 2.2.9, p. 65. *)
Lemma finite_continued_fraction_block (R : realType) q (t : R) :
  finite_continued_fraction (quadruple_digits q) t = continued_fraction_block q t.
Proof. by []. Qed.

(** Source for [continued_fraction_convergent]: direct m-term
    truncation of the fraction displayed in Federer 2.2.9,
    p. 65. For m positive its tail is zero;
    the zero-term value is defined as zero for indexing only. *)
Definition continued_fraction_convergent (R : realType)
    (n : positive_sequence_space R) (m : nat) : R :=
  finite_continued_fraction (map (positive_sequence_coordinates n) (iota 0 m)) 0.
