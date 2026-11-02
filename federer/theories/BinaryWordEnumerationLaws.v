(** Finite sets of short words and the two enumeration properties for the
    local counterexample to Federer (1969), 2.3.8, p. 78. Eventually every
    enumerated cylinder has long prefix, but every infinite sequence belongs
    to arbitrarily late cylinders. *)
From mathcomp Require Import all_boot finmap boolp classical_sets cardinality.
From Federer Require Import NonnegativeSumContinuity BinarySequenceCylinders BinaryCylinderPrefixLaws
  BinaryWordEnumerationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.

(** Source for [short_binary_words_finite]: there are only
    finitely many binary words of bounded length, set-theoretic
    infrastructure for the example in Federer 2.3.8, p. 78. *)
Lemma short_binary_words_finite k : finite_set [set w : seq bool | size w <= k].
Proof.
pose E (i : 'I_k.+1) : set (seq bool) := (fun u : (val i).-tuple bool => val u) @` setT.
have hE i : finite_set (E i) := finite_image _ finite_finset.
have hf : finite_set (\bigcup_(i : 'I_k.+1) E i).
  apply: bigcup_finite; first exact: finite_finset.
  by move=> i _.
apply: sub_finite_set _ hf=> w hw.
have hi : size w < k.+1 by rewrite ltnS.
exists (Ordinal hi); first exact Logic.I.
exists (@Tuple (size w) bool w (eqxx _)); by [].
Qed.

(** Source for [finite_natural_set_upper_bound]: a finite
    set of natural indices has a strict upper bound, general
    set theory supporting Federer 2.3.8, p. 78. *)
Lemma finite_natural_set_upper_bound (A : set nat) : finite_set A ->
  exists K, forall n, A n -> n < K.
Proof.
move=> /finite_fsetP [F hF].
have [K hK] : exists K, forall n, n \in F -> n < K.
  apply: (@finite_increasing_cover [the eqType of (nat : Type)] (fun K => [set n | n < K]) F).
  - move=> K L hKL n hn; exact: leq_trans hn hKL.
  - move=> n hn; exists n.+1; exact: ltnSn.
exists K=> n hn; apply: hK; by move: hn; rewrite hF.
Qed.

Section Enumeration.
Variables (encode : seq bool -> nat) (decode : nat -> seq bool).
Hypothesis he : is_binary_word_enumeration encode decode.

(** Source for [binary_enumeration_lengths_escape]: the lengths
    of enumerated words eventually exceed each fixed bound,
    supporting convergence in measure in the local example for
    Federer 2.3.8, p. 78. *)
Lemma binary_enumeration_lengths_escape k : exists K,
  forall n, K <= n -> k < size (decode n).
Proof.
have hf : finite_set (encode @` [set w : seq bool | size w <= k]).
  exact: finite_image _ (short_binary_words_finite k).
have [K hK] := finite_natural_set_upper_bound hf; exists K=> n hn.
rewrite ltnNge; apply/negP=> hk.
have hc : (encode @` [set w : seq bool | size w <= k]) n.
  exists (decode n)=> //; exact: he.2.
have := leq_ltn_trans hn (hK n hc); by rewrite ltnn.
Qed.

(** Source for [binary_enumeration_late_membership]: each binary
    sequence lies in a cylinder at an arbitrarily late enumeration
    index. This supplies failure of pointwise convergence to zero
    in the local counterexample to Federer 2.3.8, p. 78. *)
Lemma binary_enumeration_late_membership (x : binary_sequence_space) K :
  exists n, K <= n /\ binary_cylinder (decode n) x.
Proof.
have hf : finite_set ((fun n => size (decode n)) @` `I_K).
  exact: finite_image _ (finite_II K).
have [M hM] := finite_natural_set_upper_bound hf.
pose w := val (binary_sequence_prefix M x).
exists (encode w); split.
- rewrite leqNgt; apply/negP=> hn.
  have hc : ((fun n => size (decode n)) @` `I_K) (size w).
    exists (encode w)=> //; by rewrite he.1.
  have hh := hM (size w) hc; by rewrite /w size_tuple ltnn in hh.
- rewrite he.1; exact: binary_sequence_in_prefix.
Qed.
End Enumeration.
