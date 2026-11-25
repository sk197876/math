(** Federer (1969), 2.2.9, p. 65, the limit of the displayed ordinary
    continued-fraction truncations. Every sufficiently long truncation
    shares a prescribed four- digit prefix and has a closed-unit tail. The
    shrinking prefix interval therefore bounds its distance to any point in
    all closed cylinders. No convergence of a mere subsequence is
    substituted for the printed limit. Source context:
    FiniteContinuedFractions.v and ContinuedFractionBranches.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SequenceSpace SequenceTreePrefixes SequenceFourBlocks
  NaturalQuadruplingSealed ContinuedFractionWords ContinuedFractionScale
  FiniteContinuedFractions ContinuedFractionPrefixGrouping ContinuedFractionLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continued_fraction_convergent_tail]: supporting
    decomposition of every truncation beyond a fixed prefix
    in Federer 2.2.9, p. 65. Its remaining
    finite fraction is a tail in the closed unit interval. *)
Lemma continued_fraction_convergent_tail (R : realType)
    (n : positive_sequence_space R) k m :
  (k*4 <= m)%N -> exists t : R, 0 <= t /\ t <= 1 /\
    continued_fraction_convergent n m = continued_fraction_word NaturalQuadrupling.decode
      (sequence_tree_prefix (sequence_group_four n) k) t.
Proof.
move=> hm.
pose t : R := finite_continued_fraction
  (map (positive_sequence_coordinates n) (iota (k*4) (m-k*4))) 0.
have [ht0 ht1] : 0 <= t /\ t <= 1 :=
  finite_continued_fraction_unit _ (lexx 0) ler01.
exists t; split=> //; split=> //.
have he : m = (k*4+(m-k*4))%N by rewrite subnKC.
rewrite /continued_fraction_convergent {1}he iotaD map_cat finite_continued_fraction_cat add0n.
exact: esym (continued_fraction_grouped_prefixE n k t).
Qed.

(** Source for [continued_fraction_cylinder_error]: supporting
    uniform error bound for Federer 2.2.9, p. 65.
    Any closed-unit tail and any point between the same
    prefix endpoints differ by at most sixteen to the negative
    number of four-digit blocks. *)
Lemma continued_fraction_cylinder_error (R : realType) d s (t x : R) :
  0 <= t -> t <= 1 -> continued_fraction_word d s 0 <= x ->
  x <= continued_fraction_word d s 1 ->
  `|continued_fraction_word d s t - x| <= ((16 : R)^+(size s))^-1.
Proof.
move=> ht ht1 hx0 hx1.
have hl := @continued_fraction_word_monotone R d s 0 t (lexx 0) ht.
have hu := @continued_fraction_word_monotone R d s t 1 ht ht1.
have hd : `|continued_fraction_word d s t - x| <=
    continued_fraction_word d s 1 - continued_fraction_word d s 0.
  rewrite ler_norml; apply/andP; split.
  - rewrite opprB; exact: lerB hl hx1.
  - exact: lerB hu hx0.
have hi := @continued_fraction_word_increasing R d s 0 1 (lexx 0) ltr01.
have hc := @continued_fraction_word_contraction R d s 0 1 (lexx 0) ler01.
rewrite subr0 normr1 mul1r ger0_norm ?subr_ge0 ?(ltW hi) // in hc.
exact: le_trans hd hc.
Qed.

(** Source for [continued_fraction_cylinders_give_limit]: direct
    full-sequence convergence required by the classical map in
    Federer 2.2.9, p. 65. Abstract endpoint bounds
    at every grouped level imply the literal ordinary-digit limit. *)
Theorem continued_fraction_cylinders_give_limit (R : realType)
    (f : positive_sequence_space R -> R) :
  (forall n k, (0 < k)%N ->
    continued_fraction_word NaturalQuadrupling.decode
      (sequence_tree_prefix (sequence_group_four n) k) 0 <= f n /\
    f n <= continued_fraction_word NaturalQuadrupling.decode
      (sequence_tree_prefix (sequence_group_four n) k) 1) ->
  is_continued_fraction_map f.
Proof.
move=> hf n e he; have [k [hk hke]] := continued_fraction_scale_small he.
exists (k*4)%N=> m hm.
have [t [ht [ht1 hconv]]] := continued_fraction_convergent_tail n hm.
have [h0 h1] := hf n k hk.
rewrite hconv; apply: le_lt_trans _ hke.
have hh := continued_fraction_cylinder_error ht ht1 h0 h1.
by rewrite sequence_tree_prefix_size in hh.
Qed.
