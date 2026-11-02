(** Finite combinatorics supporting the binary-cylinder example for Federer
    (1969), 2.3.8, p. 78. A word of length k has exactly 2^(n-k) extensions
    to length n. This verifies the elementary cylinder costs for the
    covering construction of 2.10.1, p. 170. Source context:
    MeasurableNormedFunctionUP.v. *)
From mathcomp Require Import all_boot.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [binary_word_extend]: concatenate a prescribed
    prefix with a free suffix, supporting the finite counting
    argument in the local Federer 2.3.8 counterexample. *)
Definition binary_word_extend n (w : seq bool) (h : size w <= n)
    (v : (n-size w).-tuple bool) : n.-tuple bool.
Proof.
apply: (@Tuple n bool (w ++ v)).
by rewrite size_cat size_tuple addnC subnK.
Defined.

(** Source for [binary_word_extend_injective]: distinct suffixes
    give distinct extensions, supporting the cylinder-cost calculation
    for Federer 2.3.8, p. 78. *)
Lemma binary_word_extend_injective n (w : seq bool) (h : size w <= n) :
  injective (@binary_word_extend n w h).
Proof.
move=> u v he; apply: val_inj.
have hc := congr1 val he; change (w ++ u = w ++ v) in hc.
have := congr1 (drop (size w)) hc.
by rewrite !drop_size_cat.
Qed.

(** Source for [binary_word_extend_prefix]: a concatenated word
    has the prescribed prefix, supporting the local example for
    Federer 2.3.8, p. 78. *)
Lemma binary_word_extend_prefix n (w : seq bool) (h : size w <= n)
    (v : (n-size w).-tuple bool) : prefix w (binary_word_extend h v).
Proof. change (prefix w (w ++ v)); exact: prefix_prefix. Qed.

(** Source for [binary_word_prefix_card]: the number of length-n
    binary words with a prescribed prefix w is 2^(n-size w),
    supporting the finite cylinder-cover estimate for Federer
    2.3.8, p. 78. This is local finite combinatorics. *)
Lemma binary_word_prefix_card n (w : seq bool) (h : size w <= n) :
  #|[pred u : n.-tuple bool | prefix w u]| = 2 ^ (n-size w).
Proof.
have he : [pred u : n.-tuple bool | prefix w u] =i
    [set binary_word_extend h v | v : (n-size w).-tuple bool].
  move=> u; apply/idP/imsetP.
  - move=> hp.
    have hv : size (drop (size w) u) == n-size w by rewrite size_drop size_tuple.
    exists (Tuple hv); first by rewrite inE.
    apply: val_inj; change (val u = w ++ drop (size w) u).
    have hp' : prefix w u := hp.
    have hpw : take (size w) u = w by move: hp'; rewrite prefixE=> /eqP.
    have hc := cat_take_drop (size w) u; rewrite hpw in hc; exact: esym hc.
  - move=> [v _ ->]; exact: binary_word_extend_prefix.
rewrite (eq_card he) card_imset; last exact: binary_word_extend_injective.
by rewrite card_tuple card_bool.
Qed.
