(** Federer (1969), 2.2.9, p. 65, supporting rational exclusion for the
    continued-fraction cylinders. Positive rational denominators strictly
    descend when outer blocks are removed, so a rational point cannot lie in
    cylinders of every depth. This supplies an arithmetic argument for the
    target being exactly the ordinary irrationals. Bell2016, section 1, p.
    1, gives termination context; Source context:
    ContinuedFractionBranches.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RationalRealUP ContinuedFractionBranches ContinuedFractionBlocks
  ContinuedFractionWords ContinuedFractionRationalBranches ContinuedFractionRationalDescent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continued_fraction_word_interior]: supporting
    strict unit-interval bounds for finite continued fractions
    with an interior tail in Federer 2.2.9, p. 65. *)
Lemma continued_fraction_word_interior (R : realType) d s (t : R) :
  0 < t -> t < 1 ->
  0 < continued_fraction_word d s t /\ continued_fraction_word d s t < 1.
Proof.
elim: s t=> [|j s IH] t ht ht1 /=; first by split.
have [hl hu] := continued_fraction_block_inside (d j) (ltW ht).
exact: IH _ hl hu.
Qed.

(** Source for [continued_fraction_word_rcons]: supporting
    outermost-block removal with the reversed-word convention
    for Federer 2.2.9, p. 65. *)
Lemma continued_fraction_word_rcons (R : realType) d s j (t : R) :
  continued_fraction_word d (rcons s j) t =
  continued_fraction_block (d j) (continued_fraction_word d s t).
Proof. by elim: s t=> [|i s IH] t /=; rewrite ?IH. Qed.

(** Source for [continued_fraction_block_rational]: supporting
    rationality of finite four-digit prefixes with positive
    rational tails in Federer 2.2.9, p. 65. *)
Lemma continued_fraction_block_rational (R : realType) d (t : R) :
  0 < t -> is_rational_real t -> is_rational_real (continued_fraction_block d t).
Proof.
move=> ht hr; case: d=> [[a b] [c d]]; rewrite /continued_fraction_block /=.
have hd := (continued_fraction_branch_unit_bounds d (ltW ht)).1.
have hc := (continued_fraction_branch_unit_bounds c (ltW hd)).1.
have hb := (continued_fraction_branch_unit_bounds b (ltW hc)).1.
apply: continued_fraction_branch_rational hb _.
apply: continued_fraction_branch_rational hc _.
apply: continued_fraction_branch_rational hd _.
exact: continued_fraction_branch_rational ht hr.
Qed.

(** Source for [continued_fraction_word_rational]: supporting
    rationality preservation by any finite prefix in Federer
    2.2.9, p. 65. It ensures that an irrational
    cylinder point has an irrational interior tail. *)
Lemma continued_fraction_word_rational (R : realType) d s (t : R) :
  0 < t -> is_rational_real t -> is_rational_real (continued_fraction_word d s t).
Proof.
elim: s t=> [|j s IH] t ht hr //=.
apply: IH; first exact: (continued_fraction_block_inside (d j) (ltW ht)).1.
exact: continued_fraction_block_rational ht hr.
Qed.

(** Source for [rational_continued_fraction_depth_bound]:
    supporting finite-depth obstruction for Federer 2.2.9,
    p. 65. A rational p/q in (0,1) cannot be
    represented by q or more four-digit blocks with an interior
    tail. The bound is deliberately coarse; strict denominator
    descent suffices, without reduced fractions or growth estimates. *)
Lemma rational_continued_fraction_depth_bound (R : realType) d q :
  forall p s (t : R), (0 < p)%N -> (p < q)%N -> 0 < t -> t < 1 ->
  continued_fraction_word d s t = p%:R / q%:R -> (size s < q)%N.
Proof.
elim/ltn_ind: q=> q IH p s t hp hpq ht ht1.
case/lastP: s=> [|s j] he; first exact: ltn_trans hp hpq.
rewrite continued_fraction_word_rcons in he.
have [hu hu1] := continued_fraction_word_interior d s ht ht1.
have [r [n [hr [hrn [hn htail]]]]] :=
  @continued_fraction_block_rational_descent R (d j) p q _ hp hpq hu hu1 he.
have hsize := IH n hn r s t hr hrn ht ht1 htail.
rewrite size_rcons; exact: leq_ltn_trans hsize hn.
Qed.
