(** Federer (1969), 2.2.9, p. 65: interval cylinders for the particular
    continued-fraction map, grouped four digits at a time to satisfy the
    existing open-tree laws. The root is the real line as those laws
    require; all positive levels lie in (0,1). This is a supporting
    construction for the final comparison, not the earlier co-countable
    real-line embedding. Source context and cylinder references:
    ContinuedFractionBranches.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import RealMetricBackground RealOpenIntervals ClosedCoverTreeUP OpenEmbeddingTreeUP
  ContinuedFractionBlocks ContinuedFractionWords ContinuedFractionContinuity
  ContinuedFractionDigits ContinuedFractionScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continued_fraction_tree]: supporting open
    cylinders for the classical continued fraction in Federer
    2.2.9, p. 65. A nonempty word denotes the
    interval between the finite-prefix values at zero and one. *)
Definition continued_fraction_tree (R : realType)
    (d : nat -> (nat * nat) * (nat * nat)) (s : seq nat) :
    set (real_line_metric R) :=
  if s is _ :: _ then real_open_interval
    (continued_fraction_word d s 0) (continued_fraction_word d s 1)
  else setT.

(** Source for [continued_fraction_tree_open]: supporting
    openness of the continued-fraction cylinders in Federer
    2.2.9, p. 65, including the whole-space root. *)
Lemma continued_fraction_tree_open (R : realType) d s :
  open (@continued_fraction_tree R d s).
Proof. case: s=> [|j s]; [exact: openT | exact: real_open_interval_open]. Qed.

(** Source for [continued_fraction_tree_nonempty]: supporting
    nonemptiness of each cylinder in Federer 2.2.9, p. 65.
    Strictly increasing even prefixes have distinct endpoint values. *)
Lemma continued_fraction_tree_nonempty (R : realType) d s :
  @continued_fraction_tree R d s !=set0.
Proof.
case: s=> [|j s]; first by exists (0 : R).
apply: real_open_interval_nonempty.
exact (@continued_fraction_word_increasing R d (j::s) 0 1 (lexx 0) ltr01).
Qed.

(** Source for [continued_fraction_tree_child_inside]: supporting
    strict containment of each child closure in its open parent
    for Federer 2.2.9, p. 65. Four positive digits
    send both closed unit endpoints strictly inside (0,1). *)
Lemma continued_fraction_tree_child_inside (R : realType) d s j :
  closure (@continued_fraction_tree R d (j::s)) `<=` continued_fraction_tree d s.
Proof.
move=> x hx; case: s hx=> [|i s] hx; first exact Logic.I.
have [hl hu] := real_open_interval_closure_bounds hx.
change (continued_fraction_word d (i::s) 0 < x /\ x < continued_fraction_word d (i::s) 1).
split.
- have hb := (continued_fraction_block_inside (d j) (lexx (0 : R))).1.
  have hh := continued_fraction_word_increasing d (i::s) (lexx 0) hb.
  exact: lt_le_trans hh hl.
- have [hb0 hb1] := continued_fraction_block_inside (d j) (ler01 : (0 : R) <= 1).
  have hh := continued_fraction_word_increasing d (i::s) (ltW hb0) hb1.
  exact: le_lt_trans hu hh.
Qed.

(** Source for [continued_fraction_tree_siblings]: supporting
    disjointness of open sibling cylinders for Federer 2.2.9,
    p. 65. Injective digit coding, finite-prefix
    injectivity and uniqueness of the four recovered digits suffice;
    closures may share rational endpoints. *)
Lemma continued_fraction_tree_siblings (R : realType) d :
  injective d -> forall s i j, i <> j ->
  @continued_fraction_tree R d (i::s) `&` continued_fraction_tree d (j::s) = set0.
Proof.
move=> hd s i j hij; apply/seteqP; split; last by move=> x [].
move=> x [[hix0 hix1] [hjx0 hjx1]].
have [u [hu [hu1 heu]]] := continued_fraction_word_interval_image hix0 hix1.
have [v [hv [hv1 hev]]] := continued_fraction_word_interval_image hjx0 hjx1.
have hbu := ltW (continued_fraction_block_inside (d i) (ltW hu)).1.
have hbv := ltW (continued_fraction_block_inside (d j) (ltW hv)).1.
have he : continued_fraction_block (d i) u = continued_fraction_block (d j) v.
  apply: (@continued_fraction_word_injective R d s _ _ hbu hbv).
  exact: eq_trans heu (esym hev).
have [hij' _] := continued_fraction_block_unique hu hu1 hv hv1 he.
exact: hij (hd _ _ hij').
Qed.

(** Source for [continued_fraction_tree_diameter]: supporting
    strict shrinking bound in Federer 2.2.9, p. 65,
    obtained from the explicit four-digit contraction. *)
Lemma continued_fraction_tree_diameter (R : realType) d s :
  s != [::] -> forall x y,
  closure (@continued_fraction_tree R d s) x -> closure (continued_fraction_tree d s) y ->
  mdist x y < @closed_cover_tree_scale R (size s).
Proof.
case: s=> [|j s] //= _ x y hx hy.
have hdist := real_open_interval_diameter_bound hx hy.
have hinc := @continued_fraction_word_increasing R d (j::s) 0 1 (lexx 0) ltr01.
have hc := @continued_fraction_word_contraction R d (j::s) 0 1 (lexx 0) ler01.
rewrite subr0 normr1 mul1r ger0_norm ?subr_ge0 ?(ltW hinc) // in hc.
apply: le_lt_trans hdist _; apply: le_lt_trans hc _.
exact: continued_fraction_tree_scale (ltn0Sn _).
Qed.

(** Source for [continued_fraction_tree_laws]: supporting
    verification that the continued-fraction cylinders satisfy
    the abstract tree of Federer 2.2.9, p. 65.
    This allows the existing sealed branch-map existence theorem
    to be reused without identifying its private construction. *)
Theorem continued_fraction_tree_laws (R : realType) d :
  injective d -> is_open_embedding_tree (@continued_fraction_tree R d).
Proof.
move=> hd; constructor; first by [].
- exact: continued_fraction_tree_open.
- exact: continued_fraction_tree_nonempty.
- exact: continued_fraction_tree_child_inside.
- exact: continued_fraction_tree_siblings hd.
- exact: continued_fraction_tree_diameter.
Qed.
