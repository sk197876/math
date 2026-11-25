(** Federer (1969), 2.2.9, p. 65, exact target of the classical
    continued-fraction homeomorphism. We identify the intersection of
    positive cylinder levels with the ordinary irrational points of (0,1).
    The two directions use the proved rational denominator descent and
    irrational Gauss step. Bell2016, section 1 and Theorem 2, pp. 1 and 5,
    gives the corresponding scalar and cylinder background. Source context:
    ContinuedFractionBranches.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RationalRealUP RealMetricBackground ContinuedFractionBlocks
  ContinuedFractionWords ContinuedFractionContinuity ContinuedFractionTreeConstruction
  ContinuedFractionGaussStep ContinuedFractionWordRationality OpenEmbeddingBorelImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continued_fraction_cylinder_tail]: supporting
    tail recovery in a non-root open cylinder of the continued
    fraction in Federer 2.2.9, p. 65. *)
Lemma continued_fraction_cylinder_tail (R : realType) d s (x : R) :
  s != [::] -> @continued_fraction_tree R d s x ->
  exists t : R, 0 < t /\ t < 1 /\ continued_fraction_word d s t = x.
Proof.
case: s=> [|j s] //= _ [hl hu].
exact (@continued_fraction_word_interval_image R d (j::s) x hl hu).
Qed.

(** Source for [continued_fraction_cylinder_unit]: supporting
    containment of every non-root cylinder in (0,1) for
    Federer 2.2.9, p. 65. *)
Lemma continued_fraction_cylinder_unit (R : realType) d s (x : R) :
  s != [::] -> @continued_fraction_tree R d s x -> 0 < x /\ x < 1.
Proof.
move=> hs hx; have [t [ht [ht1 <-]]] := continued_fraction_cylinder_tail hs hx.
exact (@continued_fraction_word_interior R d s t ht ht1).
Qed.

(** Source for [continued_fraction_tree_image_irrational]: direct
    irrational-target inclusion for the map mentioned in Federer
    2.2.9, p. 65. A rational p/q cannot lie
    in a cylinder of depth q+1, by natural denominator descent. *)
Lemma continued_fraction_tree_image_irrational (R : realType) d :
  open_embedding_image (@continued_fraction_tree R d) `<=` irrational_unit_interval.
Proof.
move=> x hx; have [s hs hxs] := hx 0%N Logic.I.
have hs0 : s != [::] by apply/eqP=> he; by rewrite he in hs.
have [hx0 hx1] := continued_fraction_cylinder_unit hs0 hxs.
split=> //; split=> // hr.
have [p [q [hp [hq he]]]] := positive_rational_natural_quotient hx0 hr.
have hqR : (0 : R) < q%:R by rewrite ltr0n.
have hpq : (p < q)%N by move: hx1; rewrite he ltr_pdivrMr // mul1r ltr_nat.
have [w hw hxw] := hx q Logic.I.
have hw0 : w != [::] by apply/eqP=> hew; by rewrite hew in hw.
have [t [ht [ht1 hft]]] := continued_fraction_cylinder_tail hw0 hxw.
have hdepth := @rational_continued_fraction_depth_bound R d q p w t hp hpq ht ht1
  (eq_trans hft he).
by move: hdepth; rewrite hw ltnNge leqnSn.
Qed.

(** Source for [irrational_continued_fraction_cylinder_tail]:
    supporting irrationality of an interior tail when the
    represented cylinder point is irrational, Federer 2.2.9,
    p. 65. The root uses the point itself as tail. *)
Lemma irrational_continued_fraction_cylinder_tail (R : realType) d s (x : R) :
  irrational_unit_interval x -> @continued_fraction_tree R d s x ->
  exists t : R, irrational_unit_interval t /\ continued_fraction_word d s t = x.
Proof.
move=> hx; case: s=> [|j s] hxs; first by exists x.
have [t [ht [ht1 he]]] := @continued_fraction_cylinder_tail R d (j::s) x (erefl true) hxs.
exists t; split=> //; split=> //; split=> // hr.
apply: hx.2.2; rewrite -he; exact: continued_fraction_word_rational ht hr.
Qed.

(** Source for [irrational_continued_fraction_tree_image]: direct
    irrational-target surjectivity for Federer 2.2.9, p. 65.
    At every finite depth, four irrational Gauss steps supply
    a child cylinder containing the point. Surjective block
    coding is the only requirement on the index enumeration. *)
Lemma irrational_continued_fraction_tree_image (R : realType) d :
  (forall q, exists j, d j = q) ->
  irrational_unit_interval `<=` open_embedding_image (@continued_fraction_tree R d).
Proof.
move=> hd x hx.
have levels k : exists s : seq nat, size s = k /\ continued_fraction_tree d s x.
  elim: k=> [|k [s [hs hxs]]]; first by exists [::]; split.
  have [t [ht he]] := irrational_continued_fraction_cylinder_tail hx hxs.
  have [q [u [hu heq]]] := irrational_continued_fraction_four_steps ht.
  have [j hj] := hd q.
  exists (j::s); split; first by rewrite /= hs.
  change (continued_fraction_word d (j::s) 0 < x /\ x < continued_fraction_word d (j::s) 1).
  have hux : continued_fraction_word d (j::s) u = x by rewrite /= hj -heq he.
  rewrite -hux; split.
  - exact (@continued_fraction_word_increasing R d (j::s) 0 u (lexx 0) hu.1).
  - exact (@continued_fraction_word_increasing R d (j::s) u 1 (ltW hu.1) hu.2.1).
move=> k _; have [s [hs hxs]] := levels k.+1.
by exists s.
Qed.

(** Source for [continued_fraction_tree_image]: direct exact
    image identification for the classical continued fraction
    in Federer 2.2.9, p. 65. *)
Theorem continued_fraction_tree_image (R : realType) d :
  (forall q, exists j, d j = q) ->
  open_embedding_image (@continued_fraction_tree R d) = irrational_unit_interval.
Proof.
move=> hd; apply/seteqP; split.
- exact: continued_fraction_tree_image_irrational.
- exact: irrational_continued_fraction_tree_image hd.
Qed.
