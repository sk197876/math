(** Federer (1969), 2.7.17, printed p. 141: "This construction was used by
    Vitali (with G = R/Z, S = Q/Z) in the first discovery of a nonmeasurable
    set." This file formalises the example. The additive group of R is a
    topological group, and Z is a closed subgroup. The group R/Z is
    specified, as in CosetSpaceUP.v, by its projection pi: R -> R/Z onto the
    space of cosets x + Z with the quotient topology, together with an
    addition and a negation characterised by pi(x) + pi(y) = pi(x + y) and
    -pi(x) = pi(-x); such a structure exists (the space is the sealed coset
    space of CosetSpace.v, the operations are obtained by choosing
    representatives). Every such R/Z is a compact Hausdorff topological
    group: the addition is continuous on R/Z x R/Z because pi is open
    (2.7.1, p. 122), and R/Z = pi[[0,1]]. Its subgroup S = Q/Z = pi[Q] is
    countable and infinite, since the points pi(1/(n+2)) are distinct. By
    2.7.17 (CompactGroupNonmeasurable.v), R/Z has a Haar measure and a
    subset that is nonmeasurable with respect to every Haar measure of R/Z.
    Federer refers to Vitali's discovery without details; Vitali's set lies
    in R and is nonmeasurable for Lebesgue measure, which is not treated
    here. The local erratum has no entry for 2.7.17. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology normedtype.
From Federer Require Import TopologicalGroupUP TopologicalGroupLaws CosetSpaceUP CosetSpaceLaws
  CosetSpace MeasureUP HaarIntegralUP CompactGroupNonmeasurable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RealAdditiveGroup.
Variable R : realType.

(** Source for [real_integers]: the subgroup Z of R in "G = R/Z",
    Federer 2.7.17, p. 141. Definition: the set of the integer
    multiples k 1 of 1 in R, k in Z. *)
Definition real_integers : set R := [set x | exists k : int, x = k%:~R].

(** Source for [real_rationals]: the subgroup Q of R in "S = Q/Z",
    Federer 2.7.17, p. 141. Definition: the image of the rational
    numbers in R. *)
Definition real_rationals : set R := [set x | exists q : rat, x = ratr q].

(** Source for [real_additive_topological_group]: the topological group
    R underlying "G = R/Z", Federer 2.7.17, p. 141, in the sense of
    2.7.1, p. 121. Supporting lemma: addition and negation are
    continuous. *)
Lemma real_additive_topological_group : is_topological_group (+%R : R -> R -> R) -%R 0.
Proof.
constructor.
- by constructor; [exact: addrA|exact: add0r|exact: addNr].
- exact: add_continuous.
- exact: opp_continuous.
Qed.

(** Source for [real_integers_subgroup]: Z is a subgroup of R, for
    "G = R/Z", Federer 2.7.17, p. 141. Supporting lemma. *)
Lemma real_integers_subgroup : is_subgroup (+%R : R -> R -> R) -%R 0 real_integers.
Proof.
constructor.
- by exists 0; rewrite mulr0z.
- by move=> x y [k ->] [l ->]; exists (k + l); rewrite intrD.
- by move=> x [k ->]; exists (- k); rewrite mulrNz.
Qed.

(** Source for [real_integers_not_between]: no integer lies strictly
    between consecutive integers k and k + 1; supporting the closedness
    of Z for "G = R/Z", Federer 2.7.17, p. 141. *)
Lemma real_integers_not_between (k m : int) : k%:~R < m%:~R :> R -> m%:~R < (k + 1)%:~R :> R -> False.
Proof.
rewrite !ltr_int ltzD1=> hkm hmk.
by move: (lt_le_trans hkm hmk); rewrite ltxx.
Qed.

(** Source for [real_integers_closed]: Z is closed in R, so
    that R/Z is Hausdorff (2.7.1, p. 122), for "G = R/Z", Federer
    2.7.17, p. 141. Supporting lemma: the complement of Z is the union
    of the open intervals ]k, k + 1[ with k in Z. *)
Lemma real_integers_closed : closed real_integers.
Proof.
rewrite -openC.
have -> : ~` real_integers = \bigcup_(k in [set: int]) `]k%:~R, (k + 1)%:~R[%classic.
  apply/seteqP; split=> x /=.
  - move=> hx; exists (Num.floor x)=> //=; rewrite in_itv /=.
    have /andP[h1 h2] := floor_itv x; rewrite h2 andbT lt_def h1 andbT.
    by apply/eqP=> hfx; apply: hx; exists (Num.floor x).
  - case=> k _; rewrite /= in_itv /= => /andP[h1 h2] [m hm].
    by rewrite hm in h1 h2; exact: real_integers_not_between h1 h2.
by apply: bigcup_open=> k _; exact: itv_open.
Qed.

(** Source for [real_integers_small]: an integer of absolute value less
    than 1 is 0; supporting the infinitude of Q/Z in "S = Q/Z", Federer
    2.7.17, p. 141. *)
Lemma real_integers_small (x : R) : real_integers x -> `|x| < 1 -> x = 0.
Proof.
case=> k ->; rewrite -intr_norm ltrz1=> hk.
have : `|k| <= 0 by rewrite -ltzD1 add0r.
by rewrite normr_le0=> /eqP ->; rewrite mulr0z.
Qed.

End RealAdditiveGroup.

(** Source for [is_real_integer_quotient_group]: the group "G = R/Z" of
    Federer 2.7.17, p. 141. Definition: pi: R -> R/Z specifies the
    space of left cosets x + Z with its quotient topology in the sense
    of CosetSpaceUP.v (2.7.1, p. 122), and the addition and negation of
    R/Z satisfy pi(x) + pi(y) = pi(x + y) and -pi(x) = pi(-x) whenever
    x, y in R. These laws determine the operations, since pi is onto. *)
Record is_real_integer_quotient_group (R : realType) (Q : topologicalType) (pi : R -> Q)
    (qadd : Q -> Q -> Q) (qopp : Q -> Q) : Prop := {
  (** Source for [real_quotient_coset_space]: R/Z is the space of the
      cosets x + Z, Federer 2.7.17, p. 141, with 2.7.1, p. 122. *)
  real_quotient_coset_space : is_left_coset_space (+%R : R -> R -> R) -%R (@real_integers R) pi;
  (** Source for [real_quotient_add]: the addition of R/Z, Federer
      2.7.17, p. 141: pi(x) + pi(y) = pi(x + y). *)
  real_quotient_add : forall x y, qadd (pi x) (pi y) = pi (x + y);
  (** Source for [real_quotient_opp]: the negation of R/Z, Federer
      2.7.17, p. 141: -pi(x) = pi(-x). *)
  real_quotient_opp : forall x, qopp (pi x) = pi (- x)
}.

(** Source for [real_integer_quotient_operations_unique]: the group
    "G = R/Z" of Federer 2.7.17, p. 141. Supporting lemma: for a given
    projection pi, the laws of is_real_integer_quotient_group determine
    the addition and the negation of R/Z, since pi is onto. *)
Lemma real_integer_quotient_operations_unique (R : realType) (Q : topologicalType) (pi : R -> Q)
    (qadd qadd' : Q -> Q -> Q) (qopp qopp' : Q -> Q) :
  is_real_integer_quotient_group pi qadd qopp -> is_real_integer_quotient_group pi qadd' qopp' ->
  qadd = qadd' /\ qopp = qopp'.
Proof.
move=> h h'; have hon := coset_projection_onto (real_quotient_coset_space h).
split.
- apply: funext=> p; apply: funext=> q; have [x <-] := hon p; have [y <-] := hon q.
  by rewrite (real_quotient_add h) (real_quotient_add h').
- by apply: funext=> q; have [x <-] := hon q; rewrite (real_quotient_opp h) (real_quotient_opp h').
Qed.

(** Source for [real_integer_quotient_group_exists]: existence of the
    group "G = R/Z" of Federer 2.7.17, p. 141. Existence proof: the
    space is the coset space of CosetSpace.v (2.7.1, p. 122), and the
    operations are pi(a) + pi(b) and pi(-a) for chosen representatives
    a, b; they are independent of the choice because Z is a subgroup. *)
Theorem real_integer_quotient_group_exists (R : realType) :
  exists (Q : topologicalType) (pi : R -> Q) (qadd : Q -> Q -> Q) (qopp : Q -> Q),
    is_real_integer_quotient_group pi qadd qopp.
Proof.
have hZ := real_integers_subgroup R.
have hQ := coset_space_specification (topological_group_laws (real_additive_topological_group R)) hZ.
pose rep q := projT1 (cid (coset_projection_onto hQ q)).
have hrep q : coset_projection +%R (@real_integers R) (rep q) = q.
  exact: projT2 (cid (coset_projection_onto hQ q)).
exists (coset_space +%R (@real_integers R)), (coset_projection +%R (@real_integers R)).
exists (fun p q => coset_projection +%R (@real_integers R) (rep p + rep q)).
exists (fun q => coset_projection +%R (@real_integers R) (- rep q)).
split=> // [x y|x].
- apply/(coset_projection_eq hQ).
  have /(coset_projection_eq hQ) hx := hrep (coset_projection +%R (@real_integers R) x).
  have /(coset_projection_eq hQ) hy := hrep (coset_projection +%R (@real_integers R) y).
  by have := subgroup_mul hZ hx hy; rewrite /= opprD addrACA.
- apply/(coset_projection_eq hQ).
  have /(coset_projection_eq hQ) hx := hrep (coset_projection +%R (@real_integers R) x).
  by have := subgroup_inv hZ hx; rewrite /= opprD.
Qed.

Section RealIntegerQuotient.
Variable R : realType.
Variable Q : topologicalType.
Variables (pi : R -> Q) (qadd : Q -> Q -> Q) (qopp : Q -> Q).
Hypothesis hQ : is_real_integer_quotient_group pi qadd qopp.
(** Source for [hT]: the topological group R underlying "G = R/Z",
    Federer 2.7.17, p. 141, used in this section. *)
Let hT : is_topological_group (+%R : R -> R -> R) -%R 0 := real_additive_topological_group R.
(** Source for [hC]: R/Z is the space of the cosets x + Z, Federer
    2.7.17, p. 141, with 2.7.1, p. 122, used in this section. *)
Let hC : is_left_coset_space (+%R : R -> R -> R) -%R (@real_integers R) pi :=
  real_quotient_coset_space hQ.

(** Source for [real_quotient_group_laws]: R/Z is a group, Federer
    2.7.17, p. 141. Supporting lemma: the group laws of R pass to R/Z
    through pi, which is onto. *)
Lemma real_quotient_group_laws : is_group_laws qadd qopp (pi 0).
Proof.
have hon := coset_projection_onto hC.
constructor.
- move=> p q r; have [x <-] := hon p; have [y <-] := hon q; have [z <-] := hon r.
  by rewrite !(real_quotient_add hQ) addrA.
- by move=> q; have [x <-] := hon q; rewrite (real_quotient_add hQ) add0r.
- by move=> q; have [x <-] := hon q; rewrite (real_quotient_opp hQ) (real_quotient_add hQ) addNr.
Qed.

(** Source for [real_quotient_add_continuous]: R/Z is a topological
    group, Federer 2.7.17, p. 141, with 2.7.1, p. 121. Supporting
    lemma: the addition is continuous on R/Z x R/Z. If N is a
    neighbourhood of pi(x + y), continuity of (u,v) |-> pi(u + v) gives
    neighbourhoods U of x and V of y with pi(u + v) in N for u in U and
    v in V; since pi is open (2.7.1, p. 122), pi[interior U] and
    pi[interior V] are neighbourhoods of pi(x) and pi(y). *)
Lemma real_quotient_add_continuous : continuous (fun p : Q * Q => qadd p.1 p.2).
Proof.
have hon := coset_projection_onto hC.
have hpo := coset_projection_open hT hC.
have hpc := coset_projection_continuous hC.
have hh : continuous (fun z : R * R => pi (z.1 + z.2)).
  by move=> z; apply: continuous_comp; [exact: add_continuous|exact: hpc].
move=> [p q]; have [x <-] := hon p; have [y <-] := hon q.
move=> N /=; rewrite (real_quotient_add hQ)=> hN.
have [[U V] /= [hU hV] hUV] := hh (x, y) N hN.
exists (pi @` U°, pi @` V°)=> /=.
  split; apply: open_nbhs_nbhs; split.
  - exact: hpo _ (open_interior U).
  - by exists x=> //; exact: nbhs_singleton (nbhs_interior hU).
  - exact: hpo _ (open_interior V).
  - by exists y=> //; exact: nbhs_singleton (nbhs_interior hV).
move=> [p' q'] [/= [u hu <-] [v hv <-]] /=; rewrite (real_quotient_add hQ).
by apply: (hUV (u, v)); split; exact: interior_subset.
Qed.

(** Source for [real_quotient_opp_continuous]: R/Z is a topological
    group, Federer 2.7.17, p. 141. Supporting lemma: the negation is
    continuous, since its composition with pi is pi o (x |-> -x). *)
Lemma real_quotient_opp_continuous : continuous qopp.
Proof.
apply/(coset_space_factor_continuous hC).
have -> : qopp \o pi = pi \o -%R by apply: funext=> x; exact: (real_quotient_opp hQ).
by move=> x; apply: continuous_comp; [exact: opp_continuous|exact: (coset_projection_continuous hC)].
Qed.

(** Source for [real_quotient_compact]: "G is a compact topological
    group", Federer 2.7.17, p. 141, for G = R/Z. Supporting lemma:
    R/Z = pi[[0,1]], since pi(x) = pi(x - k) for the integer part k of
    x, and [0,1] is compact. *)
Lemma real_quotient_compact : compact [set: Q].
Proof.
have -> : [set: Q] = pi @` `[0, 1]%classic.
  apply/seteqP; split=> q // _.
  have [x <-] := coset_projection_onto hC q.
  exists (x - (Num.floor x)%:~R).
    rewrite /= in_itv /=; have /andP[h1 h2] := floor_itv x.
    rewrite subr_ge0 h1 /=; apply: ltW; rewrite ltrBlDr addrC -[1](mulr1z 1) -intrD; exact: h2.
  by apply/(coset_projection_eq hC); rewrite /= opprB subrK; exists (Num.floor x).
apply: continuous_compact; last exact: segment_compact.
exact: continuous_subspaceT (coset_projection_continuous hC).
Qed.

(** Source for [real_quotient_compact_group]: "G is a compact
    topological group", Federer 2.7.17, p. 141, for G = R/Z, within the
    standing hypothesis of 2.7.1, p. 121. Direct formalisation: R/Z is
    a compact Hausdorff, hence locally compact, topological group; it
    is Hausdorff because Z is closed in R (2.7.1, p. 122). *)
Theorem real_quotient_compact_group :
  is_locally_compact_hausdorff_group qadd qopp (pi 0) /\ compact [set: Q].
Proof.
split; last exact: real_quotient_compact.
constructor.
- constructor; [exact: real_quotient_group_laws|exact: real_quotient_add_continuous|].
  exact: real_quotient_opp_continuous.
- exact: (coset_space_hausdorff hT hC (@real_integers_closed R)).
- move=> q _; exists [set: Q]; first exact: withinT.
  by split; [exact: real_quotient_compact|exact: closedT].
Qed.

(** Source for [real_quotient_rationals_subgroup]: "S = Q/Z" is a
    subgroup of R/Z, Federer 2.7.17, p. 141. Supporting lemma: Q/Z is
    the image pi[Q], and Q is a subgroup of R. *)
Lemma real_quotient_rationals_subgroup : is_subgroup qadd qopp (pi 0) (pi @` @real_rationals R).
Proof.
constructor.
- by exists 0=> //; exists 0; rewrite rmorph0.
- move=> _ _ [a [r ->] <-] [b [s ->] <-]; rewrite (real_quotient_add hQ).
  by exists (ratr r + ratr s)=> //; exists (r + s); rewrite rmorphD.
- move=> _ [a [r ->] <-]; rewrite (real_quotient_opp hQ).
  by exists (- ratr r)=> //; exists (- r); rewrite rmorphN.
Qed.

(** Source for [real_quotient_rationals_countable]: "S is a countably
    infinite subgroup", Federer 2.7.17, p. 141, for S = Q/Z.
    Supporting lemma: Q/Z = pi[Q] is the image of the countable set of
    rational numbers. *)
Lemma real_quotient_rationals_countable : countable (pi @` @real_rationals R).
Proof.
have -> : @real_rationals R = [set ratr r | r in [set: rat]].
  by apply/seteqP; split=> x /= [r hr]; [exists r|exists r].
apply: card_le_trans (card_image_le pi _) _; apply: card_le_trans (card_image_le ratr _) _.
exact: countableP.
Qed.

(** Source for [real_quotient_rationals_infinite]: "S is a countably
    infinite subgroup", Federer 2.7.17, p. 141, for S = Q/Z.
    Supporting lemma: the points pi(1/(n+2)), n in N, of Q/Z are
    distinct, because the difference of two of the numbers 1/(n+2) has
    absolute value less than 1 and is not a nonzero integer. *)
Lemma real_quotient_rationals_infinite : infinite_set (pi @` @real_rationals R).
Proof.
pose a (n : nat) : R := (n.+2%:R)^-1.
have ha0 n : 0 < a n by rewrite invr_gt0 ltr0n.
have ha1 n : a n < 1 by rewrite invf_lt1 ?ltr0n // ltr1n.
have hinj : injective (fun n => pi (a n)).
  move=> n m /(coset_projection_eq hC) /= hnm.
  have hd : `|- a n + a m| < 1.
    rewrite ltr_norml; apply/andP; split.
    - by rewrite -(addr0 (-1)) ltr_leD ?ltrN2 // ltW.
    - by rewrite -(add0r 1) ltr_leD ?oppr_lt0 // ltW.
  have /eqP := real_integers_small hnm hd; rewrite addrC subr_eq0=> /eqP.
  by move/invr_inj/eqP; rewrite eqr_nat=> /eqP [].
move=> hfin; apply: infinite_nat.
have hS n : (pi @` @real_rationals R) (pi (a n)).
  by exists (a n)=> //; exists (n.+2%:R)^-1; rewrite fmorphV rmorph_nat.
have := finite_preimage (fun n m _ _ => hinj n m) hfin.
by have -> : (fun n => pi (a n)) @^-1` (pi @` @real_rationals R) = [set: nat]
  by apply/seteqP; split=> n // _; exact: hS.
Qed.

(** Source for [real_quotient_vitali_nonmeasurable]: "This construction
    was used by Vitali (with G = R/Z, S = Q/Z) in the first discovery of
    a nonmeasurable set", Federer 2.7.17, p. 141. Direct formalisation
    of the example for every group R/Z in the sense of
    is_real_integer_quotient_group: R/Z has a left Haar measure, and a
    set T with exactly one point in each coset of Q/Z, chosen by the
    axiom of choice, is nonmeasurable with respect to every left or
    right Haar measure of R/Z. *)
Theorem real_quotient_vitali_nonmeasurable :
  (exists phi : set Q -> \bar R, is_left_haar_measure qadd phi) /\
  exists T : set Q, (forall g, exists! t, T t /\ left_coset qadd g (pi @` @real_rationals R) t) /\
    forall phi : set Q -> \bar R,
      is_left_haar_measure qadd phi \/ is_right_haar_measure qadd qopp phi -> ~ measure_measurable phi T.
Proof.
have [hGc hc] := real_quotient_compact_group.
have hS := real_quotient_rationals_subgroup.
have [hphi _] := compact_group_nonmeasurable_set_exists R hGc hc hS real_quotient_rationals_countable
  real_quotient_rationals_infinite.
split=> //.
have [T hT1] := left_coset_transversal_exists real_quotient_group_laws hS.
exists T; split=> //.
exact: (compact_group_transversal_nonmeasurable hGc hc hS real_quotient_rationals_countable
  real_quotient_rationals_infinite hT1).
Qed.

End RealIntegerQuotient.

(** Source for [vitali_nonmeasurable_set_exists]: "This construction
    was used by Vitali (with G = R/Z, S = Q/Z) in the first discovery of
    a nonmeasurable set", Federer 2.7.17, p. 141. Corollary: there is a
    group R/Z, and a subset of R/Z which is nonmeasurable with respect
    to every Haar measure of R/Z, while Haar measures of R/Z exist. *)
Corollary vitali_nonmeasurable_set_exists (R : realType) :
  exists (Q : topologicalType) (pi : R -> Q) (qadd : Q -> Q -> Q) (qopp : Q -> Q),
    [/\ is_real_integer_quotient_group pi qadd qopp,
      exists phi : set Q -> \bar R, is_left_haar_measure qadd phi &
      exists T : set Q, forall phi : set Q -> \bar R,
        is_left_haar_measure qadd phi \/ is_right_haar_measure qadd qopp phi ->
        ~ measure_measurable phi T].
Proof.
have [Q [pi [qadd [qopp hQ]]]] := real_integer_quotient_group_exists R.
have [hphi [T [_ hT]]] := real_quotient_vitali_nonmeasurable hQ.
by exists Q, pi, qadd, qopp; split=> //; exists T.
Qed.
