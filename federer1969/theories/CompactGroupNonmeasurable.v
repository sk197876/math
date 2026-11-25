(** Federer (1969), 2.7.17, printed p. 141: "If G is a compact topological
    group, S is a countably infinite subgroup of G, and T is a subset of G
    which has exactly one point in common with each left coset of S, then T
    is nonmeasurable with respect to any Haar measure of G. In fact the
    countably many sets Ts corresponding to s in S are disjoint, have equal
    measures, and add up to G. If T were measurable, so would the sets Ts,
    and G would have infinite measure." G satisfies the standing hypothesis
    of 2.7.1, p. 121, of a locally compact Hausdorff topological group, and
    is compact. A Haar measure is a left or a right Haar measure in the
    sense of 2.7.2, p. 122 (HaarIntegralUP.v): the K(G) regular measure
    associated with a left or right Haar integral. "Countably infinite" is
    countable S together with infinite_set S, and "exactly one point in
    common with each left coset" is unique existence of t in T cap g S for
    every g in G. Federer's argument uses facts he does not state: the left
    and right Haar measures of a compact group coincide, by the
    unimodularity of compact groups (2.7.12, p. 129), so the right
    translates Ts have the measure of T and are measurable
    (InvariantMeasureTranslates.v); a Haar measure of a compact group is
    finite, since G is compact (2.5.14, p. 107), and nonzero
    (HaarIntegralLaws.v); and a countable disjointed family of measurable
    sets is additive (2.1.3(3), p. 55). The equal measures then sum to 0 or
    to infinity, by 2.1.1, p. 52. The existence of such sets T, by the axiom
    of choice, is also proved. Federer's historical remark, "This
    construction was used by Vitali (with G = R/Z, S = Q/Z) in the first
    discovery of a nonmeasurable set", is formalised in
    VitaliNonmeasurableSet.v. The local erratum has no entry for 2.7.17; its
    entry for p. 141 concerns 2.7.18. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import TopologicalGroupUP TopologicalGroupLaws FunctionLatticeRegularityUP
  CompactSupportFunctionUP RealIntegralFunctionalUP MeasureUP MeasureBasic
  MeasureCountableAdditivity NonnegativeSum NonnegativeSumConstant CompactSupportMeasureFinite
  CovariantIntegralUP HaarIntegralUP HaarIntegralLaws UnimodularGroupUP UnimodularGroups
  HaarIntegralExistence InvariantMeasureTranslates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CosetTransversals.
Variable G : Type.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hG : is_group_laws mul inv e.
Variables S T : set G.
Hypothesis hS : is_subgroup mul inv e S.
Hypothesis hT1 : forall g, exists! t, T t /\ left_coset mul g S t.

(** Source for [coset_transversal_translates_disjoint]: "the countably
    many sets Ts corresponding to s in S are disjoint", Federer 2.7.17,
    p. 141. Direct formalisation: if x = t s = t' s' with t, t' in T
    and s, s' in S, then t = x s^{-1} and t' = x s'^{-1} lie in the left
    coset x S, hence t = t', and s = s'. *)
Lemma coset_transversal_translates_disjoint s s' :
  S s -> S s' -> s <> s' -> forall x, [set mul t s | t in T] x -> [set mul t s' | t in T] x -> False.
Proof.
move=> hs hs' hne x [t ht htx] [t' ht' htx'].
have [t0 [_ hu]] := hT1 x.
have hxt : left_coset mul x S t.
  by exists (inv s); [exact: (subgroup_inv hS hs)|rewrite -htx (group_mulgK hG)].
have hxt' : left_coset mul x S t'.
  by exists (inv s'); [exact: (subgroup_inv hS hs')|rewrite -htx' (group_mulgK hG)].
have htt : t = t' by rewrite -(hu t (conj ht hxt)) (hu t' (conj ht' hxt')).
move: htx'; rewrite -htt -htx=> /(group_mul_left_cancel hG) hss.
exact: hne (esym hss).
Qed.

(** Source for [coset_transversal_translates_cover]: the sets Ts,
    s in S, "add up to G", Federer 2.7.17, p. 141. Direct
    formalisation: if t is the point of T in x S, say t = x s, then x
    belongs to T s^{-1}, and s^{-1} is in S. *)
Lemma coset_transversal_translates_cover : [set: G] = \bigcup_(s in S) [set mul t s | t in T].
Proof.
apply/seteqP; split=> x // _.
have [t [[ht [s0 hs0 hxs0]] _]] := hT1 x.
exists (inv s0); first exact: (subgroup_inv hS hs0).
by exists t=> //; rewrite -hxs0 (group_mulgK hG).
Qed.

End CosetTransversals.

(** Source for [left_coset_transversal_exists]: the sets T of Federer
    2.7.17, p. 141, "a subset of G which has exactly one point in common
    with each left coset of S". Supporting existence lemma, by the axiom
    of choice: T is the set of the chosen points of the left cosets. *)
Lemma left_coset_transversal_exists (G : Type) (mul : G -> G -> G) (inv : G -> G) (e : G)
    (S : set G) :
  is_group_laws mul inv e -> is_subgroup mul inv e S ->
  exists T : set G, forall g, exists! t, T t /\ left_coset mul g S t.
Proof.
move=> hG hS.
have hne C : exists x, (exists g, C = left_coset mul g S) -> C x.
  have [[x hx]|h0] := pselect (exists x, C x); first by exists x.
  exists e=> [[g hg]]; exfalso; apply: h0; exists g; rewrite hg.
  exists e; first exact: (subgroup_unit hS).
  exact: (group_mulg1 hG g).
pose rep C := projT1 (cid (hne C)).
have hrep g : left_coset mul g S (rep (left_coset mul g S)).
  by apply: (projT2 (cid (hne (left_coset mul g S)))); exists g.
exists [set rep (left_coset mul h S) | h in [set: G]]=> g.
exists (rep (left_coset mul g S)); split; first by split; [exists g|exact: hrep].
move=> t [[h _ <-] hgt].
have hh := hrep h.
have hgh : left_coset mul g S = left_coset mul h S.
  apply/(left_coset_eq hG g h hS); move/(left_coset_member hG): hgt=> hgt.
  move/(left_coset_member hG): hh=> hh.
  have := subgroup_mul hS hgt (subgroup_inv hS hh).
  by rewrite (group_invM hG) (group_invK hG) (group_mulA hG) (group_mulgK hG).
by rewrite hgh.
Qed.

Section CompactGroupNonmeasurable.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hGc : is_locally_compact_hausdorff_group mul inv e.
Hypothesis hc : compact [set: G].
(** Source for [hT]: G is a topological group, Federer 2.7.17,
    p. 141, with 2.7.1, p. 121, used in this section. *)
Let hT : is_topological_group mul inv e := lch_group_topological hGc.
(** Source for [hG]: the group laws of G, Federer 2.7.1, p. 121, used
    in this section. *)
Let hG : is_group_laws mul inv e := topological_group_laws hT.

(** Source for [compact_group_haar_measures_coincide]: "any Haar
    measure of G", Federer 2.7.17, p. 141, for a compact group G.
    Supporting lemma: by "every compact group is unimodular", 2.7.12,
    p. 129, the left and right Haar integrals of G coincide, hence so
    do the associated left and right Haar measures of 2.7.2, p. 122. *)
Lemma compact_group_haar_measures_coincide (phi : set G -> \bar R) :
  is_left_haar_measure mul phi <-> is_right_haar_measure mul inv phi.
Proof.
have hU := compact_group_unimodular (R:=R) hGc hc.
by split; case=> mu [hmu hphi hi hr]; exists mu; split=> //; apply/(hU mu).
Qed.

(** Source for [compact_right_haar_measure_total]: "G would have
    infinite measure", Federer 2.7.17, p. 141, which is absurd because a
    Haar measure of a compact group has finite nonzero total measure.
    Supporting lemma: phi(G) < infinity since G is compact and phi
    represents a Daniell integral on K(G) (2.5.14, p. 107), and
    phi(G) > 0 since a Haar measure is not the zero measure (2.7.2,
    p. 122). *)
Lemma compact_right_haar_measure_total (phi : set G -> \bar R) :
  is_right_haar_measure mul inv phi -> (0 < phi [set: G])%E /\ (phi [set: G] < +oo)%E.
Proof.
move=> hphi; have [mu [_ hm hi _]] := hphi.
split.
- have [B hB] := nonzero_invariant_measure_nonzero hphi.
  rewrite lt_def (measure_nonnegative hm) andbT; apply/eqP=> h0; apply: hB.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT -h0.
  exact: (measure_mono hm (@subsetT _ B)).
- exact: (compact_support_representing_measure_compact_finite hm hi (lch_group_hausdorff hGc)
    (lch_group_locally_compact hGc) hc).
Qed.

(** Source for [compact_group_transversal_right_haar_nonmeasurable]:
    Federer 2.7.17, p. 141, for a right Haar measure. Direct
    formalisation of the printed argument: the sets T s, s in S, are
    disjoint, measurable with the measure of T, and cover G, so phi(G)
    is the sum over the infinite set S of the constant phi(T), which is
    0 or infinity, while 0 < phi(G) < infinity. *)
Theorem compact_group_transversal_right_haar_nonmeasurable (S T : set G) (phi : set G -> \bar R) :
  is_subgroup mul inv e S -> countable S -> infinite_set S ->
  (forall g, exists! t, T t /\ left_coset mul g S t) ->
  is_right_haar_measure mul inv phi -> ~ measure_measurable phi T.
Proof.
move=> hS hcS hiS hT1 hphi hTm.
have hinv := nonzero_invariant_measure_invariant hphi.
have [mu [_ hm _ _]] := hphi.
have [hpos hfin] := compact_right_haar_measure_total hphi.
have hFm s : measure_measurable phi [set mul t s | t in T].
  exact: (right_invariant_measure_translate_measurable hT hinv).
have hdisj s s' : S s -> S s' -> s != s' ->
    forall x, [set mul t s | t in T] x -> [set mul t s' | t in T] x -> False.
  by move=> hs hs' /eqP hne; exact: (coset_transversal_translates_disjoint hG hS hT1 hs hs' hne).
have hsum := measure_countable_disjoint_additivity hm hcS (fun s _ => hFm s) hdisj.
rewrite -(coset_transversal_translates_cover hG hS hT1) in hsum.
have hFphi : (fun s => phi [set mul t s | t in T]) = fun _ => phi T.
  by apply: funext=> s; exact: (right_invariant_measure_translate hT hinv).
rewrite hFphi in hsum.
have hT0 := measure_nonnegative hm T.
have [h0|h0] := eqVneq (phi T) 0%E.
  move: hpos; rewrite hsum h0 (nonnegative_sum_zero (A:=S) (f:=fun _ => 0%E)) //.
  by rewrite ltxx.
have hTfin : (phi T < +oo)%E.
  exact: le_lt_trans (measure_mono hm (@subsetT _ T)) hfin.
have hTr : phi T = (fine (phi T))%:E by rewrite fineK // ge0_fin_numE.
have hr : 0 < fine (phi T).
  by rewrite -lte_fin -hTr lt_def h0 hT0.
move: hfin; rewrite hsum hTr (nonnegative_sum_infinite_constant hr hiS).
by rewrite ltxx.
Qed.

(** Source for [compact_group_transversal_left_haar_nonmeasurable]:
    Federer 2.7.17, p. 141, for a left Haar measure. Direct
    formalisation: on a compact group a left Haar measure is a right
    Haar measure (2.7.12, p. 129), and the right case applies. *)
Theorem compact_group_transversal_left_haar_nonmeasurable (S T : set G) (phi : set G -> \bar R) :
  is_subgroup mul inv e S -> countable S -> infinite_set S ->
  (forall g, exists! t, T t /\ left_coset mul g S t) ->
  is_left_haar_measure mul phi -> ~ measure_measurable phi T.
Proof.
move=> hS hcS hiS hT1 /compact_group_haar_measures_coincide hphi.
exact: compact_group_transversal_right_haar_nonmeasurable hS hcS hiS hT1 hphi.
Qed.

(** Source for [compact_group_transversal_nonmeasurable]: "If G is a
    compact topological group, S is a countably infinite subgroup of G,
    and T is a subset of G which has exactly one point in common with
    each left coset of S, then T is nonmeasurable with respect to any
    Haar measure of G", Federer 2.7.17, p. 141. Direct formalisation,
    for left and right Haar measures. *)
Theorem compact_group_transversal_nonmeasurable (S T : set G) :
  is_subgroup mul inv e S -> countable S -> infinite_set S ->
  (forall g, exists! t, T t /\ left_coset mul g S t) ->
  forall phi : set G -> \bar R, is_left_haar_measure mul phi \/ is_right_haar_measure mul inv phi ->
    ~ measure_measurable phi T.
Proof.
move=> hS hcS hiS hT1 phi [hphi|hphi].
- exact: compact_group_transversal_left_haar_nonmeasurable hS hcS hiS hT1 hphi.
- exact: compact_group_transversal_right_haar_nonmeasurable hS hcS hiS hT1 hphi.
Qed.

(** Source for [compact_group_nonmeasurable_set_exists]: Federer
    2.7.17, p. 141, together with the existence of the sets T by the
    axiom of choice and of Haar measures by 2.7.5, p. 125, and 2.7.2,
    p. 122. Corollary: a compact group with a countably infinite
    subgroup has a left Haar measure, and a subset that is
    nonmeasurable with respect to every left or right Haar measure. *)
Corollary compact_group_nonmeasurable_set_exists (S : set G) :
  is_subgroup mul inv e S -> countable S -> infinite_set S ->
  (exists phi : set G -> \bar R, is_left_haar_measure mul phi) /\
  exists T : set G, forall phi : set G -> \bar R,
    is_left_haar_measure mul phi \/ is_right_haar_measure mul inv phi -> ~ measure_measurable phi T.
Proof.
move=> hS hcS hiS; split.
- have [mu hmu] := left_haar_integral_exists R hGc.
  by have [phi [hphi _ _ _ _]] := nonzero_invariant_measure_exists hmu; exists phi.
- have [T hT1] := left_coset_transversal_exists hG hS.
  by exists T; exact: compact_group_transversal_nonmeasurable hS hcS hiS hT1.
Qed.

End CompactGroupNonmeasurable.
