(** Federer (1969), 2.7.14, printed p. 131: "Every left (right) chi
    covariant measure over G is a Radon measure", and 2.7.15, p. 133. By
    2.7.1, p. 122, a chi covariant measure is the K(X) regular measure
    associated with a monotone chi covariant integral, and the zero integral
    is such an integral for every chi. This module shows that the statement
    fails for the zero integral when X is not a countable union of compact
    sets, which justifies the alternative hypothesis of
    CovariantMeasureRadon.v and HomogeneousCovariantMeasureRadon.v. Let phi
    be the K(X) regular measure associated with the zero integral. Then
    phi(K) = 0 for every compact K. If phi(X) < oo, then X would lie in a
    set of the class F2 of 2.5.3, p. 94, hence in a countable union of the
    compact supports spt f, f in K(X)+; so phi(X) = oo, and the inner
    regularity of the open set X required by 2.2.5, p. 62, fails. A group to
    which this applies is the set of all subsets of N with the symmetric
    difference and the discrete topology: it is a locally compact Hausdorff
    topological group, its compact subsets are finite, and it is
    uncountable. The counterexample confirms Federer's erratum p. 3, book
    p. 131 line 10, which adds "nonzero". *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality
  functions reals constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground FunctionLatticeUP MonotoneDaniellIntegralUP
  ExtendedRealOrderLimit CompactSupportFunctionUP FunctionLatticeLevelFamilies
  FunctionLatticeRegularityUP RealIntegralFunctionalUP MeasureUP MeasureBasic RadonMeasureUP
  TopologicalGroupUP CovariantIntegralUP CovariantIntegralLaws HaarIntegralUP
  GroupMultiplicationHomogeneous ContinuumUncountability DiscreteSliceSpace
  RegularMeasureRadonCriteria CovariantMeasureRadon.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [zero_integral_regular_not_radon]: the K(X) regular
    measure associated with the zero integral on K(X) is not a Radon
    measure when X is not a countable union of compact sets; local
    counterexample to the unrestricted reading of "Every left (right)
    chi covariant measure over G is a Radon measure", Federer 2.7.14,
    p. 131, and of 2.7.15, p. 133, through 2.5.3, p. 94, and 2.2.5,
    p. 62. *)
Theorem zero_integral_regular_not_radon (R : realType) (X : topologicalType)
    (phi : set X -> \bar R) (A : (X -> R) -> R) :
  hausdorff_space X -> locally_compact [set: X] -> is_measure phi ->
  is_real_integral_functional phi (@compactly_supported_continuous_functions R X) A ->
  is_function_lattice_regular (@compactly_supported_continuous_functions R X) phi ->
  (forall u, @compactly_supported_continuous_functions R X u -> A u = 0) ->
  ~ is_sigma_compact_space X -> ~ is_radon_measure phi.
Proof.
move=> hX hlX hm hA hr hz hns hrad.
have hK0 := regular_vanishing_compact_null hX hlX hm hA hz.
have hinf : phi [set: X] = +oo%E.
  apply: contrapT=> hne.
  have hfin : (phi [set: X] < +oo)%E by rewrite ltey; apply/eqP.
  have [W [hXW [[V [hV [_ [_ hW]]]] _]]] := (hr [set: X]).1 hfin.
  have [Z [hZ [_ hV0]]] := hV 0%N.
  have hc m : exists C, compact C /\ Z m `<=` C.
    have [f [t [[hf _] [ht ->]]]] := hZ m.
    exists (real_function_support f); split; first exact: hf.2.
    move=> x hx; apply: subset_closure=> h0; move: hx; rewrite /= h0 ltNge (ltW ht) //.
  apply: hns; exists (fun m => projT1 (cid (hc m))); split.
    by move=> m; exact: (projT2 (cid (hc m))).1.
  move=> x _; have hx : W x := hXW x I.
  rewrite hW in hx; have := hx 0%N I; rewrite hV0=> -[m _ hm'].
  by exists m=> //; exact: (projT2 (cid (hc m))).2.
have hle := @radon_inner_least R X phi hrad [set: X] openT 0%E
  (fun C hC _ => eq_ind_r (fun a => (a <= 0)%E) (lexx 0%E) (hK0 C hC)).
by move: hle; rewrite hinf leNgt ltry.
Qed.

(** Source for [subset_group]: the subsets of N with the discrete
    topology, the group of the counterexample to the unrestricted
    reading of Federer 2.7.14, p. 131. Definition. *)
Definition subset_group : topologicalType := discrete_topology (set nat).

(** Source for [subset_difference]: the symmetric difference
    A, B |-> {n: n in A if and only if n notin B}, the multiplication of
    the group of the counterexample to the unrestricted reading of
    Federer 2.7.14, p. 131. Definition. *)
Definition subset_difference (A B : subset_group) : subset_group := [set n | ~ (A n <-> B n)].

(** Source for [subset_group_lch]: the subsets of N with the symmetric
    difference and the discrete topology form a locally compact Hausdorff
    topological group, with A^{-1} = A and identity the empty set;
    supporting the counterexample to the unrestricted reading of Federer
    2.7.14, p. 131, which uses the standing hypotheses of 2.7.1, p. 121.
    Supporting lemma. *)
Lemma subset_group_lch : is_locally_compact_hausdorff_group subset_difference id (set0 : subset_group).
Proof.
constructor.
- constructor.
  + constructor.
    * move=> A B C; rewrite /subset_difference; apply/seteqP; split=> n /=;
        case: (pselect (A n)); case: (pselect (B n)); case: (pselect (C n)); tauto.
    * move=> A; rewrite /subset_difference; apply/seteqP; split=> n /=; case: (pselect (A n)); tauto.
    * move=> A; rewrite /subset_difference; apply/seteqP; split=> n /=; tauto.
  + move=> [x y] N hN.
    exists ([set x], [set y]); first by split; exact: discrete_set1.
    by move=> [a b] [/= -> ->]; exact: nbhs_singleton hN.
  + by move=> x; exact: cvg_id.
- exact: discrete_hausdorff.
- move=> x _; rewrite withinET; exists [set x]; first exact: discrete_set1.
  by split; [exact: compact_set1|exact: discrete_closed].
Qed.

(** Source for [subset_group_not_sigma_compact]: the group of subsets
    of N is not a countable union of compact sets, since its compact
    subsets are finite (it is discrete) and it is uncountable; supporting
    the counterexample to the unrestricted reading of Federer 2.7.14,
    p. 131. Supporting lemma. *)
Lemma subset_group_not_sigma_compact : ~ is_sigma_compact_space subset_group.
Proof.
move=> [C [hC hcov]]; apply: natural_power_set_uncountable.
have hfin n : countable (C n).
  have hf : finite_set (C n) := @slice_index_compact_finite (set nat) (C n) (hC n).
  exact: (finite_set_countable hf).
have hU := @bigcup_countable nat (set nat) [set: nat] C (countableP _) (fun n _ => hfin n).
apply: (sub_countable _ hU); apply: subset_card_le=> A _.
by have [n _ hn] := hcov A I; exists n.
Qed.

(** Source for [zero_left_invariant_measure_not_radon]: there is a left
    invariant measure (2.7.2, p. 122) over a locally compact Hausdorff
    topological group which is not a Radon measure and vanishes on all
    compact sets; local counterexample to the unrestricted reading of
    "Every left ... chi covariant measure over G is a Radon measure",
    Federer 2.7.14, p. 131. It is the K(G) regular measure associated
    with the zero integral on the group of subsets of N. *)
Theorem zero_left_invariant_measure_not_radon (R : realType) :
  exists phi : set subset_group -> \bar R,
    [/\ is_left_invariant_measure subset_difference phi,
      forall C, compact C -> phi C = 0%E & ~ is_radon_measure phi].
Proof.
have hG := subset_group_lch.
have hzm : is_monotone_daniell_integral (@compactly_supported_continuous_functions R subset_group)
    (fun _ => 0).
  constructor.
  - by move=> f g _ _; rewrite addr0.
  - by move=> c f _ _; rewrite mulr0.
  - by move=> f g _ _ _.
  - move=> f g _ _ _; split; first by move=> n m _.
    by split=> [a ha|b hb]; exists 0%N=> n _.
have hzc : is_covariant_on (@compactly_supported_continuous_functions R subset_group)
    (left_multiplication_action subset_difference) (fun _ => 1) (fun _ => 0).
  by move=> u g _; rewrite mulr0.
have [phi [hcm hm hA hr _]] := covariant_measure_exists hzm hzc.
have hX := lch_group_hausdorff hG; have hlX := lch_group_locally_compact hG.
exists phi; split=> //.
- exact: (regular_vanishing_compact_null hX hlX hm hA (fun _ _ => erefl)).
- exact: (zero_integral_regular_not_radon hX hlX hm hA hr (fun _ _ => erefl) subset_group_not_sigma_compact).
Qed.
