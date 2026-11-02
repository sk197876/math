(** Federer (1969), 2.5.14, p. 108: "however k need not be Phi almost
    unique, only locally so". Let D be an uncountable set with the discrete
    topology, X the cartesian product of D and R, lambda the product of the
    counting functional on K(D) and the integral on K(R) induced by the
    identity (DiscreteSliceSpace.v), and Phi a Radon measure over X with
    integral lambda(f) for every f in K(X), as constructed in 2.5.14, p.
    107. The set Z = D x {0} meets every compact set in a Phi null set,
    because a compact set meets only finitely many slices {d} x R. Every
    open set V containing Z contains a strip {d} x {t : |t| < 1/(n_d+1)} for
    each d in D; since D is uncountable, infinitely many d share one n_d, so
    Phi(V) = infinity, and Phi(Z) = infinity by the outer regularity of Phi.
    Federer gives no example for this sentence; the example is supplied
    here. The local erratum has no entry for p. 108. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  fsbigop reals constructive_ereal topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground FunctionLatticeUP CompactSupportFunctionUP
  CompactSupportFunctionLattice ExtendedRealBoundsUP MeasureUP RadonMeasureUP RealIntegralFunctionalUP
  MeasureBasic RealTotalCharacteristicBounds RepresentedLatticeClosedLevels CompactSeparatedProduct
  CompactOpenContentUP CompactOpenContentSealed CompactOpenContentMeasureBound
  LocallyNullMeasureUP RadonLocallyNull ExtendedRealReciprocalBounds DiscreteSliceSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [extended_le_scaled_epsilon]: supporting estimate for
    the null sets of the counterexample in Federer 2.5.14, p. 108: a
    nonnegative extended real bounded by c e for every e > 0 vanishes. *)
Lemma extended_le_scaled_epsilon (R : realType) (x : \bar R) (c : R) :
  (0%E <= x)%E -> 0 <= c -> (forall e : R, 0 < e -> (x <= (c * e)%:E)%E) -> x = 0%E.
Proof.
case: x=> [r| |] hx hc he.
- have hr : 0 <= r by rewrite -lee_fin.
  congr (_%:E); apply/eqP; rewrite eq_le hr andbT.
  apply/ler_addgt0Pr=> e he0; rewrite add0r.
  have hc1 : 0 < c + 1 by lra.
  have := he (e / (c + 1)) (divr_gt0 he0 hc1); rewrite lee_fin=> h.
  apply: le_trans h _; rewrite mulrA ler_pdivrMr // mulrDr mulr1 mulrC.
  by rewrite lerDl ltW.
- by have := he 1 ltr01; rewrite leye_eq.
- by move: hx; rewrite leeNy_eq.
Qed.

(** Source for [extended_unbounded_multiples]: supporting estimate for
    the open sets of the counterexample in Federer 2.5.14, p. 108: an
    extended real bounded below by every multiple m b, b > 0, of a
    positive real number is infinite. *)
Lemma extended_unbounded_multiples (R : realType) (x : \bar R) (b : R) :
  0 < b -> (forall m : nat, ((m%:R * b)%:E <= x)%E) -> x = +oo%E.
Proof.
case: x=> [r| |] hb hm //.
- have [n hn] : exists n : nat, r / b < n%:R.
    exists (Num.bound `|r / b|).
    exact: le_lt_trans (ler_norm _) (archi_boundP (normr_ge0 _)).
  have := hm n; rewrite lee_fin -ler_pdivlMr // => h.
  by have := lt_le_trans hn h; rewrite ltxx.
- by have := hm 0%N; rewrite leeNy_eq.
Qed.

Section Radon.
Variable R : realType.
Variable D : choiceType.
Local Notation slice_index := (discrete_topology D).
Local Notation slice_space := (discrete_topology D * R)%type.
Local Notation KD := (@compactly_supported_continuous_functions R slice_index).
Local Notation KR := (@compactly_supported_continuous_functions R R).
Local Notation KX := (@compactly_supported_continuous_functions R slice_space).
Local Notation lambda := (@slice_lambda R D).

(** Source for [zero_slice]: the set Z = D x {0} of the counterexample
    to almost uniqueness in Federer 2.5.14, p. 108, on which two
    densities will differ. *)
Definition zero_slice : set slice_space := [set p | p.2 = 0].

Variable phi : set slice_space -> \bar R.
Hypothesis hm : is_measure phi.
Hypothesis hr : is_radon_measure phi.
Hypothesis hA : is_real_integral_functional phi KX lambda.

(** Source for [slice_indicator_member]: the indicator of a finite set
    of indices belongs to K(D), supporting Federer 2.5.14, p. 108. *)
Lemma slice_indicator_member (F : set slice_index) : finite_set F ->
  KD (fun d => (d \in F)%:R).
Proof.
move=> hF; apply/slice_index_compact_support.
apply: (sub_finite_set _ hF)=> d /=.
by case: (boolP (d \in F))=> [/set_mem //|_ h]; exfalso; exact: h.
Qed.

(** Source for [zero_slice_compact_null]: a compact set meets
    Z = D x {0} in a Phi null set, supporting the local uniqueness
    assertion of Federer 2.5.14, p. 108. The compact set meets only
    finitely many slices, and the measure of their points is estimated
    by lambda(u . b) = A(u) B(b) with B(b) <= 2e. *)
Lemma zero_slice_compact_null (K : set slice_space) : compact K -> phi (K `&` zero_slice) = 0%E.
Proof.
move=> hK.
pose F := [set p.1 | p in K].
have hFc : compact F.
  apply: continuous_compact hK; apply: continuous_subspaceT=> p.
  exact: cvg_fst.
have hF : finite_set F := slice_index_compact_finite hFc.
pose u := fun d : slice_index => (d \in F)%:R : R.
have hu : KD u := slice_indicator_member hF.
have hu0 : forall d, 0 <= u d by move=> d; rewrite ler0n.
apply: (@extended_le_scaled_epsilon R _ (slice_count u * 2)).
- exact (measure_nonnegative hm _).
- by rewrite mulr_ge0 // slice_count_nonnegative.
move=> e he.
have [b [hb [hb0 [hb1 hbi]]]] := line_bump_small he.
pose f := fun p : slice_space => u p.1 * b p.2.
have hf : KX f := compactly_supported_separated_product hu hb.
have hf0 : function_nonnegative f by move=> p; rewrite mulr_ge0.
have hlev := represented_lattice_closed_upper_level_measurable hm hA 1 hf.
have hsub : K `&` zero_slice `<=` [set p | 1 <= f p].
  move=> [d t] [hp ht]; rewrite /zero_slice /= in ht; rewrite /f /= ht hb1 mulr1 /u.
  by have -> : (d \in F) by apply/mem_set; exists (d, t).
apply: le_trans (measure_mono hm hsub) _.
have := real_total_integral_level_lower_bound hm hlev ltr01 (@hA f hf) hf0 (fun p hp => hp).
rewrite mul1e /f slice_lambda_separated // => h; apply: le_trans h _.
rewrite lee_fin -mulrA ler_wpM2l ?slice_count_nonnegative //.
Qed.

(** Source for [zero_slice_locally_null]: Z = D x {0} is locally Phi
    null, Federer 2.5.14, p. 108: it meets every set of finite measure
    in a null set. *)
Theorem zero_slice_locally_null : measure_locally_null phi zero_slice.
Proof.
apply/(radon_locally_null_compact_iff hm hr)=> K hK.
exact (zero_slice_compact_null hK).
Qed.

Hypothesis hD : ~ countable [set: D].

(** Source for [zero_slice_open_superset_infinite]: every open set
    containing Z = D x {0} has infinite Phi measure, supporting Federer
    2.5.14, p. 108. Each d in D has a strip {d} x {t : |t| < 1/(N(d)+1)}
    inside V; as D is uncountable, some value n of N is taken infinitely
    often, and the test functions u . b with u the indicator of m indices
    with N = n give Phi(V) >= alpha(V) >= m B(b) for every m. *)
Lemma zero_slice_open_superset_infinite (V : set slice_space) :
  open V -> zero_slice `<=` V -> phi V = +oo%E.
Proof.
move=> hV hZV.
have hstrip : forall d : slice_index, exists n : nat,
    forall t : R, `|t| < n.+1%:R^-1 -> V (d, t).
  move=> d.
  have hn : nbhs ((d, 0) : slice_space) V.
    by move: hV; rewrite openE=> /(_ (d, 0)); apply; exact: hZV.
  have [[P1 P2] /= [hP1 hP2] hP] := hn.
  have [e he hball] := proj1 (nbhs_ballP (0 : R) P2) hP2.
  have [n hne] := positive_reciprocal_nat_small he.
  exists n=> t ht; apply: (hP (d, t)); split=> //=; first exact: nbhs_singleton hP1.
  apply: hball; rewrite /ball /= sub0r normrN.
  exact: lt_trans ht hne.
have [N hN] := choice hstrip.
have [n0 hn0] : exists n0, infinite_set [set d | N d = n0].
  apply: contrapT=> hno; apply: hD.
  have -> : [set: slice_index] = \bigcup_(n in [set: nat]) [set d | N d = n].
    by apply/seteqP; split=> [d _|d _ //]; exists (N d).
  apply: bigcup_countable=> // n _; apply: finite_set_countable.
  by apply: contrapT=> hinf; apply: hno; exists n.
pose r := n0.+1%:R^-1 : R.
have hr0 : 0 < r by rewrite invr_gt0 ltr0n.
have hr2 : 0 < r / 2 by lra.
have [b [hb [hb01 [hbs hbpos]]]] := line_bump_positive hr2.
apply: (extended_unbounded_multiples hbpos)=> m.
have [B hB hBm] := infinite_set_fset m hn0.
pose s := finmap.enum_fset B.
pose u := fun d : slice_index => (d \in s)%:R : R.
have hs : uniq s := finmap.fset_uniq B.
have hu : KD u.
  apply/slice_index_compact_support; apply: (sub_finite_set _ (finite_seq s))=> d /=.
  by rewrite /u; case: (boolP (d \in s))=> [hd _|_ h] //; exfalso; exact: h.
pose f := fun p : slice_space => u p.1 * b p.2.
have hf : KX f := compactly_supported_separated_product hu hb.
pose C : set slice_space := [set` s] `*` `[- (r / 2), r / 2]%classic.
have hC : closed C.
  have hc := compact_setX (finite_compact (finite_seq s)) (@segment_compact R (- (r / 2)) (r / 2)).
  exact (compact_closed (@slice_space_hausdorff R D) hc).
have hCV : C `<=` V.
  move=> [d t] [/= hd ht]; apply: (hN d).
  have hdB : N d = n0 by apply: hB; exact: hd.
  rewrite hdB -/r.
  move: ht; rewrite /= in_itv /= => /andP[ht1 ht2].
  by rewrite ltr_norml; apply/andP; split; lra.
have htest : is_compact_open_test_function V f.
  split=> //; split.
  - move=> [d t]; rewrite /f /u /=.
    have /andP[hb0 hb1] := hb01 t.
    case: (d \in s)=> /=; last by rewrite mul0r lexx ler01.
    by rewrite mul1r hb0 hb1.
  - apply: subset_trans _ hCV; apply: real_function_support_in_closed_set=> // [[d t]] hn.
    rewrite /f /u /=; case: (boolP (d \in s))=> hds; last by rewrite mul0r.
    case: (eqVneq (b t) 0)=> hbt; first by rewrite hbt mulr0.
    exfalso; apply: hn; split=> //=.
    move/eqP: hbt=> hbt; have /andP[h1 h2] := hbs t hbt.
    by rewrite /= in_itv /=; apply/andP; split; lra.
have ha := @CompactOpenContent.laws R slice_space lambda.
have hle := @compact_open_content_representing_measure_bound R slice_space phi lambda _ hm hA ha V hV.
apply: le_trans hle; apply: le_trans (extended_real_supremum_upper (ha V hV) _); last first.
  by exists f; split.
rewrite lee_fin /f slice_lambda_separated // slice_count_indicator //.
by apply: ler_wpM2r; [exact: ltW hbpos|rewrite ler_nat; exact: hBm].
Qed.

(** Source for [zero_slice_infinite]: Phi(Z) = infinity for
    Z = D x {0}, Federer 2.5.14, p. 108, by the outer regularity of the
    Radon measure Phi (2.2.5, p. 62). Hence Z is locally null but not
    null. *)
Theorem zero_slice_infinite : phi zero_slice = +oo%E.
Proof.
apply/eqP; rewrite eq_le leey /=.
apply: (radon_outer_greatest hr)=> V hV hZV.
by rewrite (zero_slice_open_superset_infinite hV hZV).
Qed.
End Radon.
