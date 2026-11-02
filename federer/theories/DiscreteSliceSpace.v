(** Federer (1969), 2.5.14, p. 108: "however k need not be Phi almost
    unique, only locally so". This module prepares the space of the
    counterexample. Let D be a set with the discrete topology and let X be
    the cartesian product of D and R. Then X is a locally compact Hausdorff
    space, every compact subset of D is finite, and the counting functional
    g |-> sum_{d in D} g(d) is a monotone Daniell integral on K(D). Its
    product, in the sense of 2.6.4, p. 119, with the Daniell integral of
    2.5.17, p. 111, induced by the identity map of R is the monotone Daniell
    integral lambda on K(X) used in the counterexample: lambda(u . b) = A(u)
    B(b) for u in K(D) and b in K(R). Federer gives no example for this
    sentence; the example is supplied here. The local erratum has no entry
    for p. 108. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  fsbigop reals constructive_ereal topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground FunctionLatticeUP CompactSupportFunctionUP
  CompactSupportFunctionLattice HausdorffBinaryProduct CompactFiniteCover MonotoneDaniellIntegralUP
  MonotoneDaniellIntegralLaws DaniellIntegralUP FunctionLatticeSeminormUP LatticeAdditiveFunctional
  CompactSupportRieszRepresentation DaniellProductUP DaniellProduct DaniellProductMonotone
  CompactSeparatedProduct CurveArcLength StieltjesIntegral StieltjesDaniellIntegral StieltjesMonotone
  IntervalBumpFunctions StieltjesContinuityPoints ExtendedRealReciprocalBounds MonotoneDaniellIntegralSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Space.
Variable R : realType.
Variable D : choiceType.

(* The set D with the discrete topology, and the space X, the
   cartesian product of D and R with the product topology. *)
Local Notation slice_index := (discrete_topology D).
Local Notation slice_space := (discrete_topology D * R)%type.

Local Notation KD := (@compactly_supported_continuous_functions R slice_index).
Local Notation KX := (@compactly_supported_continuous_functions R slice_space).

(** Source for [slice_index_compact_finite]: supporting general
    topology for Federer 2.5.14, p. 108: a compact subset of a discrete
    space is finite, because the singletons form an open cover. *)
Lemma slice_index_compact_finite (K : set slice_index) : compact K -> finite_set K.
Proof.
move=> hK.
have [F _ hcov] := @compact_open_finite_cover slice_index D K
  (fun x : slice_index => [set x]) K hK (fun x _ => discrete_open _)
  (fun x hx => ex_intro2 _ _ x hx erefl).
apply: (sub_finite_set _ (finite_fset F))=> x hx.
have [y hy hxy] := hcov x hx.
by rewrite hxy.
Qed.

(** Source for [slice_index_hausdorff]: supporting general topology for
    Federer 2.5.14, p. 108: a discrete space is Hausdorff. *)
Lemma slice_index_hausdorff : hausdorff_space slice_index.
Proof. exact: discrete_hausdorff. Qed.

(** Source for [slice_index_locally_compact]: supporting general
    topology for Federer 2.5.14, p. 108: each singleton of a discrete
    space is a compact closed neighbourhood. *)
Lemma slice_index_locally_compact : locally_compact [set: slice_index].
Proof.
move=> x _; rewrite withinET; exists [set x]; first exact: discrete_set1.
by split; [exact: compact_set1|exact: discrete_closed].
Qed.

(** Source for [slice_space_hausdorff]: the space X of the
    counterexample to almost uniqueness, Federer 2.5.14, p. 108, is a
    Hausdorff space, as required by 2.5.13, p. 106. *)
Lemma slice_space_hausdorff : hausdorff_space slice_space.
Proof. exact: hausdorff_binary_product slice_index_hausdorff (@Rhausdorff R). Qed.

(** Source for [slice_space_locally_compact]: the space X of the
    counterexample, Federer 2.5.14, p. 108, is locally compact, as
    required by 2.5.13, p. 106: the point (d,t) has the compact closed
    neighbourhood {d} x U, where U is a compact closed neighbourhood
    of t in R. *)
Lemma slice_space_locally_compact : locally_compact [set: slice_space].
Proof.
move=> [d t] _; rewrite withinET.
have := @locally_compactR R t Logic.I; rewrite withinET=> -[U hU [hUc hUcl]].
exists ([set d] `*` U).
  exists ([set d], U); last by [].
  by split; [exact: discrete_set1|exact: hU].
have hc := compact_setX (@compact_set1 slice_index d) hUc.
split; first exact hc.
exact (compact_closed slice_space_hausdorff hc).
Qed.

(** Source for [slice_index_continuous]: supporting general topology for
    Federer 2.5.14, p. 108: every real function on a discrete space is
    continuous. *)
Lemma slice_index_continuous (g : slice_index -> R) :
  continuous (g : slice_index -> real_line_metric R).
Proof. by apply/continuousP=> A _; exact: discrete_open. Qed.

(** Source for [slice_index_compact_support]: supporting general topology
    for Federer 2.5.14, p. 108: a function on D belongs to K(D) if and
    only if it vanishes outside a finite set. *)
Lemma slice_index_compact_support (g : slice_index -> R) :
  KD g <-> finite_set [set d | g d <> 0].
Proof.
split=> [hg|hfin].
- apply: (sub_finite_set _ (slice_index_compact_finite hg.2))=> d hd.
  exact: subset_closure hd.
- split; first exact: slice_index_continuous.
  rewrite /real_function_support -((closure_id _).1 (discrete_closed _)).
  exact: finite_compact hfin.
Qed.

(** Source for [slice_count]: the counting functional on K(D),
    A(g) = sum_{d in D} g(d), supporting the counterexample to almost
    uniqueness in Federer 2.5.14, p. 108. The sum has finitely many
    nonzero terms for every member of K(D). *)
Definition slice_count (g : slice_index -> R) : R := \sum_(d \in [set: slice_index]) g d.

(** Source for [slice_count_restrict]: supporting computation for
    Federer 2.5.14, p. 108: the counting functional is the sum over any
    set containing the points where g does not vanish. *)
Lemma slice_count_restrict (g : slice_index -> R) (S : set slice_index) :
  (forall d, g d <> 0 -> S d) -> slice_count g = \sum_(d \in S) g d.
Proof.
move=> hS; rewrite /slice_count; symmetry.
apply: fsbig_widen=> // d [_ hd] /=.
by apply: contrapT=> hn; apply: hd; exact: hS.
Qed.

(** Source for [slice_count_add]: additivity of the counting functional
    on K(D), supporting Federer 2.5.14, p. 108, and the hypotheses of
    2.5.13, p. 106. *)
Lemma slice_count_add (f g : slice_index -> R) : KD f -> KD g ->
  slice_count (fun d => f d + g d) = slice_count f + slice_count g.
Proof.
move=> /slice_index_compact_support hf /slice_index_compact_support hg.
pose S := [set d | f d <> 0] `|` [set d | g d <> 0].
have hS : finite_set S by rewrite /S finite_setU; split.
have hfS d : f d <> 0 -> S d by move=> h; left.
have hgS d : g d <> 0 -> S d by move=> h; right.
have hfgS d : f d + g d <> 0 -> S d.
  move=> h; apply: contrapT=> hn; apply: h.
  have hf0 : f d = 0 by apply: contrapT=> h'; apply: hn; left.
  have hg0 : g d = 0 by apply: contrapT=> h'; apply: hn; right.
  by rewrite hf0 hg0 addr0.
rewrite (slice_count_restrict hfgS) (slice_count_restrict hfS) (slice_count_restrict hgS).
exact: fsbig_split.
Qed.

(** Source for [slice_count_scale]: homogeneity of the counting
    functional, supporting Federer 2.5.14, p. 108. *)
Lemma slice_count_scale (c : R) (f : slice_index -> R) :
  slice_count (fun d => c * f d) = c * slice_count f.
Proof. by rewrite /slice_count mulr_fsumr. Qed.

(** Source for [slice_count_nonnegative]: positivity of the counting
    functional, supporting Federer 2.5.14, p. 108. *)
Lemma slice_count_nonnegative (f : slice_index -> R) :
  function_nonnegative f -> 0 <= slice_count f.
Proof. by move=> hf; apply: fsumr_ge0=> d _; exact: hf. Qed.

(** Source for [slice_count_monotone_daniell]: the counting functional
    is a monotone Daniell integral on K(D), supporting the counterexample
    in Federer 2.5.14, p. 108; the Daniell continuity is the first
    conclusion of 2.5.13, p. 106. *)
Theorem slice_count_monotone_daniell : is_monotone_daniell_integral KD slice_count.
Proof.
have hL := @compactly_supported_continuous_functions_lattice R slice_index.
have hmon := @positive_additive_lattice_functional_monotone R slice_index KD slice_count hL
  slice_count_add (fun f _ hf => slice_count_nonnegative hf).
have hD : is_daniell_integral KD slice_count.
  apply: (compact_support_order_bounded_daniell slice_index_hausdorff slice_index_locally_compact).
  - by split; [exact: slice_count_add|move=> c f _; exact: slice_count_scale].
  - move=> u hu; exists (slice_count u)=> k [hk [_ hku]]; exact: hmon hk hu.1 hku.
constructor.
- exact: slice_count_add.
- by move=> c f _ _; exact: slice_count_scale.
- by move=> f g hf hg hfg; exact: hmon.
- move=> f h hf hh hinc; split.
  + move=> n m hnm; rewrite lee_fin; apply: hmon=> // x.
    by have := (hinc x).1 n m hnm; rewrite lee_fin.
  + exact (daniell_integral_increasing_continuity hD hf hh hinc).
Qed.

(** Source for [slice_count_indicator]: the counting functional of the
    indicator of a finite set listed without repetitions is its number
    of elements, supporting the lower estimate in the counterexample to
    almost uniqueness, Federer 2.5.14, p. 108. *)
Lemma slice_count_indicator (s : seq slice_index) : uniq s ->
  slice_count (fun d => (d \in s)%:R) = (size s)%:R.
Proof.
move=> hs.
have hsub d : (d \in s)%:R <> 0 :> R -> [set` s] d.
  by case: (boolP (d \in s))=> // _; rewrite /= eqxx.
rewrite (slice_count_restrict hsub) -fsbig_seq //.
rewrite big_seq (eq_bigr (fun _ => 1)); last by move=> d ->.
by rewrite -big_seq -sum1_size natr_sum.
Qed.
End Space.

Section Line.
Variable R : realType.
Local Notation KR := (@compactly_supported_continuous_functions R R).

(** Source for [line_integral]: the Daniell integral on K(R) induced
    by the identity map of R, Federer 2.5.17, p. 111, used as the second
    factor of the counterexample to almost uniqueness in 2.5.14, p. 108.
    Its value on f in K(R) is the Riemann-Stieltjes integral of f with
    respect to the identity over a segment beyond which f vanishes. *)
Definition line_integral : (R -> R) -> R := induced_daniell (fun x : R => x).

(** Source for [line_identity_variation]: the identity map of R has
    locally finite variation, Federer 2.5.17, p. 111, as required for
    the induced Daniell integral. *)
Lemma line_identity_variation :
  curve_locally_finite_variation ((fun x : R => x) : R -> real_line_metric R).
Proof. exact: monotone_locally_finite_variation. Qed.

(** Source for [line_integral_monotone_daniell]: the integral induced by
    the identity is a monotone Daniell integral on K(R), Federer 2.5.17,
    p. 111, supporting 2.5.14, p. 108. *)
Lemma line_integral_monotone_daniell : is_monotone_daniell_integral KR line_integral.
Proof. exact: induced_daniell_monotone_daniell line_identity_variation (fun x y h => h). Qed.

(** Source for [line_bump_small]: supporting estimate for the
    counterexample in Federer 2.5.14, p. 108: for every e > 0 some
    nonnegative b in K(R) with b(0) = 1 vanishes outside the interval
    {t : -e < t < e} and has integral at most 2e. *)
Lemma line_bump_small (e : R) : 0 < e ->
  exists b, KR b /\ function_nonnegative b /\ b 0 = 1 /\ line_integral b <= 2 * e.
Proof.
move=> he; have [n hn] := positive_reciprocal_nat_small he.
have hb := @interval_bump_member R (- e) e n.
exists (interval_bump (- e) e n); split=> //.
split; first by move=> x; exact: interval_bump_ge0.
split.
  apply: interval_bump_inner_one; rewrite div1r; move: hn;
    set q := (n.+1%:R^-1 : R)=> hn; lra.
rewrite /line_integral (induced_daniell_value line_identity_variation hb (a := - e) (b := e)).
- apply: le_trans (stieltjes_integral_upper_bound line_identity_variation (fun x y h => h)
    (M := 1) (KR_continuous hb) _ _) _.
  + lra.
  + by move=> x _; exact: interval_bump_le1.
  + by rewrite mul1r opprK; lra.
- lra.
- by move=> x; exact: interval_bump_support.
Qed.

(** Source for [line_bump_positive]: supporting estimate for the
    counterexample in Federer 2.5.14, p. 108: for every e > 0 some b in
    K(R) with values in [0,1], vanishing outside {t : -e < t < e}, has
    positive integral. *)
Lemma line_bump_positive (e : R) : 0 < e ->
  exists b, KR b /\ (forall x, 0 <= b x <= 1) /\ (forall x, b x <> 0 -> - e < x < e) /\
    0 < line_integral b.
Proof.
move=> he; have he2 : 0 < e / 2 by lra.
have [n hn] := positive_reciprocal_nat_small he2.
have hb := @interval_bump_member R (- e) e n.
have hc := KR_continuous hb.
have hid := line_identity_variation.
have hmono : forall x y : R, x <= y -> x <= y by [].
exists (interval_bump (- e) e n); split=> //.
split; first by move=> x; rewrite interval_bump_ge0 interval_bump_le1.
split; first by move=> x; exact: interval_bump_support.
rewrite /line_integral (induced_daniell_value hid hb (a := - e) (b := e)); last 2 first.
- lra.
- by move=> x; exact: interval_bump_support.
have h1 : - e <= - (e / 2) by lra.
have h2 : - (e / 2) <= e / 2 by lra.
have h3 : e / 2 <= e by lra.
rewrite -(stieltjes_integral_cat hid hc h1 (le_trans h2 h3)).
rewrite -(stieltjes_integral_cat hid hc h2 h3).
have l1 := stieltjes_integral_lower_bound hid hmono (m := 0) hc h1
  (fun x _ => interval_bump_ge0 (- e) e n x).
have l3 := stieltjes_integral_lower_bound hid hmono (m := 0) hc h3
  (fun x _ => interval_bump_ge0 (- e) e n x).
have hin : forall x, - (e / 2) <= x <= e / 2 -> 1 <= interval_bump (- e) e n x.
  move=> x /andP[hx1 hx2]; rewrite interval_bump_inner_one // div1r; move: hn;
    set q := (n.+1%:R^-1 : R)=> hn; lra.
have l2 := stieltjes_integral_lower_bound hid hmono (m := 1) hc h2 hin.
rewrite !mul0r mul1r in l1 l2 l3.
lra.
Qed.
End Line.

Section Product.
Variable R : realType.
Variable D : choiceType.
Local Notation slice_index := (discrete_topology D).
Local Notation slice_space := (discrete_topology D * R)%type.
Local Notation KD := (@compactly_supported_continuous_functions R slice_index).
Local Notation KR := (@compactly_supported_continuous_functions R R).
Local Notation KX := (@compactly_supported_continuous_functions R slice_space).

(** Source for [slice_lambda]: the monotone Daniell integral lambda on
    K(X) of the counterexample to almost uniqueness in Federer 2.5.14,
    p. 108: the product, in the sense of 2.6.4, p. 119, of the counting
    functional on K(D) and the integral on K(R) induced by the identity.
    It is used only through the product law and the monotone Daniell
    laws. *)
Definition slice_lambda : (slice_space -> R) -> R :=
  @daniell_product R slice_index R (@slice_count R D) (@line_integral R)
    (@slice_index_hausdorff D) (@slice_index_locally_compact D) (@Rhausdorff R) (@locally_compactR R)
    (monotone_daniell_integral_is_daniell (@slice_count_monotone_daniell R D))
    (monotone_daniell_integral_is_daniell (@line_integral_monotone_daniell R)).

(** Source for [slice_lambda_specification]: lambda is the product of
    the counting functional and the line integral, Federer 2.6.4,
    p. 119, as used in 2.5.14, p. 108. *)
Lemma slice_lambda_specification :
  is_daniell_product (@slice_count R D) (@line_integral R) slice_lambda.
Proof. exact: daniell_product_specification. Qed.

(** Source for [slice_lambda_monotone_daniell]: lambda is a monotone
    Daniell integral on K(X), Federer 2.6.4, p. 119, as required in
    2.5.14, p. 107. *)
Theorem slice_lambda_monotone_daniell : is_monotone_daniell_integral KX slice_lambda.
Proof.
exact: (daniell_product_is_monotone (@slice_index_hausdorff D) (@slice_index_locally_compact D)
  (@Rhausdorff R) (@locally_compactR R) (@slice_count_monotone_daniell R D)
  (@line_integral_monotone_daniell R) slice_lambda_specification).
Qed.

(** Source for [slice_lambda_separated]: lambda(u . b) = A(u) B(b) for
    u in K(D) and b in K(R), Federer 2.6.4, p. 119, as used in the
    counterexample of 2.5.14, p. 108. *)
Lemma slice_lambda_separated (u : slice_index -> R) (b : R -> R) : KD u -> KR b ->
  slice_lambda (fun p : slice_space => u p.1 * b p.2) = slice_count u * line_integral b.
Proof. by move=> hu hb; exact: slice_lambda_specification.2. Qed.
End Product.
