(** Federer (1969), 2.5.19, p. 113, first paragraph: for a lattice L of
    functions on a set X, the set L* of all Daniell integrals on L is a
    vector space; the inclusion of L* in the cartesian product R^L endows L*
    with its weak topology; the map delta : X -> L* associates with each x
    the monotone Daniell integral delta_x(f) = f(x). The weak topology is
    the initial topology of the restriction map to the members of L, so that
    convergence is pointwise on L. The elements of L* are kept as total
    functionals on all functions, as in the predicate of 2.5.5; two
    functionals agreeing on L are therefore not identified. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws ExtendedRealOrderLimit
  MonotoneDaniellIntegralUP DaniellIntegralUP DaniellIntegralAlgebra DaniellIntegralNegation
  RealSequenceLimitArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [initial_topology_cvg]: supporting convergence criterion
    for the initial topology of a map, used for the weak topology of
    Federer 2.5.19, p. 113: a filter converges to s if and only if its
    image converges to f(s). *)
Lemma initial_topology_cvg (S : choiceType) (T : topologicalType) (f : S -> T)
    (F : set_system S) (s : S) :
  Filter F -> (F --> (s : initial_topology f) <-> f @ F --> f s).
Proof.
move=> FF; split=> h.
- move=> A hA; apply: h; have hc := @initial_continuous S T f s.
  exact: (hc A hA).
- move=> A; rewrite nbhsE => -[B [hBo hBs] hBA].
  case: hBo => V hV hVB.
  apply: filterS hBA _; rewrite -hVB; apply: h.
  by apply: open_nbhs_nbhs; split=> //; rewrite -hVB in hBs.
Qed.

(** Source for [product_topology_cvg]: supporting coordinatewise
    convergence criterion in the cartesian product of Federer 2.5.19,
    p. 113. *)
Lemma product_topology_cvg (I : Type) (T : I -> topologicalType)
    (F : set_system (forall i, T i)) (phi : forall i, T i) :
  Filter F ->
  (F --> (phi : prod_topology T) <-> forall i, (fun psi : forall i, T i => psi i) @ F --> phi i).
Proof.
move=> FF.
have h := @cvg_sup (forall i, T i) I
  (fun i => Topological.class (initial_topology (fun f : (forall i, T i) => f i))) F phi FF.
split=> hc.
- move=> i; have hi := h.1 hc i.
  exact: (@initial_topology_cvg _ _ (fun f : (forall i, T i) => f i) F phi FF).1 hi.
- apply: h.2 => i.
  exact: (@initial_topology_cvg _ _ (fun f : (forall i, T i) => f i) F phi FF).2 (hc i).
Qed.

(** Source for [real_sequence_limit_scale]: supporting positive
    homogeneity of real sequence limits, used for the vector space laws of
    Federer 2.5.19, p. 113. *)
Lemma real_sequence_limit_scale (R : realType) (u : nat -> R) (a c : R) :
  0 <= c -> extended_order_limit (fun n => (u n)%:E) a%:E ->
  extended_order_limit (fun n => (c * u n)%:E) (c * a)%:E.
Proof.
move=> hc [hlow hup]; case: (ltgtP 0 c)=> [hc0|hc0|hc0].
- split.
  + case=> [b|hb|_]; last by exists 0%N=> n _; rewrite ltNye.
    * rewrite lte_fin=> hb.
      have hb' : ((b / c)%:E < a%:E)%E by rewrite lte_fin ltr_pdivrMr // mulrC.
      have [N hN] := hlow _ hb'; exists N=> n hn.
      by have := hN n hn; rewrite !lte_fin ltr_pdivrMr // mulrC.
    * by move: hb; rewrite ltNge leey.
  + case=> [b|_|hb]; first last.
    * by move: hb; rewrite ltNge leNye.
    * by exists 0%N=> n _; rewrite ltey.
    * rewrite lte_fin=> hb.
      have hb' : (a%:E < (b / c)%:E)%E by rewrite lte_fin ltr_pdivlMr // mulrC.
      have [N hN] := hup _ hb'; exists N=> n hn.
      by have := hN n hn; rewrite !lte_fin ltr_pdivlMr // mulrC.
- by move: hc; rewrite leNgt hc0.
- rewrite -hc0; split.
  + by move=> b; rewrite mul0r=> hb; exists 0%N=> n _; rewrite mul0r.
  + by move=> b; rewrite mul0r=> hb; exists 0%N=> n _; rewrite mul0r.
Qed.

Section DaniellSpace.
Variable R : realType.
Variable X : Type.
Variable L : set (X -> R).

(** Source for [daniell_integrals]: the set L* of all Daniell integrals
    on L, Federer 2.5.19, p. 113. *)
Definition daniell_integrals : set ((X -> R) -> R) := [set A | is_daniell_integral L A].

(** Source for [daniell_integrals_add]: L* is closed under addition,
    first part of the vector space statement of Federer 2.5.19, p. 113. *)
Lemma daniell_integrals_add (A B : (X -> R) -> R) :
  daniell_integrals A -> daniell_integrals B -> daniell_integrals (fun f => A f + B f).
Proof.
move=> hA hB; constructor.
- move=> f g hf hg.
  by rewrite (daniell_integral_add hA hf hg) (daniell_integral_add hB hf hg) addrACA.
- move=> c f hc hf.
  by rewrite (daniell_integral_scale hA hc hf) (daniell_integral_scale hB hc hf) mulrDr.
- move=> f hf.
  have [a ha] := daniell_integral_order_bounded hA hf.
  have [b hb] := daniell_integral_order_bounded hB hf.
  by exists (a + b)=> k hk; exact: lerD (ha k hk) (hb k hk).
- move=> f g hfn hg hfg.
  exact: real_sequence_limit_add (daniell_integral_increasing_continuity hA hfn hg hfg)
    (daniell_integral_increasing_continuity hB hfn hg hfg).
Qed.

(** Source for [daniell_integrals_scale_nonnegative]: L* is closed under
    nonnegative real multiples, Federer 2.5.19, p. 113; no lattice law is
    needed for this part. *)
Lemma daniell_integrals_scale_nonnegative (c : R) (A : (X -> R) -> R) :
  0 <= c -> daniell_integrals A -> daniell_integrals (fun f => c * A f).
Proof.
move=> hc hA; constructor.
- by move=> f g hf hg; rewrite (daniell_integral_add hA hf hg) mulrDr.
- by move=> d f hd hf; rewrite (daniell_integral_scale hA hd hf) mulrCA.
- move=> f hf; have [b hb] := daniell_integral_order_bounded hA hf.
  by exists (c * b)=> k hk; apply: ler_wpM2l=> //; exact: hb k hk.
- move=> f g hfn hg hfg.
  exact: real_sequence_limit_scale hc (daniell_integral_increasing_continuity hA hfn hg hfg).
Qed.

(** Source for [daniell_integrals_scale]: L* is closed under all real
    multiples, Federer 2.5.19, p. 113; negative multiples use the
    negation law of 2.5.5 and hence the lattice laws of L. *)
Lemma daniell_integrals_scale (c : R) (A : (X -> R) -> R) :
  is_function_lattice L -> daniell_integrals A -> daniell_integrals (fun f => c * A f).
Proof.
move=> hL hA; case: (lerP 0 c)=> hc; first exact: daniell_integrals_scale_nonnegative hc hA.
have hn : daniell_integrals (fun f => - A f) := daniell_integral_negate hL hA.
have hc' : 0 <= - c by rewrite oppr_ge0 (ltW hc).
have h := daniell_integrals_scale_nonnegative hc' hn.
have -> : (fun f => c * A f) = (fun f => - c * - A f) by apply: funext=> f; rewrite mulrNN.
exact: h.
Qed.

(** Source for [daniell_integrals_zero]: the zero functional belongs to
    L*, Federer 2.5.19, p. 113. *)
Lemma daniell_integrals_zero : daniell_integrals (fun _ => 0).
Proof.
constructor.
- by move=> f g _ _; rewrite addr0.
- by move=> c f _ _; rewrite mulr0.
- by move=> f _; exists 0.
- move=> f g _ _ _; split.
  + by move=> a ha; exists 0%N.
  + by move=> b hb; exists 0%N.
Qed.

(** Source for [daniell_integrals_opp]: L* is closed under negation,
    Federer 2.5.19, p. 113, by the negation law proved for 2.5.5. *)
Lemma daniell_integrals_opp (A : (X -> R) -> R) :
  is_function_lattice L -> daniell_integrals A -> daniell_integrals (fun f => - A f).
Proof. by move=> hL hA; exact: daniell_integral_negate hL hA. Qed.

(** Source for [daniell_restriction]: the inclusion of L* in the
    cartesian product R^L of Federer 2.5.19, p. 113, extended to all
    functionals: a functional is sent to its restriction to the members
    of L. *)
Definition daniell_restriction : ((X -> R) -> R) -> prod_topology (fun _ : L => R) :=
  fun A f => A (val f).

(** Source for [daniell_weak_space]: the functionals on functions on X
    with the weak topology of Federer 2.5.19, p. 113, namely the initial
    topology of the inclusion in R^L. *)
Definition daniell_weak_space := initial_topology daniell_restriction.

(** Source for [daniell_weak_cvg]: convergence in the weak topology of
    Federer 2.5.19, p. 113, is convergence of the values on every member
    of L. *)
Lemma daniell_weak_cvg (F : set_system ((X -> R) -> R)) (A : (X -> R) -> R) :
  Filter F ->
  (F --> (A : daniell_weak_space) <->
    forall f, L f -> (fun B : (X -> R) -> R => B f) @ F --> A f).
Proof.
move=> FF; rewrite (@initial_topology_cvg _ _ daniell_restriction F A FF).
have := @product_topology_cvg L (fun _ => R) (daniell_restriction @ F) (daniell_restriction A)
  (fmap_filter _ FF).
move=> ->; split=> h f.
- by move=> hf; exact: h (exist _ f (mem_set hf)).
- exact: h (val f) (set_valP f).
Qed.

(** Source for [daniell_weak_open_preimage]: the open sets of the weak
    topology of Federer 2.5.19, p. 113, are the inverse images of the
    open subsets of R^L. *)
Lemma daniell_weak_open_preimage (V : set (prod_topology (fun _ : L => R))) :
  open V -> open (daniell_restriction @^-1` V : set daniell_weak_space).
Proof. by move=> hV; exists V. Qed.

(** Source for [daniell_weak_evaluation_continuous]: evaluation at a
    member of L is continuous for the weak topology of Federer 2.5.19,
    p. 113. *)
Lemma daniell_weak_evaluation_continuous (f : X -> R) :
  L f -> continuous (fun A : daniell_weak_space => A f).
Proof.
move=> hf A.
have hF : Filter (nbhs (A : daniell_weak_space)) :=
  @nbhs_filter [the topologicalType of daniell_weak_space] A.
have h := (@daniell_weak_cvg (nbhs (A : daniell_weak_space)) A hF).1 (@cvg_refl _ _) f hf.
exact: h.
Qed.

(** Source for [daniell_weak_strip_open]: the sets {A : a < A(f) < b}
    for f in L are open in the weak topology, Federer 2.5.19, p. 113,
    compared with the weak topology of 2.5.12(2), p. 103. *)
Lemma daniell_weak_strip_open (f : X -> R) (a b : R) :
  L f -> open [set A : daniell_weak_space | a < A f /\ A f < b].
Proof.
move=> hf; have hc := daniell_weak_evaluation_continuous hf.
have -> : [set A : daniell_weak_space | a < A f /\ A f < b]
  = (fun A : daniell_weak_space => A f) @^-1` ([set t | a < t] `&` [set t | t < b]) by [].
apply: open_comp; first by move=> A _; exact: hc A.
by apply: openI; [exact: open_gt | exact: open_lt].
Qed.

(** Source for [point_evaluation]: the map delta of Federer 2.5.19,
    p. 113, with delta_x(f) = f(x). *)
Definition point_evaluation (x : X) : (X -> R) -> R := fun f => f x.

(** Source for [point_evaluation_monotone_daniell]: delta_x is a monotone
    Daniell integral on L, Federer 2.5.19, p. 113. *)
Lemma point_evaluation_monotone_daniell (x : X) :
  is_monotone_daniell_integral L (point_evaluation x).
Proof.
constructor=> //.
- by move=> f g _ _ hfg; exact: hfg x.
- by move=> f g _ _ hfg; exact: hfg x.
Qed.

(** Source for [point_evaluation_daniell]: delta maps X into L*,
    Federer 2.5.19, p. 113. *)
Lemma point_evaluation_daniell (x : X) : daniell_integrals (point_evaluation x).
Proof. exact: monotone_daniell_is_daniell (point_evaluation_monotone_daniell x). Qed.

(** Source for [point_evaluation_span]: the vector space generated by
    the image of delta, Federer 2.5.19, p. 113: the finite linear
    combinations of point evaluations. *)
Definition point_evaluation_span : set ((X -> R) -> R) :=
  [set A | exists s : seq (R * X), A = fun f => \sum_(p <- s) p.1 * f p.2].

(** Source for [point_evaluation_span_evaluation]: the span contains the
    image of delta, Federer 2.5.19, p. 113. *)
Lemma point_evaluation_span_evaluation (x : X) : point_evaluation_span (point_evaluation x).
Proof. by exists [:: (1, x)]; apply: funext=> f; rewrite big_seq1 /= mul1r. Qed.

(** Source for [point_evaluation_span_zero]: the span contains zero,
    Federer 2.5.19, p. 113. *)
Lemma point_evaluation_span_zero : point_evaluation_span (fun _ => 0).
Proof. by exists [::]; apply: funext=> f; rewrite big_nil. Qed.

(** Source for [point_evaluation_span_add]: the span is closed under
    addition, Federer 2.5.19, p. 113. *)
Lemma point_evaluation_span_add (A B : (X -> R) -> R) :
  point_evaluation_span A -> point_evaluation_span B -> point_evaluation_span (fun f => A f + B f).
Proof.
move=> [s ->] [t ->]; exists (s ++ t); apply: funext=> f.
by rewrite big_cat.
Qed.

(** Source for [point_evaluation_span_scale]: the span is closed under
    real multiples, Federer 2.5.19, p. 113. *)
Lemma point_evaluation_span_scale (c : R) (A : (X -> R) -> R) :
  point_evaluation_span A -> point_evaluation_span (fun f => c * A f).
Proof.
move=> [s ->]; exists [seq (c * p.1, p.2) | p <- s]; apply: funext=> f.
by rewrite big_map mulr_sumr; apply: eq_bigr=> p _; rewrite /= mulrA.
Qed.

(** Source for [point_evaluation_span_least]: the span is the smallest
    vector space of functionals containing the image of delta, Federer
    2.5.19, p. 113. *)
Lemma point_evaluation_span_least (V : set ((X -> R) -> R)) :
  V (fun _ => 0) -> (forall x, V (point_evaluation x)) ->
  (forall A B, V A -> V B -> V (fun f => A f + B f)) ->
  (forall c A, V A -> V (fun f => c * A f)) ->
  point_evaluation_span `<=` V.
Proof.
move=> h0 hx hadd hsc A [s ->]; elim: s=> [|p s ih].
- have -> : (fun f : X -> R => \sum_(q <- [::]) q.1 * f q.2) = (fun _ => 0).
    by apply: funext=> f; rewrite big_nil.
  exact: h0.
- have -> : (fun f : X -> R => \sum_(q <- p :: s) q.1 * f q.2)
    = (fun f => p.1 * point_evaluation p.2 f + \sum_(q <- s) q.1 * f q.2).
    by apply: funext=> f; rewrite big_cons.
  apply: hadd ih; exact: hsc (hx p.2).
Qed.

(** Source for [point_evaluation_span_daniell]: the vector space
    generated by the image of delta lies in L*, Federer 2.5.19, p. 113. *)
Lemma point_evaluation_span_daniell :
  is_function_lattice L -> point_evaluation_span `<=` daniell_integrals.
Proof.
move=> hL; apply: point_evaluation_span_least.
- exact: daniell_integrals_zero.
- exact: point_evaluation_daniell.
- exact: daniell_integrals_add.
- by move=> c A; exact: daniell_integrals_scale hL.
Qed.

End DaniellSpace.

Section PointEvaluationContinuity.
Variable R : realType.
Variable X : topologicalType.
Variable L : set (X -> R).

(** Source for [point_evaluation_continuous]: delta is continuous for the
    weak topology when the members of L are continuous, the first half of
    the embedding statement of Federer 2.5.19, p. 113, for K(X). *)
Lemma point_evaluation_continuous :
  (forall f, L f -> continuous f) ->
  continuous (@point_evaluation R X : X -> daniell_weak_space L).
Proof.
move=> hc; apply: continuous_comp_initial=> x.
have hF : Filter ((@daniell_restriction R X L \o @point_evaluation R X) @ nbhs x) :=
  fmap_filter _ (nbhs_filter x).
apply/(product_topology_cvg _ hF)=> f.
exact: hc (val f) (set_valP f) x.
Qed.

End PointEvaluationContinuity.
