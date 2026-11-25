(** Federer (1969), 2.5.19, p. 113, last paragraph: if u : X -> Y is a
    continuous proper map of locally compact Hausdorff spaces, there is a
    unique continuous linear map u_* : K(X)* -> K(Y)* with u_* o delta_X =
    delta_Y o u; in fact <f, u_*(mu)> = <f o u, mu> for f in K(Y) and mu in
    K(X)*. For a monotone Daniell integral lambda on K(X) and a measure phi
    representing it, 2.4.18 gives <f, u_*(lambda)> = int f d(u_# phi) for f
    in K(Y). Existence is the explicit formula, and uniqueness is proved
    from the density of the span of the image of delta. The final remark
    that u_# phi need not be K(Y) regular is formalised in
    DaniellSpaceImageRegularity.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground FunctionLatticeUP FunctionLatticeLaws
  MonotoneDaniellIntegralUP DaniellIntegralUP DaniellIntegralAlgebra CompactSupportFunctionUP
  CompactSupportFunctionLattice ProperMapUP MeasureUP MeasurePushforward PartialFunctionUP
  PartialFunctionPrecomposition MeasureIntegralUP MeasureIntegralGraphEquivalence
  SummableRealFunctionUP RealIntegralFunctionalUP PushforwardIntegral
  DaniellSpaceWeakTopology DaniellSpaceDensity DaniellSpaceCompactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Pushforward.
Variable R : realType.
Variables X Y : topologicalType.
Variable u : X -> Y.
Hypothesis hu : continuous u.
Hypothesis hp : is_proper_map u.
Local Notation KX := (@compactly_supported_continuous_functions R X).
Local Notation KY := (@compactly_supported_continuous_functions R Y).

(** Source for [compactly_supported_compose]: f o u belongs to K(X) for
    f in K(Y), since spt(f o u) lies in the compact set u^{-1}(spt f);
    supporting the formula <f, u_*(mu)> = <f o u, mu> of Federer 2.5.19,
    p. 113. *)
Lemma compactly_supported_compose (f : Y -> R) :
  compactly_supported_continuous_functions f -> compactly_supported_continuous_functions (f \o u).
Proof.
move=> [hf hs]; split.
- move=> x; apply: continuous_comp; [exact: hu | exact: hf].
- apply: (@real_function_compact_support_in_closed_set R X _ (u @^-1` real_function_support f)).
  + exact: hp hs.
  + apply: preimage_closed; last exact: real_function_support_closed.
    by move=> x _; exact: hu.
  + by move=> x hx; exact: real_function_zero_off_support hx.
Qed.

(** Source for [daniell_pushforward]: the map u_* of Federer 2.5.19, p. 113,
    given by <f, u_*(mu)> = <f o u, mu> *)
Definition daniell_pushforward (A : (X -> R) -> R) : (Y -> R) -> R := fun f => A (f \o u).

(** Source for [daniell_pushforward_daniell]: u_* maps K(X)* into K(Y)*,
    Federer 2.5.19, p. 113 *)
Lemma daniell_pushforward_daniell (A : (X -> R) -> R) :
  is_daniell_integral KX A -> is_daniell_integral KY (daniell_pushforward A).
Proof.
move=> hA; constructor.
- move=> f g hf hg.
  exact: (daniell_integral_add hA (compactly_supported_compose hf) (compactly_supported_compose hg)).
- move=> c f hc hf; exact: (daniell_integral_scale hA hc (compactly_supported_compose hf)).
- move=> f hf; have [b hb] := daniell_integral_order_bounded hA (compactly_supported_compose hf).
  exists b=> k [hk [hk0 hkf]]; apply: hb; split; first exact: compactly_supported_compose hk.
  by split=> x; [exact: hk0 | exact: hkf].
- move=> f g hfn hg hfg.
  apply: (daniell_integral_increasing_continuity hA (fun n => compactly_supported_compose (hfn n))
    (compactly_supported_compose hg)).
  by move=> x; exact: hfg (u x).
Qed.

(** Source for [daniell_pushforward_monotone]: u_* maps monotone Daniell
    integrals to monotone Daniell integrals, Federer 2.5.19, p. 113. *)
Lemma daniell_pushforward_monotone (A : (X -> R) -> R) :
  is_monotone_daniell_integral KX A -> is_monotone_daniell_integral KY (daniell_pushforward A).
Proof.
move=> hA; constructor.
- move=> f g hf hg.
  exact: (monotone_daniell_integral_add hA (compactly_supported_compose hf)
    (compactly_supported_compose hg)).
- move=> c f hc hf; exact: (monotone_daniell_integral_scale hA hc (compactly_supported_compose hf)).
- move=> f g hf hg hfg.
  apply: (monotone_daniell_integral_monotone hA (compactly_supported_compose hf)
    (compactly_supported_compose hg)).
  by move=> x; exact: hfg (u x).
- move=> f g hfn hg hfg.
  apply: (monotone_daniell_integral_increases hA (fun n => compactly_supported_compose (hfn n))
    (compactly_supported_compose hg)).
  by move=> x; exact: hfg (u x).
Qed.

(** Source for [daniell_pushforward_point_evaluation]: the commutative
    diagram u_* o delta_X = delta_Y o u of Federer 2.5.19, p. 113. *)
Lemma daniell_pushforward_point_evaluation (x : X) :
  daniell_pushforward (@point_evaluation R X x) = @point_evaluation R Y (u x).
Proof. by []. Qed.

(** Source for [daniell_pushforward_add]: u_* is additive, Federer
    2.5.19, p. 113. *)
Lemma daniell_pushforward_add (A B : (X -> R) -> R) :
  daniell_pushforward (fun f => A f + B f) = (fun g => daniell_pushforward A g + daniell_pushforward B g).
Proof. by []. Qed.

(** Source for [daniell_pushforward_scale]: u_* is homogeneous, Federer
    2.5.19, p. 113. *)
Lemma daniell_pushforward_scale (c : R) (A : (X -> R) -> R) :
  daniell_pushforward (fun f => c * A f) = (fun g => c * daniell_pushforward A g).
Proof. by []. Qed.

(** Source for [daniell_pushforward_continuous]: u_* is continuous for
    the weak topologies of K(X)* and K(Y)*, Federer 2.5.19, p. 113. *)
Lemma daniell_pushforward_continuous :
  continuous (daniell_pushforward : daniell_weak_space KX -> daniell_weak_space KY).
Proof.
apply: continuous_comp_initial=> A.
have hF : Filter ((@daniell_restriction R Y KY \o daniell_pushforward) @ nbhs (A : daniell_weak_space KX)) :=
  fmap_filter _ (@nbhs_filter [the topologicalType of daniell_weak_space KX] A).
apply/(product_topology_cvg _ hF)=> g.
have hgu := compactly_supported_compose (set_valP g).
exact (@daniell_weak_evaluation_continuous R X KX (val g \o u) hgu A).
Qed.

(** Source for [daniell_pushforward_unique]: uniqueness of u_* in
    Federer 2.5.19, p. 113: a map T of K(X)* into functionals on Y which
    is continuous at every point of K(X)* relative to K(X)*, additive and
    homogeneous on K(X)* and satisfies T o delta_X = delta_Y o u on K(Y)
    agrees with u_* on K(Y). *)
Theorem daniell_pushforward_unique (T : daniell_weak_space KX -> daniell_weak_space KY) :
  (forall A, daniell_integrals KX A ->
    T @ within (daniell_integrals KX) (nbhs (A : daniell_weak_space KX)) --> T A) ->
  (forall A B, daniell_integrals KX A -> daniell_integrals KX B -> forall g, KY g ->
    T (fun f => A f + B f) g = T A g + T B g) ->
  (forall c A, daniell_integrals KX A -> forall g, KY g -> T (fun f => c * A f) g = c * T A g) ->
  (forall x g, KY g -> T (@point_evaluation R X x) g = g (u x)) ->
  forall A, daniell_integrals KX A -> forall g, KY g -> T A g = daniell_pushforward A g.
Proof.
move=> hcont hadd hscale hpt A hA g hg.
have hL := @compactly_supported_continuous_functions_lattice R X.
have hgu := compactly_supported_compose hg.
have h0 : daniell_integrals KX (fun _ => 0) := @daniell_integrals_zero R X KX.
have hT0 : T (fun _ => 0) g = 0.
  have h := hadd _ _ h0 h0 g hg.
  rewrite (_ : (fun f : X -> R => 0 + 0) = (fun _ => 0)) in h; last first.
    by apply: funext=> f; rewrite addr0.
  lra.
have hspan : forall s : seq (R * X),
    T (fun h => \sum_(p <- s) p.1 * h p.2) g = \sum_(p <- s) p.1 * g (u p.2).
  elim=> [|p s ih].
  - rewrite big_nil (_ : (fun h : X -> R => \sum_(q <- [::]) q.1 * h q.2) = (fun _ => 0)) //.
    by apply: funext=> h; rewrite big_nil.
  - have hA1 : daniell_integrals KX (fun h => p.1 * @point_evaluation R X p.2 h) :=
      daniell_integrals_scale p.1 hL (point_evaluation_daniell KX p.2).
    have hB1 : daniell_integrals KX (fun h => \sum_(q <- s) q.1 * h q.2).
      by apply: (point_evaluation_span_daniell hL); exists s.
    rewrite (_ : (fun h : X -> R => \sum_(q <- p :: s) q.1 * h q.2)
      = (fun h => p.1 * @point_evaluation R X p.2 h + \sum_(q <- s) q.1 * h q.2)); last first.
      by apply: funext=> h; rewrite big_cons.
    rewrite (hadd _ _ hA1 hB1 g hg) ih big_cons.
    by rewrite (hscale p.1 _ (point_evaluation_daniell KX p.2) g hg) (hpt p.2 g hg).
apply/eqP; rewrite -subr_eq0 -normr_eq0 eq_le normr_ge0 andbT.
apply/ler_addgt0Pr=> e he; rewrite add0r.
have he2 : 0 < e / 2 by lra.
have hW1 : nbhs (A : daniell_weak_space KX)
    [set B | daniell_integrals KX B -> `|T B g - T A g| < e / 2].
  have hV : nbhs (T A) [set C : daniell_weak_space KY | `|C g - T A g| < e / 2].
    exact (@daniell_weak_evaluation_continuous R Y KY g hg (T A) _ (real_ball_nbhs (T A g) he2)).
  exact: (hcont A hA _ hV).
have hW2 : nbhs (A : daniell_weak_space KX)
    [set B : daniell_weak_space KX | `|B (g \o u) - A (g \o u)| < e / 2].
  exact (@daniell_weak_evaluation_continuous R X KX (g \o u) hgu A _ (real_ball_nbhs (A (g \o u)) he2)).
have hW := @filterI _ _ (@nbhs_filter [the topologicalType of daniell_weak_space KX] A) _ _ hW1 hW2.
have [nu [[s hs] [h1 h2]]] := point_evaluation_span_dense hL hA hW.
have hnu : daniell_integrals KX nu by apply: (point_evaluation_span_daniell hL); exists s.
have heq : T nu g = nu (g \o u) by rewrite hs hspan.
have h1' : `|T nu g - T A g| < e / 2 := h1 hnu.
have h2' : `|nu (g \o u) - A (g \o u)| < e / 2 := h2.
rewrite heq distrC in h1'.
have h3 := ler_distD (nu (g \o u)) (T A g) (A (g \o u)).
rewrite /daniell_pushforward; lra.
Qed.

(** Source for [daniell_pushforward_integral]: if phi is a measure over X
    representing a Daniell integral lambda on K(X), then the image measure
    u_# phi represents u_*(lambda) on K(Y), that is <f, u_*(lambda)> = int f
    d(u_# phi) for f in K(Y), by 2.4.18; Federer 2.5.19, p. 113. *)
Theorem daniell_pushforward_integral (phi : set X -> \bar R) (A : (X -> R) -> R) :
  is_measure phi -> is_real_integral_functional phi KX A ->
  is_real_integral_functional (measure_pushforward u phi) KY (daniell_pushforward A).
Proof.
move=> hm hi g hg.
have h := hi _ (compactly_supported_compose hg).
have h' : is_measure_integral phi (partial_function_precompose u (real_total_integrand g))
    (A (g \o u))%:E.
  by apply: (measure_integral_graph_equivalent _ h)=> x z; split=> hz; exact: hz.
exact ((measure_pushforward_integral_iff hm h'.1 _).1 h').
Qed.

End Pushforward.
