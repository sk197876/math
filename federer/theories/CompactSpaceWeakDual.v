(** Federer (1969), 2.5.19, p. 113, third paragraph: "If X is a compact
    Hausdorff space, then the above defined weak topology coincides with the
    weak topology [see 2.5.12(2)] of K(X)* as the conjugate space of the
    vectorspace K(X) relative to the norm nu defined by the formula nu(f) =
    sup im |f| whenever f in K(X)." The vector space K(X) is any realisation
    in the sense of CompactFunctionSpaceUP.v, normed by the uniform norm;
    its conjugate space with the weak topology of 2.5.12(2), p. 103, is
    [weak_dual_space] of VectorDaniellHypotheses.v. The Daniell integrals on
    K(X) are total functionals whose weak topology in
    DaniellSpaceWeakTopology.v only sees their values on K(X). The
    coincidence is stated for every identification Phi of the conjugate
    space with Daniell integrals in the sense of CompactFunctionDualUP.v:
    Phi and the restriction map A |-> (v |-> A(ev v)) are mutually inverse
    up to agreement on K(X), both are continuous, and the open sets of the
    conjugate space are exactly the inverse images under Phi of the open
    sets of the weak topology of 2.5.19. The main ingredient is
    DaniellSpaceCompactSpace.v: for compact Hausdorff X the Daniell
    integrals on K(X) are the nu bounded linear functionals. The local
    erratum has no entry for p. 113. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground RealNormUP NormMetric NormMetricScaleContinuity
  CompactSupportFunctionUP CompactSupportFunctionLattice FunctionLatticeSeminormUP DaniellIntegralUP
  CompactFunctionSpaceUP CompactFunctionSpaceLaws CompactFunctionDualUP CompactFunctionDual
  VectorDaniellHypotheses VectorDaniellDualExtension DaniellSpaceWeakTopology DaniellSpaceCompactness
  DaniellSpaceCompactSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CompactWeakDual.
Variable R : realType.
Variable X : topologicalType.
Hypothesis hh : hausdorff_space X.
Hypothesis hc : compact (@setT X).
Variable V : lmodType R.
Variable ev : V -> X -> R.
Hypothesis hv : is_compact_function_space ev.
Local Notation K := (@compactly_supported_continuous_functions R X).
Local Notation N := (@compact_function_norm R X V ev).
(** Source for [hN]: the norm nu(f) = sup im |f| on K(X), Federer
    2.5.19, p. 113. *)
Let hN : is_real_norm N := compact_function_norm_laws hv.
Local Notation D := (weak_dual_space hN).

(** Source for [daniell_dual_restriction]: the passage from a
    functional A on functions on X to the functional v |-> A(ev v) on
    the vector space K(X), supporting the comparison of the two weak
    topologies in Federer 2.5.19, p. 113. *)
Definition daniell_dual_restriction (A : (X -> R) -> R) : weak_function_space V :=
  fun v => A (ev v).

(** Source for [daniell_dual_restriction_dual]: for compact Hausdorff
    X every Daniell integral on K(X) restricts to a nu continuous
    linear functional, Federer 2.5.19, p. 113, by the nu
    boundedness of DaniellSpaceCompactSpace.v. *)
Lemma daniell_dual_restriction_dual (A : (X -> R) -> R) :
  is_daniell_integral K A -> dual_space hN (daniell_dual_restriction A).
Proof.
move=> hA; have [[hadd hscale] [C [hC hb]]] := (compact_space_daniell_iff hh hc A).1 hA.
have hlin : forall c u v, A (ev (c *: u + v)) = c * A (ev u) + A (ev v).
  move=> c u v.
  rewrite (compact_function_evaluation_add hv) (hadd _ _ (compact_function_evaluation_member hv _)
    (compact_function_evaluation_member hv _)).
  by rewrite (compact_function_evaluation_scale hv) (hscale c _ (compact_function_evaluation_member hv u)).
split; first by move=> c u v; exact: hlin.
apply: (@metric_fixed_lipschitz_continuous R [the metricType R of real_norm_metric_space hN]
  [the metricType R of real_line_metric R] (daniell_dual_restriction A) C hC).
move=> u v; rewrite real_line_metric_distanceE real_norm_metric_distanceE.
have hsub : A (ev u) - A (ev v) = A (ev (u - v)).
  have h := hlin 1 v (u - v).
  rewrite scale1r mul1r addrC subrK in h.
  rewrite h; lra.
rewrite /daniell_dual_restriction hsub.
apply: (hb _ (compact_function_evaluation_member hv _) _ (real_seminorm_nonnegative hN.1 _)).
move=> x; exact: (@compact_function_evaluation_bound R X V ev hv (u - v) x).
Qed.

(** Source for [daniell_dual_restriction_continuous]: the restriction
    map is continuous from the weak topology of 2.5.19, p. 113, to the
    product topology of 2.5.12(2), p. 103, on the real functions on
    K(X); each coordinate is evaluation at a member of K(X). *)
Lemma daniell_dual_restriction_continuous :
  continuous (daniell_dual_restriction : daniell_weak_space K -> weak_function_space V).
Proof.
move=> A.
have hF : Filter (daniell_dual_restriction @ nbhs (A : daniell_weak_space K)) :=
  fmap_filter _ (@nbhs_filter (daniell_weak_space K) A).
apply/(@product_topology_cvg V (@weak_factor R V) _ _ hF)=> v.
exact: (@daniell_weak_evaluation_continuous R X K (ev v) (compact_function_evaluation_member hv v) A).
Qed.

(** Source for [daniell_dual_point]: the member of the conjugate
    space K(X)* of 2.5.12(2), p. 103, corresponding to a Daniell
    integral on K(X), Federer 2.5.19, p. 113. *)
Definition daniell_dual_point (A : (X -> R) -> R) (hA : is_daniell_integral K A) : D :=
  @exist (weak_function_space V) (fun alpha => alpha \in (dual_space hN : set (weak_function_space V)))
    (daniell_dual_restriction A) (mem_set (daniell_dual_restriction_dual hA)).

(** Source for [daniell_dual_pointE]: the functional underlying the
    point of K(X)* given by a Daniell integral A is v |-> A(ev v),
    Federer 2.5.19, p. 113. *)
Lemma daniell_dual_pointE (A : (X -> R) -> R) (hA : is_daniell_integral K A) :
  val (daniell_dual_point hA) = daniell_dual_restriction A.
Proof. by []. Qed.

Variable Phi : D -> daniell_weak_space K.
Hypothesis hPhi : is_compact_function_dual_identification ev Phi.

(** Source for [compact_dual_restriction_left_inverse]: restricting
    the Daniell integral Phi(a) recovers a, Federer 2.5.19, p. 113:
    Phi preserves the pairing with K(X). *)
Lemma compact_dual_restriction_left_inverse (a : D) : daniell_dual_restriction (Phi a) = val a.
Proof. by apply: funext=> v; exact: compact_function_dual_evaluation hPhi a v. Qed.

(** Source for [compact_dual_point_right_inverse]: Phi applied to the
    point of K(X)* given by a Daniell integral A agrees with A on K(X),
    Federer 2.5.19, p. 113. Only values on K(X) are determined. *)
Lemma compact_dual_point_right_inverse (A : (X -> R) -> R) (hA : is_daniell_integral K A) :
  forall f, K f -> Phi (daniell_dual_point hA) f = A f.
Proof.
move=> f hf; have [v <-] := compact_function_evaluation_surjective hv hf.
by rewrite (compact_function_dual_evaluation hPhi).
Qed.

(** Source for [compact_dual_identification_injective]: two members
    of K(X)* whose Daniell integrals agree on K(X) are equal, Federer
    2.5.19, p. 113. *)
Lemma compact_dual_identification_injective (a b : D) :
  (forall f, K f -> Phi a f = Phi b f) -> a = b.
Proof.
move=> hab; apply: val_inj; apply: funext=> v.
rewrite -!(compact_function_dual_evaluation hPhi); apply: hab.
exact: compact_function_evaluation_member hv v.
Qed.

(** Source for [daniell_weak_open_saturated]: an open set of the weak
    topology of 2.5.19, p. 113, contains with A every functional that
    agrees with A on K(X); the topology is induced from R^K(X). *)
Lemma daniell_weak_open_saturated (W : set (daniell_weak_space K)) (A B : (X -> R) -> R) :
  open W -> (forall f, K f -> A f = B f) -> W A -> W B.
Proof.
case=> O _ <- hAB; rewrite /preimage /=.
have -> : @daniell_restriction R X K B = @daniell_restriction R X K A.
  by apply: funext=> f; rewrite /daniell_restriction hAB //; exact: set_valP f.
by [].
Qed.

(** Source for [compact_dual_open_iff]: the open sets of K(X)* with
    the weak topology of 2.5.12(2), p. 103, are exactly the inverse
    images under Phi of the open sets of the weak topology of 2.5.19,
    p. 113. *)
Theorem compact_dual_open_iff (U : set D) :
  open U <-> exists2 W : set (daniell_weak_space K), open W & U = Phi @^-1` W.
Proof.
split.
- case=> O hO hOU.
  exists (daniell_dual_restriction @^-1` O).
    exact: (proj1 (continuousP _) daniell_dual_restriction_continuous O hO).
  rewrite -hOU; apply/seteqP; split=> a /=; rewrite /preimage /=;
    by rewrite compact_dual_restriction_left_inverse.
- move=> [W hW ->].
  exact: (proj1 (continuousP _) (compact_function_dual_continuous hPhi) W hW).
Qed.

(** Source for [compact_space_weak_topologies_coincide]: the complete
    assertion of Federer 2.5.19, p. 113, third paragraph, for compact
    Hausdorff X: Phi maps the conjugate space K(X)* of (K(X), nu),
    with the weak topology of 2.5.12(2), p. 103, into the Daniell
    integrals on K(X); it is onto and one to one up to agreement on
    K(X); it is continuous for the weak topology of 2.5.19; and the
    open sets of K(X)* are precisely the inverse images of the open
    sets of that weak topology, which in turn contain with each Daniell
    integral every functional agreeing with it on K(X). Thus Phi is a
    homeomorphism of K(X)* onto K(X)* with the topology of 2.5.19. *)
Theorem compact_space_weak_topologies_coincide :
  [/\ forall a, is_daniell_integral K (Phi a),
    forall A, is_daniell_integral K A -> exists a, forall f, K f -> Phi a f = A f,
    forall a b, (forall f, K f -> Phi a f = Phi b f) -> a = b,
    continuous Phi &
    forall U : set D, open U <-> exists2 W : set (daniell_weak_space K), open W & U = Phi @^-1` W].
Proof.
split.
- exact: compact_function_dual_daniell hPhi.
- move=> A hA; exists (daniell_dual_point hA); exact: compact_dual_point_right_inverse.
- exact: compact_dual_identification_injective.
- exact: compact_function_dual_continuous hPhi.
- exact: compact_dual_open_iff.
Qed.

End CompactWeakDual.

(** Source for [compact_function_dual_map_weak_homeomorphism]: the
    coincidence of Federer 2.5.19, p. 113, third paragraph, for the
    public identification [compact_function_dual_map] of
    CompactFunctionDual.v, used in 2.5.20, p. 114. *)
Theorem compact_function_dual_map_weak_homeomorphism (R : realType) (X : topologicalType)
    (V : lmodType R) (ev : V -> X -> R) (hv : is_compact_function_space ev)
    (hh : hausdorff_space X) (hc : compact (@setT X)) :
  let Phi := @compact_function_dual_map R X V ev hv hh hc in
  [/\ forall a, is_daniell_integral (@compactly_supported_continuous_functions R X) (Phi a),
    forall A, is_daniell_integral (@compactly_supported_continuous_functions R X) A ->
      exists a, forall f, compactly_supported_continuous_functions f -> Phi a f = A f,
    forall a b, (forall f, compactly_supported_continuous_functions f -> Phi a f = Phi b f) -> a = b,
    continuous Phi &
    forall U : set (weak_dual_space (compact_function_norm_laws hv)),
      open U <-> exists2 W : set (daniell_weak_space (@compactly_supported_continuous_functions R X)),
        open W & U = Phi @^-1` W].
Proof.
exact (@compact_space_weak_topologies_coincide R X hh hc V ev hv _
  (compact_function_dual_map_specification hv hh hc)).
Qed.
