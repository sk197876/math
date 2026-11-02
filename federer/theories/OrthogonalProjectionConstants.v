(** Federer (1969), 2.7.16, printed p. 139, example (6): "Whenever n >= m
    are positive integers and 1 <= t < oo, there exists a positive number
    beta_t(n, m) such that (int |(Lambda_m p) xi|^t dtheta*_{n,m} p)^{1/t} =
    beta_t(n, m) . |xi| for every simple m-vector xi of R^n. In fact the
    integral is positively homogeneous of degree t with respect to xi, the
    group O(n) acts transitively on the set of all simple m vectors of norm
    1, and the invariance of theta*_{n,m} implies the integrals
    corresponding to xi and (Lambda_m g) xi are equal whenever g in O(n)."
    The number beta_t(n, m) is introduced by the predicate
    is_projection_constant, which states the displayed equation for every
    normalised invariant measure theta*_{n,m} of O*(n, m) (2.7.16, p. 139;
    EuclideanOrthogonalInvariantMeasures.v) and every restricted group
    structure of O(n); later results use only this predicate. Existence and
    uniqueness are proved for m <= n and t > 0. The integrand p |->
    |(Lambda_m p) xi|^t is continuous (ExteriorMapNormContinuity.v), hence a
    member of K(O*(n, m)) (2.5.13, p. 106), and its integral is the value of
    the invariant integral nu represented by theta*_{n,m}. A nonzero simple
    xi is c e_1 wedge ... wedge e_m with e orthonormal and |c| = |xi|
    (1.7.5, p. 32), which gives the homogeneity. For two orthonormal
    m-families e, e' there is g in O(n) with g(e_i) = e'_i
    (OrthogonalInjectionSpaces.v), so that |(Lambda_m p)(e'_1 wedge ...
    wedge e'_m)| = |(Lambda_m(p o g))(e_1 wedge ... wedge e_m)|, and the
    invariance of nu gives equal integrals. This is the transitivity used by
    Federer, applied to orthonormal frames, on which the integrand depends
    only up to the sign of the m-vector. The integral is positive by 1.7.7,
    p. 34 (some p in O*(n, m) has |(Lambda_m p) xi| = |xi|), the continuity
    of the integrand and the positivity of nonzero invariant integrals
    (InvariantIntegralPositivity.v). The local erratum has no entry for p.
    139. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals topology
  constructive_ereal.
From Federer Require Import TensorUP InnerProductUP InnerNorm InnerMetric LinearBasis Hom HomInner
  OrthogonalMaps OrthonormalFamilies AdjointUP Adjoint GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates CoordinateProjection OrthonormalFrameMap IsotropyGroupTopology TopologicalGroupUP
  TopologicalGroupLaws HomogeneousSpaceUP RealMetricBackground CompactSupportFunctionUP
  FunctionLatticeUP DaniellIntegralUP MonotoneDaniellIntegralUP MonotoneDaniellIntegralLaws
  DaniellIntegralNegation CovariantIntegralUP HaarIntegralUP RealIntegralFunctionalUP
  SummableRealFunctionUP MeasureUP MeasureIntegralUP MeasureIntegralUniqueness ExtendedPositivePower
  RealPower RealPowerContinuity HomSpaceTopology LinearGroupTopology LinearGroupSealed
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure CompactGroupHaarNormalisation
  CompactGroupHomogeneousMeasures OrthogonalInjectionSpaces EuclideanOrthogonalInvariantMeasures
  InvariantIntegralPositivity ExteriorGrading ExteriorMaps ExteriorMapScaling FiniteExteriorPowers
  InnerExterior ExteriorNorm ExteriorProjectionNorm AssociatedSubspace SimpleElementary
  SimpleOrthonormalFactor SimpleProjectionAttainment ExteriorMapNormContinuity DaniellSpaceCompactSpace
  CompactSupportFunctionLattice.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ProjectionNorm.
Variable R : realType.
Hypothesis h2 : (1 + 1 : R) != 0.
Variables n m : nat.
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hBm := (@euclidean_inner_productP R m).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation hbm := (@coordinate_basisP R m).
Local Notation OP := (set_type (euclidean_orthogonal_projections R n m)).

(** Source for [projection_norm]: the function p |-> |(Lambda_m p) xi|
    on O*(n, m), Federer 2.7.16, p. 139, written f(p) = |<xi, Lambda_m p>|
    on p. 140. Definition. *)
Definition projection_norm (xi : exterior_power (R_n R n) m) (p : OP) : R :=
  exterior_norm h2 hBm (exterior_power_map (hom_as_linear (orthogonal_projection_map p)) m xi).

(** Source for [projection_norm_nonnegative]: |(Lambda_m p) xi| >= 0,
    Federer 1.7.5, p. 32, for the integrand of 2.7.16, p. 139.
    Supporting lemma. *)
Lemma projection_norm_nonnegative xi p : 0 <= projection_norm xi p.
Proof. exact: exterior_norm_nonnegative. Qed.

(** Source for [projection_norm_scale]: |(Lambda_m p)(c xi)| =
    |c| |(Lambda_m p) xi|, the homogeneity in "the integral is positively
    homogeneous of degree t with respect to xi", Federer 2.7.16, p. 139.
    Supporting lemma. *)
Lemma projection_norm_scale (c : R) xi p : projection_norm (c *: xi) p = `|c| * projection_norm xi p.
Proof. by rewrite /projection_norm linearZ exterior_norm_scale. Qed.

(** Source for [projection_norm_zero]: the integrand vanishes for
    xi = 0, Federer 2.7.16, p. 139. Supporting lemma. *)
Lemma projection_norm_zero p : projection_norm 0 p = 0.
Proof. by rewrite /projection_norm linear0 exterior_norm_zero. Qed.

(** Source for [projection_norm_bound]: |(Lambda_m p) xi| <= |xi| for p
    in O*(n, m), the first inequality of the proof of 1.7.7, p. 34, used
    in Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma projection_norm_bound xi p : projection_norm xi p <= exterior_norm h2 hBn xi.
Proof.
exact: (@exterior_projection_norm_bound R h2 _ _ _ _ hBn hBm _
  (orthogonal_projection_map_projection p) m xi).
Qed.

(** Source for [projection_norm_continuous]: p |-> |(Lambda_m p) xi| is
    continuous on O*(n, m) for simple xi, supporting the integrals of
    Federer 2.7.16, pp. 139-140. Supporting lemma. *)
Lemma projection_norm_continuous xi : simple xi -> continuous (projection_norm xi : OP -> real_line_metric R).
Proof.
move=> hs p.
exact: (continuous_comp (@set_type_val_continuous _ (euclidean_orthogonal_projections R n m) p)
  (@exterior_map_norm_continuous R h2 (R_n R n) (R_n R m) _ _ hBn hBm n _ hbn m xi hs (set_val p))).
Qed.

(** Source for [projection_norm_power_continuous]: p |-> |(Lambda_m p)
    xi|^t is continuous on O*(n, m) for simple xi and t > 0, the
    integrand of Federer 2.7.16, p. 139. Supporting lemma. *)
Lemma projection_norm_power_continuous xi (t : R) : simple xi -> 0 < t ->
  continuous ((fun p => real_power (projection_norm xi p) t) : OP -> real_line_metric R).
Proof.
move=> hs ht; apply: real_power_continuous_comp=> //; first exact: projection_norm_continuous.
exact: projection_norm_nonnegative.
Qed.

(** Source for [projection_norm_e_lambda]: (Lambda_m p)(e_1 wedge ...
    wedge e_m) = p(e_1) wedge ... wedge p(e_m), Federer 1.3.1, p. 14, in
    the integrand of 2.7.16, p. 139. Supporting lemma. *)
Lemma projection_norm_e_lambda (e : 'I_m -> R_n R n) p :
  projection_norm (e_lambda e (ord_tuple m)) p =
    exterior_norm h2 hBm (e_lambda (fun i => orthogonal_projection_map p (e i)) (ord_tuple m)).
Proof.
by rewrite /projection_norm exterior_power_map_e_lambda.
Qed.

Variables (mulS : euclidean_orthogonal_group R n -> euclidean_orthogonal_group R n ->
    euclidean_orthogonal_group R n)
  (invS : euclidean_orthogonal_group R n -> euclidean_orthogonal_group R n)
  (eS : euclidean_orthogonal_group R n).
Hypothesis hS : is_subgroup_restriction (linear_group_mul hBn hbn) (linear_group_inv hBn hbn)
  (linear_group_unit hBn hbn) (euclidean_orthogonal_group R n) mulS invS eS.
Local Notation A := (orthogonal_projection_action hBm hBn hbn hS).
Local Notation K := (@compactly_supported_continuous_functions R OP).
Local Notation om := (@orthogonal_element_map R (R_n R n) _ hBn n _ hbn).

(** Source for [hOG]: the group laws of O(n), Federer 2.7.16, p. 139,
    used in this section. *)
Let hOG : is_group_laws mulS invS eS := topological_group_laws (lch_group_topological (orthogonal_group_lch hS)).

(** Source for [projection_space_compact]: O*(n, m) is compact, Federer
    2.7.16, p. 139. Supporting lemma. *)
Lemma projection_space_compact : compact [set: OP].
Proof. exact: (orthogonal_projections_compact hbm hS). Qed.

(** Source for [projection_space_continuous_compact]: every continuous
    real function on O*(n, m) belongs to K(O*(n, m)), Federer 2.5.13,
    p. 106, since O*(n, m) is compact (2.7.16, p. 139). Supporting
    lemma. *)
Lemma projection_space_continuous_compact (u : OP -> R) :
  continuous (u : OP -> real_line_metric R) -> K u.
Proof.
move=> hu; split=> //.
apply: (real_function_compact_support_in_closed_set projection_space_compact closedT).
by move=> x hx; exfalso; exact: hx.
Qed.

(** Source for [projection_norm_power_compact]: the integrand of
    Federer 2.7.16, p. 139, belongs to K(O*(n, m)). Supporting lemma. *)
Lemma projection_norm_power_compact xi (t : R) : simple xi -> 0 < t ->
  K (fun p => real_power (projection_norm xi p) t).
Proof.
by move=> hs ht; apply: projection_space_continuous_compact; exact: projection_norm_power_continuous.
Qed.

(** Source for [projection_frame_translate]: for orthonormal m-families
    e and e' of R^n there is g in O(n) with |(Lambda_m p)(e'_1 wedge ...
    wedge e'_m)| = |(Lambda_m A(g, p))(e_1 wedge ... wedge e_m)| for every
    p in O*(n, m), where A(g, p) = p o g^{-1}; supporting "the group O(n)
    acts transitively ... and the invariance of theta*_{n,m} implies the
    integrals corresponding to xi and (Lambda_m g) xi are equal", Federer
    2.7.16, p. 139. Supporting lemma, for frames. *)
Lemma projection_frame_translate (e e' : 'I_m -> R_n R n) :
  orthonormal_family (@euclidean_inner_product R n) e ->
  orthonormal_family (@euclidean_inner_product R n) e' ->
  exists g, forall p, projection_norm (e_lambda e' (ord_tuple m)) p =
    projection_norm (e_lambda e (ord_tuple m)) (A g p).
Proof.
move=> he he'.
have [f [hf hfe]] := orthonormal_frame_map_exists hBn he.
have [f' [hf' hfe']] := orthonormal_frame_map_exists hBn he'.
have [g0 [hg0 hgf]] := orthogonal_injection_transitive hBm hBn hbm hbn hf hf'.
pose G := orthogonal_element_of hBn hbn hg0.
exists (invS G)=> p; rewrite !projection_norm_e_lambda.
congr (exterior_norm _ _ (e_lambda _ _)); apply: funext=> i.
rewrite orthogonal_projection_actionE (group_invK hOG) orthogonal_element_ofE.
by rewrite -hfe hgf hfe'.
Qed.

(** Source for [normalised_invariant_measure_integral]: a normalised
    invariant measure phi over O*(n, m), such as theta*_{n,m} of Federer
    2.7.16, p. 139, represents a nonzero monotone invariant integral nu
    on K(O*(n, m)) with nu(1) = 1 (2.7.1, p. 122; 2.5.3, p. 94).
    Supporting lemma. *)
Lemma normalised_invariant_measure_integral (phi : set OP -> \bar R) :
  is_normalised_invariant_measure A phi ->
  exists nu : (OP -> R) -> R,
    [/\ is_nonzero_monotone_invariant_integral A nu, is_real_integral_functional phi K nu,
      is_measure phi & nu (fun _ => 1) = 1].
Proof.
move=> [[nu [hM hC hm hrep _]] h1].
have hone := compact_space_constant_one R projection_space_compact.
have hnu1 : nu (fun _ => 1) = 1.
  by move: h1; rewrite (compact_representing_measure_total projection_space_compact hm hrep); case.
exists nu; split=> //; split=> //.
- by split=> //; exact: monotone_daniell_is_daniell.
- by exists (fun _ => 1)=> //; rewrite hnu1; exact/eqP/oner_neq0.
Qed.

(** Source for [projection_constant_integral_value]: for a normalised
    invariant measure phi over O*(n, m) with integral nu, an orthonormal
    m-family e_0 of R^n and t > 0, the number c = nu(p |-> |(Lambda_m p)
    (e_0)|^t) is positive and nu(p |-> |(Lambda_m p) xi|^t) = |xi|^t c
    for every simple xi; this is "In fact the integral is positively
    homogeneous of degree t with respect to xi, the group O(n) acts
    transitively ...", Federer 2.7.16, p. 139. Supporting theorem; the
    proof is supplied (see the header). *)
Theorem projection_constant_integral_value (nu : (OP -> R) -> R) (t : R)
    (e0 : 'I_m -> R_n R n) :
  is_nonzero_monotone_invariant_integral A nu -> 0 < t ->
  orthonormal_family (@euclidean_inner_product R n) e0 ->
  0 < nu (fun p => real_power (projection_norm (e_lambda e0 (ord_tuple m)) p) t) /\
  forall xi, simple xi ->
    nu (fun p => real_power (projection_norm xi p) t) =
      real_power (exterior_norm h2 hBn xi) t *
        nu (fun p => real_power (projection_norm (e_lambda e0 (ord_tuple m)) p) t).
Proof.
move=> hnu ht he0.
have hM := nonzero_invariant_integral_monotone hnu.
have hlaw := covariant_integral_law (nonzero_invariant_integral_invariant hnu).
pose F (xi : exterior_power (R_n R n) m) p := real_power (projection_norm xi p) t.
have hK xi : simple xi -> K (F xi) := fun hs => projection_norm_power_compact hs ht.
have hframe (e : 'I_m -> R_n R n) : orthonormal_family (@euclidean_inner_product R n) e ->
    nu (F (e_lambda e (ord_tuple m))) = nu (F (e_lambda e0 (ord_tuple m))).
  move=> he; have [g hg] := projection_frame_translate he0 he.
  have -> : F (e_lambda e (ord_tuple m)) = F (e_lambda e0 (ord_tuple m)) \o A g.
    by apply: funext=> p; rewrite /F /= hg.
  by rewrite (hlaw _ g (hK _ (product_simple _))) mul1r.
split.
- have hx0 : e_lambda e0 (ord_tuple m) != 0.
    by rewrite -(exterior_norm_eq0 h2 hBn) (orthonormal_product_unit_norm h2 hBn he0) oner_eq0.
  have [f [p [hf [hadj hp]]]] := simple_projection_norm_attained h2 hBn hx0 (product_simple _).
  have hpp : is_orthogonal_projection (@euclidean_inner_product R n) (@euclidean_inner_product R m) p.
    by exists f.
  pose p0 : OP := orthogonal_projection_of hBm hBn hbn hpp.
  apply: (nonzero_invariant_integral_positive hOG (orthogonal_projections_homogeneous hBm hbm hS) hnu
    (hK _ (product_simple _))).
  + move=> q; exact: real_power_nonnegative.
  + exists p0; rewrite /F.
    have -> : projection_norm (e_lambda e0 (ord_tuple m)) p0 = 1.
      rewrite /projection_norm -(orthonormal_product_unit_norm h2 hBn he0) -hp.
      congr (exterior_norm _ _ _); apply: exterior_power_map_ext=> v.
      by rewrite hom_as_linearE; exact: hom_of_linearE.
    by rewrite real_power_one_base; exact/eqP/oner_neq0.
move=> xi hs.
have [->|hx] := eqVneq xi 0.
  have -> : (fun p => real_power (projection_norm 0 p) t) = (fun _ => 0).
    by apply: funext=> p; rewrite projection_norm_zero real_power_zero_base ?gt_eqF.
  rewrite exterior_norm_zero real_power_zero_base ?gt_eqF // mul0r.
  exact: (monotone_daniell_integral_zero hM (@compactly_supported_zero_function R OP)).
have [e [c [he [hc hxe]]]] := simple_orthonormal_factor h2 hBn hx hs.
have hxn : exterior_norm h2 hBn xi = `|c|.
  by rewrite hxe exterior_norm_scale (orthonormal_product_unit_norm h2 hBn he) mulr1.
have -> : (fun p => real_power (projection_norm xi p) t) =
    (fun p => real_power `|c| t * F (e_lambda e (ord_tuple m)) p).
  apply: funext=> p; rewrite /F hxe projection_norm_scale real_power_product //.
  exact: projection_norm_nonnegative.
rewrite (monotone_daniell_integral_scale hM (real_power_nonnegative _ _) (hK _ (product_simple _))).
by rewrite hframe // hxn.
Qed.

End ProjectionNorm.

Section ProjectionConstant.
Variable R : realType.
Hypothesis h2 : (1 + 1 : R) != 0.
Local Notation hBn n := (@euclidean_inner_productP R n).
Local Notation hbn n := (@coordinate_basisP R n).

(** Source for [is_projection_constant]: "there exists a positive
    number beta_t(n, m) such that (int |(Lambda_m p) xi|^t dtheta*_{n,m}
    p)^{1/t} = beta_t(n, m) . |xi| for every simple m-vector xi of R^n",
    Federer 2.7.16, p. 139. Definition by this property: beta > 0 and the
    displayed equation holds for every normalised invariant measure over
    O*(n, m) (the measure theta*_{n,m}, for any restricted group structure
    of O(n)) and every simple xi. *)
Definition is_projection_constant (t : R) (n m : nat) (beta : R) : Prop :=
  0 < beta /\
  forall mulS invS eS
    (hS : is_subgroup_restriction (linear_group_mul (hBn n) (hbn n)) (linear_group_inv (hBn n) (hbn n))
      (linear_group_unit (hBn n) (hbn n)) (euclidean_orthogonal_group R n) mulS invS eS)
    (phi : set (set_type (euclidean_orthogonal_projections R n m)) -> \bar R),
    is_normalised_invariant_measure (orthogonal_projection_action (hBn m) (hBn n) (hbn n) hS) phi ->
    forall xi : exterior_power (R_n R n) m, simple xi ->
      exists2 a, is_measure_integral phi
          (real_total_integrand (fun p => real_power (projection_norm h2 xi p) t)) a &
        extended_positive_power a t^-1 = (beta * exterior_norm h2 (hBn n) xi)%:E.

(** Source for [orthogonal_projection_action_independent]: the action
    A(g, p) = p o g^{-1} of O(n) on O*(n, m), Federer 2.7.16, p. 139,
    does not depend on the restricted group structure of O(n): g^{-1} is
    the inverse of g in Hom(R^n, R^n) for both. Supporting lemma. *)
Lemma orthogonal_projection_action_independent n m mulS invS eS mulS' invS' eS'
    (hS : is_subgroup_restriction (linear_group_mul (hBn n) (hbn n)) (linear_group_inv (hBn n) (hbn n))
      (linear_group_unit (hBn n) (hbn n)) (euclidean_orthogonal_group R n) mulS invS eS)
    (hS' : is_subgroup_restriction (linear_group_mul (hBn n) (hbn n)) (linear_group_inv (hBn n) (hbn n))
      (linear_group_unit (hBn n) (hbn n)) (euclidean_orthogonal_group R n) mulS' invS' eS') :
  orthogonal_projection_action (hBn m) (hBn n) (hbn n) hS =
    orthogonal_projection_action (hBn m) (hBn n) (hbn n) hS'.
Proof.
apply: funext=> g; apply: funext=> p; apply: orthogonal_projection_ext=> v.
rewrite !orthogonal_projection_actionE; congr (orthogonal_projection_map p _).
have [c1 _] := orthogonal_element_inv hS g.
have [_ c2] := orthogonal_element_inv hS' g.
by rewrite -{1}(c2 v) c1.
Qed.

(** Source for [projection_constant_exists]: "Whenever n >= m are
    positive integers and 1 <= t < oo, there exists a positive number
    beta_t(n, m) such that ...", Federer 2.7.16, p. 139. Direct
    formalisation, for m <= n and every t > 0; the proof is supplied (see
    the header). *)
Theorem projection_constant_exists (t : R) (n m : nat) :
  (m <= n)%N -> 0 < t -> exists beta, is_projection_constant t n m beta.
Proof.
move=> hmn ht.
have [mulS0 [invS0 [eS0 hS0]]] := orthogonal_group_restriction_exists (hBn n) (hbn n).
have [phi0 [hphi0 hphi0u _]] := euclidean_theta_star_nm_exists_unique hS0 hmn.
have [nu0 [hnu0 hrep0 hm0 _]] := normalised_invariant_measure_integral hphi0.
pose e0 (i : 'I_m) : R_n R n := @coordinate_basis R n (widen_ord hmn i).
have hw i j : (widen_ord hmn i == widen_ord hmn j) = (i == j).
  by apply/eqP/eqP=> [h|->] //; apply: val_inj; exact: (congr1 val h).
have he0 : orthonormal_family (@euclidean_inner_product R n) e0.
  move=> i j; rewrite /e0 euclidean_inner_basis /coordinate_basis ffunE.
  by rewrite hw eq_sym.
pose c := nu0 (fun p => real_power (projection_norm h2 (e_lambda e0 (ord_tuple m)) p) t).
have [hc hval] := projection_constant_integral_value h2 hnu0 ht he0.
exists (real_power c t^-1); split; first by apply: real_power_strictly_positive.
move=> mulS invS eS hS phi hphi xi hs.
have he : orthogonal_projection_action (hBn m) (hBn n) (hbn n) hS =
    orthogonal_projection_action (hBn m) (hBn n) (hbn n) hS0.
  exact: orthogonal_projection_action_independent.
have hphi' : is_normalised_invariant_measure (orthogonal_projection_action (hBn m) (hBn n) (hbn n) hS0) phi.
  by rewrite -he.
have -> : phi = phi0 := hphi0u phi hphi'.
exists (nu0 (fun p => real_power (projection_norm h2 xi p) t))%:E.
  exact: hrep0 (projection_norm_power_compact h2 hS0 hs ht).
rewrite hval //= real_power_product ?real_power_nonnegative ?ltW //.
rewrite real_power_root_cancel ?exterior_norm_nonnegative // mulrC.
by rewrite /c.
Qed.

(** Source for [projection_constant_integral]: the t-th power form
    int |(Lambda_m p) xi|^t dtheta*_{n,m} p = beta_t(n, m)^t |xi|^t of
    the equation of Federer 2.7.16, p. 139, used in the proof of the
    second display. Supporting lemma. *)
Lemma projection_constant_integral (t : R) n m beta mulS invS eS
    (hS : is_subgroup_restriction (linear_group_mul (hBn n) (hbn n)) (linear_group_inv (hBn n) (hbn n))
      (linear_group_unit (hBn n) (hbn n)) (euclidean_orthogonal_group R n) mulS invS eS)
    (phi : set (set_type (euclidean_orthogonal_projections R n m)) -> \bar R)
    (xi : exterior_power (R_n R n) m) :
  is_projection_constant t n m beta -> 0 < t ->
  is_normalised_invariant_measure (orthogonal_projection_action (hBn m) (hBn n) (hbn n) hS) phi ->
  simple xi ->
  is_measure_integral phi (real_total_integrand (fun p => real_power (projection_norm h2 xi p) t))
    (real_power beta t * real_power (exterior_norm h2 (hBn n) xi) t)%:E.
Proof.
move=> [hb hbeta] ht hphi hs.
have [nu [hnu hrep hm _]] := normalised_invariant_measure_integral hphi.
have hK := projection_norm_power_compact h2 hS hs ht.
have [a ha hroot] := hbeta _ _ _ hS phi hphi xi hs.
have hi := hrep _ hK.
rewrite -(measure_integral_unique hi ha) /= in hroot.
case: hroot=> hroot.
have hnn : 0 <= nu (fun p => real_power (projection_norm h2 xi p) t).
  rewrite -(monotone_daniell_integral_zero (nonzero_invariant_integral_monotone hnu) hK).
  apply: (monotone_daniell_integral_monotone (nonzero_invariant_integral_monotone hnu)
    (@compactly_supported_zero_function R _) hK)=> p; exact: real_power_nonnegative.
have -> : real_power beta t * real_power (exterior_norm h2 (hBn n) xi) t =
    nu (fun p => real_power (projection_norm h2 xi p) t).
  rewrite -(real_power_product t (ltW hb) (exterior_norm_nonnegative h2 (hBn n) xi)) -hroot.
  rewrite (real_power_positive_iterate hnn (_ : 0 < t^-1) ht) ?invr_gt0 //.
  by rewrite mulVf ?gt_eqF // real_power_one_exponent.
exact: hi.
Qed.

(** Source for [projection_constant_unique]: "a positive number
    beta_t(n, m) such that ...", Federer 2.7.16, p. 139: the number is
    determined by the displayed equation, for m <= n and t > 0.
    Supporting theorem. *)
Theorem projection_constant_unique (t : R) n m beta1 beta2 :
  (m <= n)%N -> 0 < t ->
  is_projection_constant t n m beta1 -> is_projection_constant t n m beta2 -> beta1 = beta2.
Proof.
move=> hmn ht h1 h2'.
have [mulS0 [invS0 [eS0 hS0]]] := orthogonal_group_restriction_exists (hBn n) (hbn n).
have [phi0 [hphi0 _ _]] := euclidean_theta_star_nm_exists_unique hS0 hmn.
pose e0 (i : 'I_m) : R_n R n := @coordinate_basis R n (widen_ord hmn i).
have hw i j : (widen_ord hmn i == widen_ord hmn j) = (i == j).
  by apply/eqP/eqP=> [h|->] //; apply: val_inj; exact: (congr1 val h).
have he0 : orthonormal_family (@euclidean_inner_product R n) e0.
  move=> i j; rewrite /e0 euclidean_inner_basis /coordinate_basis ffunE.
  by rewrite hw eq_sym.
have hx1 := orthonormal_product_unit_norm h2 (hBn n) he0.
have i1 := projection_constant_integral h1 ht hphi0 (product_simple e0).
have i2 := projection_constant_integral h2' ht hphi0 (product_simple e0).
have := measure_integral_unique i1 i2; rewrite hx1 real_power_one_base !mulr1 => -[] he.
apply: (real_power_injective _ _ ht he); [exact: ltW h1.1|exact: ltW h2'.1].
Qed.

End ProjectionConstant.
