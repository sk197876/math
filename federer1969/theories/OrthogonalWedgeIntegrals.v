(** Federer (1969), 2.7.16, printed p. 139, example (6): "If xi in Lambda_m
    R^n, eta in Lambda_k R^n, m + k <= n and xi, eta are simple, then
    int_{O(n)} |<xi, Lambda_m g> wedge eta|^t dtheta_n g = beta_t(n, m)^t
    beta_t(n - k, m)^{-t} |xi|^t |eta|^t. ... Using Fubini's theorem and the
    fact that r o q in O*(n, m) for each r in O*(n - k, m), we infer
    beta_t(n - k, m)^t int |<xi, Lambda_m g> wedge eta|^t dtheta_n g = int
    int |<xi, Lambda_m(r o q o g)>|^t dtheta_n g dtheta*_{n-k,m} r = int
    beta_t(n, m)^t dtheta*_{n-k,m} r = beta_t(n, m)^t. As a corollary we
    obtain the equation beta_t(n, m)/ beta_t(n - k, m) = beta_t(n,
    k)/beta_t(n - m, k), because O(n) is unimodular and |<xi, Lambda_m g>
    wedge eta| = |xi wedge <eta, Lambda_k g^{-1}>| for g in O(n)." Here <xi,
    Lambda_m g> = (Lambda_m g) xi, theta_n is a normalised Haar measure of
    O(n) and beta_t is given by is_projection_constant
    (OrthogonalProjectionConstants.v). The proof follows Federer. The
    reduction to |eta| = 1 uses the homogeneity of the integrand; q is
    chosen by WedgeKernelProjection.v. All integrands are continuous on the
    compact spaces O(n) and O(n) x O*(n - k, m), hence members of K (2.5.13,
    p. 106), and their integrals are values of the Haar integral lambda of
    theta_n and of the invariant integral nu' of theta*_{n-k,m}. Fubini's
    theorem is applied to these Daniell integrals on K(O(n) x O*(n - k, m))
    (2.6.4 and 2.6.6, pp. 119-120; compact_daniell_iterations_commute). The
    inner integral over O(n) is computed from theta*_{n,m} = (A^p)_#
    theta_n, p = r o q, with A(g, p) = p o g^{-1} (2.7.16, p. 139), and from
    the unimodularity of the compact group O(n) (2.7.12, p. 129), which
    gives lambda(u o g^{-1}) = lambda(u) by 2.7.8(3), p. 126. The local
    erratum has no entry for p. 139. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  topology constructive_ereal.
From mathcomp Require Import ring.
From Federer Require Import TensorUP InnerProductUP InnerNorm InnerMetric LinearBasis Hom HomInner
  OrthogonalMaps OrthonormalFamilies AdjointUP Adjoint GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates CoordinateProjection IsotropyGroupTopology TopologicalGroupUP TopologicalGroupLaws
  TopologicalProductMaps HomogeneousSpaceUP HomogeneousSpaceLaws RealMetricBackground
  CompactSupportFunctionUP CompactSupportFunctionLattice FunctionLatticeUP DaniellIntegralUP
  MonotoneDaniellIntegralUP MonotoneDaniellIntegralLaws DaniellIntegralNegation DaniellSpacePushforward
  DaniellSpaceCompactSpace DaniellSpaceCompactness CompactDaniellIterationCommutation
  CovariantIntegralUP HaarIntegralUP
  ModularFunctionUP ModularFunction UnimodularGroupUP UnimodularGroups RealIntegralFunctionalUP
  SummableRealFunctionUP MeasureUP MeasurePushforward MeasureIntegralUP MeasureIntegralUniqueness
  RealPower RealPowerDivision RealPowerContinuity HomSpaceTopology LinearGroupTopology LinearGroupSealed
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure CompactGroupHaarNormalisation
  CompactGroupHomogeneousMeasures OrthogonalInjectionSpaces EuclideanOrthogonalInvariantMeasures
  SubtypeCompactHausdorff ExteriorGrading ExteriorMaps ExteriorMapScaling FiniteExteriorPowers
  ExteriorHomogeneousProducts InnerExterior ExteriorNorm ExteriorNormNaturality ExteriorProjectionNorm
  AssociatedSubspace SimpleElementary SimpleOrthonormalFactor Bilinear ExteriorMapNormContinuity
  WedgeKernelProjection
  OrthogonalProjectionConstants.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CompactInversion.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hGc : is_locally_compact_hausdorff_group mul inv e.
Hypothesis hc : compact [set: G].

(** Source for [compact_haar_integral_inversion]: "because O(n) is
    unimodular", Federer 2.7.16, p. 139: for a left Haar integral lambda
    of a compact group, lambda(u o inv) = lambda(u) whenever u in K(G),
    by 2.7.8(3), p. 126, since Delta_G = 1 (2.7.12, p. 129). Supporting
    lemma. *)
Lemma compact_haar_integral_inversion (lambda : (G -> R) -> R) (u : G -> R) :
  is_left_haar_integral mul lambda -> compactly_supported_continuous_functions u ->
  lambda (u \o inv) = lambda u.
Proof.
move=> hl hu.
have [D hD] := modular_function_exists R hGc.
have hD1 := (unimodular_iff_modular_unit hGc hD).1 (compact_group_unimodular hGc hc).
have := modular_function_left_inversion hD hl hu.
have -> : (fun x => u (inv x) * D (inv x)) = u \o inv.
  by apply: funext=> x; rewrite hD1 mulr1.
by [].
Qed.

End CompactInversion.

(** Source for [orthogonal_projection_compose]: "the fact that r o q in
    O*(n, m) for each r in O*(n - k, m)", Federer 2.7.16, p. 139: the
    composite of two orthogonal projections is an orthogonal projection,
    the adjoint of the composite of the orthogonal injections (1.7.4,
    p. 30). Supporting lemma. *)
Lemma orthogonal_projection_compose (R : realFieldType) (V U W : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R) (D : W -> W -> R)
    (q : {linear V -> U}) (r : {linear U -> W}) :
  is_orthogonal_projection B C q -> is_orthogonal_projection C D r ->
  is_orthogonal_projection B D (linear_comp r q).
Proof.
move=> [h [hh hq]] [h' [hh' hr]].
exists (linear_comp h h'); split.
  by move=> x y; rewrite /linear_comp /= hh hh'.
by move=> x y; rewrite /linear_comp /= hr hq.
Qed.

Section WedgeIntegrals.
Variable R : realType.
Hypothesis h2 : (1 + 1 : R) != 0.
Local Notation CE j := (@euclidean_inner_product R j).
Local Notation hBn j := (@euclidean_inner_productP R j).
Local Notation hbn j := (@coordinate_basisP R j).
Local Notation HOM a b := (inner_metric_space (hom_inner_productP (hBn a) (hBn b) (hbn a))).
Variable n : nat.
Local Notation O := (euclidean_orthogonal_group R n).
Local Notation om := (@orthogonal_element_map R (R_n R n) _ (hBn n) n _ (hbn n)).
Variables (mulS : O -> O -> O) (invS : O -> O) (eS : O).
Hypothesis hS : is_subgroup_restriction (linear_group_mul (hBn n) (hbn n))
  (linear_group_inv (hBn n) (hbn n)) (linear_group_unit (hBn n) (hbn n)) O mulS invS eS.
Local Notation KO := (@compactly_supported_continuous_functions R O).

(** Source for [hOlch]: O(n) is a compact Hausdorff group, Federer
    2.7.16, p. 139, used in this section. *)
Let hOlch : is_locally_compact_hausdorff_group mulS invS eS := orthogonal_group_lch hS.
(** Source for [hOc]: O(n) is compact, Federer 2.7.16, p. 139, used in
    this section. *)
Let hOc : compact [set: O] := @orthogonal_group_compact_space R (R_n R n) _ (hBn n) n _ (hbn n).
(** Source for [hOG]: the group laws of O(n), used in this section. *)
Let hOG : is_group_laws mulS invS eS := topological_group_laws (lch_group_topological hOlch).

(** Source for [orthogonal_group_continuous_compact]: every continuous
    real function on O(n) belongs to K(O(n)), Federer 2.5.13, p. 106,
    since O(n) is compact (2.7.16, p. 139). Supporting lemma. *)
Lemma orthogonal_group_continuous_compact (u : O -> R) :
  continuous (u : O -> real_line_metric R) -> KO u.
Proof.
move=> hu; split=> //.
apply: (real_function_compact_support_in_closed_set hOc closedT).
by move=> x hx; exfalso; exact: hx.
Qed.

(** Source for [orthogonal_composite_norm_power_compact]: for a fixed
    linear map Q of R^n into R^j, a simple m-vector xi and t > 0, the
    function g |-> |(Lambda_m(Q o g)) xi|^t belongs to K(O(n)),
    supporting the integrals of Federer 2.7.16, p. 139. Supporting
    lemma. *)
Lemma orthogonal_composite_norm_power_compact j m (Q : {linear R_n R n -> R_n R j})
    (xi : exterior_power (R_n R n) m) (t : R) :
  simple xi -> 0 < t ->
  KO (fun g => real_power (exterior_norm h2 (hBn j)
    (exterior_power_map (hom_as_linear (hom_comp (hom_of_linear Q) (om g))) m xi)) t).
Proof.
move=> hs ht; apply: orthogonal_group_continuous_compact.
have hc : continuous (fun g : O => (hom_comp (hom_of_linear Q) (om g) : HOM n j)).
  move=> g.
  have hp : continuous (fun g : O => ((hom_of_linear Q : HOM n j), (om g : HOM n n))).
    exact: (@topological_pair_continuous O (HOM n j) (HOM n n) (fun _ => hom_of_linear Q)
      (fun g => om g) (@cst_continuous O (HOM n j) (hom_of_linear Q))
      (@orthogonal_element_continuous R (R_n R n) _ (hBn n) n _ (hbn n))).
  exact: (continuous_comp (hp g) (@hom_composition_continuous_general R (R_n R n) (R_n R n) (R_n R j)
    _ _ _ (hBn n) (hBn n) (hBn j) n _ n _ (hbn n) (hbn n) _)).
move=> g; exact: (continuous_comp (hc g)
  (@exterior_map_norm_power_continuous R h2 (R_n R n) (R_n R j) _ _ (hBn n) (hBn j) n _ (hbn n)
  m xi t hs ht _)).
Qed.

(** Source for [orthogonal_wedge_integrand_compact]: for simple xi in
    Lambda_m R^n, eta in Lambda_k R^n and t > 0, the function
    g |-> |<xi, Lambda_m g> wedge eta|^t belongs to K(O(n)); the
    integrand of Federer 2.7.16, p. 139. Supporting lemma: for eta != 0,
    |<xi, Lambda_m g> wedge eta| = |eta| |(Lambda_m(q o g)) xi| with q
    from wedge_kernel_projection_exists. *)
Lemma orthogonal_wedge_integrand_compact m k (xi : exterior_power (R_n R n) m)
    (eta : exterior_power (R_n R n) k) (t : R) :
  simple xi -> simple eta -> 0 < t ->
  KO (fun g => real_power (exterior_norm h2 (hBn n)
    (exterior_product (exterior_power_map (hom_as_linear (om g)) m xi) eta)) t).
Proof.
move=> hsx hse ht.
have [->|he0] := eqVneq eta 0.
  have -> : (fun g : O => real_power (exterior_norm h2 (hBn n)
      (exterior_product (exterior_power_map (hom_as_linear (om g)) m xi) (0 : exterior_power _ k))) t) =
      (fun _ => 0).
    apply: funext=> g; rewrite (bil0r (@exterior_product_bilinear R (R_n R n) m k)).
    by rewrite exterior_norm_zero real_power_zero_base ?gt_eqF.
  exact: compactly_supported_zero_function.
have [f [c [hf [hc heta]]]] := simple_orthonormal_factor h2 (hBn n) he0 hse.
pose eta1 := e_lambda f (ord_tuple k).
have hs1 : simple eta1 := product_simple f.
have hn1 : exterior_norm h2 (hBn n) eta1 = 1 := orthonormal_product_unit_norm h2 (hBn n) hf.
have hce : exterior_norm h2 (hBn n) eta = `|c| by rewrite heta exterior_norm_scale (orthonormal_product_unit_norm h2 (hBn n) hf) mulr1.
have [q [h [hho hadj _ _ hnorm]]] := wedge_kernel_projection_exists (hbn n) hs1 hn1.
have -> : (fun g : O => real_power (exterior_norm h2 (hBn n)
      (exterior_product (exterior_power_map (hom_as_linear (om g)) m xi) eta)) t) =
    (fun g => real_power (exterior_norm h2 (hBn n) eta) t *
      real_power (exterior_norm h2 (hBn (n - k))
        (exterior_power_map (hom_as_linear (hom_comp (hom_of_linear q) (om g))) m xi)) t).
  apply: funext=> g.
  rewrite {1}heta (bilZr (@exterior_product_bilinear R (R_n R n) m k)) exterior_norm_scale.
  rewrite hce real_power_product ?exterior_norm_nonnegative //.
  rewrite (hnorm _ _ (exterior_power_map_simple _ hsx)) exterior_power_map_composition.
  congr (_ * real_power (exterior_norm _ _ _) _); apply: exterior_power_map_ext=> v.
  by rewrite /linear_comp /= ?hom_as_linearE ?hom_compE ?hom_of_linearE.
apply: compactly_supported_scale.
exact: orthogonal_composite_norm_power_compact.
Qed.

(** Source for [orthogonal_wedge_integral]: "If xi in Lambda_m R^n,
    eta in Lambda_k R^n, m + k <= n and xi, eta are simple, then
    int_{O(n)} |<xi, Lambda_m g> wedge eta|^t dtheta_n g = beta_t(n, m)^t
    beta_t(n - k, m)^{-t} |xi|^t |eta|^t", Federer 2.7.16, p. 139.
    Direct formalisation for t > 0, with beta_t(n, m) and beta_t(n - k, m)
    given by is_projection_constant and theta_n any normalised Haar
    measure of O(n). The proof follows Federer (see the header). *)
Theorem orthogonal_wedge_integral m k (t beta1 beta2 : R) (theta : set O -> \bar R)
    (xi : exterior_power (R_n R n) m) (eta : exterior_power (R_n R n) k) :
  0 < t -> (m + k <= n)%N ->
  is_projection_constant h2 t n m beta1 -> is_projection_constant h2 t (n - k) m beta2 ->
  is_normalised_haar_measure mulS theta -> simple xi -> simple eta ->
  is_measure_integral theta (real_total_integrand (fun g => real_power (exterior_norm h2 (hBn n)
      (exterior_product (exterior_power_map (hom_as_linear (om g)) m xi) eta)) t))
    (real_power beta1 t * real_power beta2 (- t) * real_power (exterior_norm h2 (hBn n) xi) t *
      real_power (exterior_norm h2 (hBn n) eta) t)%:E.
Proof.
move=> ht hmkn hb1 hb2 htheta hsx hse.
have [[lam [hl hmt hrep _]] _] := htheta.
have hlM := nonzero_invariant_integral_monotone hl.
have hKG := orthogonal_wedge_integrand_compact hsx hse ht.
apply: (eq_ind _ (fun a => is_measure_integral theta _ a%:E) (hrep _ hKG)).
pose X := exterior_norm h2 (hBn n) xi.
have hX : 0 <= X := exterior_norm_nonnegative _ _ _.
have hb1p := hb1.1; have hb2p := hb2.1.
have hb2t : 0 < real_power beta2 t := real_power_strictly_positive t hb2p.
(* the case eta = 0 *)
have [he0|he0] := eqVneq eta 0.
  have -> : (fun g : O => real_power (exterior_norm h2 (hBn n)
      (exterior_product (exterior_power_map (hom_as_linear (om g)) m xi) eta)) t) = (fun _ => 0).
    apply: funext=> g; rewrite he0 (bil0r (@exterior_product_bilinear R (R_n R n) m k)).
    by rewrite exterior_norm_zero real_power_zero_base ?gt_eqF.
  rewrite he0 exterior_norm_zero real_power_zero_base ?gt_eqF // mulr0.
  exact: (monotone_daniell_integral_zero hlM (@compactly_supported_zero_function R O)).
(* reduction to |eta| = 1 and the choice of q *)
have [f [c0 [hf [hc0 heta]]]] := simple_orthonormal_factor h2 (hBn n) he0 hse.
pose eta1 := e_lambda f (ord_tuple k).
have hs1 : simple eta1 := product_simple f.
have hn1 : exterior_norm h2 (hBn n) eta1 = 1 := orthonormal_product_unit_norm h2 (hBn n) hf.
pose c := exterior_norm h2 (hBn n) eta.
have hce : c = `|c0| by rewrite /c heta exterior_norm_scale (orthonormal_product_unit_norm h2 (hBn n) hf) mulr1.
have [q [h [hho hadj _ _ hnorm]]] := wedge_kernel_projection_exists (hbn n) hs1 hn1.
have hqp : is_orthogonal_projection (CE n) (CE (n - k)) q := wedge_kernel_projection_star hho hadj.
pose G1 (g : O) := real_power (exterior_norm h2 (hBn (n - k))
  (exterior_power_map (hom_as_linear (hom_comp (hom_of_linear q) (om g))) m xi)) t.
have hG1 : KO G1 := orthogonal_composite_norm_power_compact q hsx ht.
have hqg (g : O) v : hom_as_linear (hom_comp (hom_of_linear q) (om g)) v = q (om g v).
  by rewrite hom_as_linearE hom_compE hom_of_linearE.
have hGG1 : (fun g : O => real_power (exterior_norm h2 (hBn n)
      (exterior_product (exterior_power_map (hom_as_linear (om g)) m xi) eta)) t) =
    (fun g => real_power c t * G1 g).
  apply: funext=> g.
  rewrite {1}heta (bilZr (@exterior_product_bilinear R (R_n R n) m k)) exterior_norm_scale.
  rewrite -hce real_power_product ?exterior_norm_nonnegative //.
  rewrite (hnorm _ _ (exterior_power_map_simple _ hsx)) exterior_power_map_composition /G1.
  congr (_ * real_power (exterior_norm _ _ _) _); apply: exterior_power_map_ext=> v.
  by rewrite /linear_comp /= ?hqg ?hom_as_linearE.
(* the measure theta*_{n-k,m} *)
have hmnk : (m <= n - k)%N.
  by rewrite -(leq_add2r k) subnK // (leq_trans (leq_addl m k) hmkn).
have [mulS' [invS' [eS' hS']]] := orthogonal_group_restriction_exists (hBn (n - k)) (hbn (n - k)).
have [phi' [hphi' _ _]] := euclidean_theta_star_nm_exists_unique hS' hmnk.
have [nu' [hnu' hrep' hm' hnu'1]] := normalised_invariant_measure_integral hphi'.
have hnuM := nonzero_invariant_integral_monotone hnu'.
pose OP' := set_type (euclidean_orthogonal_projections R (n - k) m).
pose OP := set_type (euclidean_orthogonal_projections R n m).
(* r o q as a point of O*(n, m) *)
have hrq (r : OP') : is_orthogonal_projection (CE n) (CE m)
    (linear_comp (hom_as_linear (orthogonal_projection_map r)) q).
  exact: orthogonal_projection_compose hqp (orthogonal_projection_map_projection r).
pose rq (r : OP') : OP := orthogonal_projection_of (hBn m) (hBn n) (hbn n) (hrq r).
pose H (z : O * OP') := real_power (exterior_norm h2 (hBn m) (exterior_power_map
  (hom_as_linear (hom_comp (hom_comp (orthogonal_projection_map z.2) (hom_of_linear q)) (om z.1)))
  m xi)) t.
(* the inner integral over O*(n - k, m) *)
have hinner1 (g : O) : nu' (fun r => H (g, r)) = real_power beta2 t * G1 g.
  pose xi' := exterior_power_map (hom_as_linear (hom_comp (hom_of_linear q) (om g))) m xi.
  have hs' : simple xi' := exterior_power_map_simple _ hsx.
  have hK' := projection_norm_power_compact h2 hS' hs' ht.
  have i1 := projection_constant_integral hb2 ht hphi' hs'.
  have := measure_integral_unique (hrep' _ hK') i1; case=> he.
  have -> : (fun r => H (g, r)) = (fun r => real_power (projection_norm h2 xi' r) t).
    apply: funext=> r; rewrite /H /projection_norm /xi' exterior_power_map_composition.
    congr (real_power (exterior_norm _ _ _) _); apply: exterior_power_map_ext=> v.
    by rewrite /linear_comp /= ?hom_as_linearE ?hom_compE ?hom_of_linearE.
  by rewrite he.
(* the inner integral over O(n) *)
have hA := orthogonal_projections_homogeneous (hBn m) (hbn m) hS.
have hXh : hausdorff_space OP :=
  @orthogonal_projections_hausdorff R (R_n R m) (R_n R n) _ _ (hBn m) (hBn n) n _ (hbn n).
have hinner2 (r : OP') : lam (fun g => H (g, r)) = real_power beta1 t * real_power X t.
  pose p := rq r.
  pose F (p' : OP) := real_power (projection_norm h2 xi p') t.
  have hKF : compactly_supported_continuous_functions F := projection_norm_power_compact h2 hS hsx ht.
  have hpush := compact_orbit_pushforward_invariant hOlch hOc hA hXh p htheta.
  have i1 := projection_constant_integral hb1 ht hpush hsx.
  have hrp := daniell_pushforward_integral (orbit_map_continuous hA p)
    (compact_homogeneous_orbit_proper hOc hA (x:=p) hXh) hmt hrep.
  have := measure_integral_unique (hrp _ hKF) i1; rewrite /daniell_pushforward; case=> he.
  have hFK := compactly_supported_compose (orbit_map_continuous hA p)
    (compact_homogeneous_orbit_proper hOc hA (x:=p) hXh) hKF.
  have -> : (fun g => H (g, r)) =
      (F \o orbit_map (orthogonal_projection_action (hBn m) (hBn n) (hbn n) hS) p) \o invS.
    apply: funext=> g; rewrite /H /F /= /orbit_map /projection_norm.
    congr (real_power (exterior_norm _ _ _) _); apply: exterior_power_map_ext=> v.
    rewrite !hom_as_linearE orthogonal_projection_actionE (group_invK hOG) !hom_compE.
    by rewrite /p /rq /orthogonal_projection_map /= ?hom_of_linearE /linear_comp /= ?hom_as_linearE.
  by rewrite (compact_haar_integral_inversion hOlch hOc hl hFK) he.
(* Fubini's theorem *)
have hHc : continuous (H : O * OP' -> real_line_metric R).
  have hc1 : continuous (fun z : O * OP' =>
      (hom_comp (orthogonal_projection_map z.2) (hom_of_linear q) : HOM n m)).
    move=> z.
    have hp : continuous (fun z : O * OP' =>
        ((orthogonal_projection_map z.2 : HOM (n - k) m), (hom_of_linear q : HOM n (n - k)))).
      apply: topological_pair_continuous; last exact: cst_continuous.
      move=> z'; exact: continuous_comp (@second_projection_continuous O OP' z')
        (@set_type_val_continuous _ (euclidean_orthogonal_projections R (n - k) m) z'.2).
    exact: (continuous_comp (hp z) (@hom_composition_continuous_general R (R_n R n) (R_n R (n - k))
      (R_n R m) _ _ _ (hBn n) (hBn (n - k)) (hBn m) n _ (n - k) _ (hbn n) (hbn (n - k)) _)).
  have hc2 : continuous (fun z : O * OP' =>
      (hom_comp (hom_comp (orthogonal_projection_map z.2) (hom_of_linear q)) (om z.1) : HOM n m)).
    move=> z.
    have hp : continuous (fun z : O * OP' =>
        ((hom_comp (orthogonal_projection_map z.2) (hom_of_linear q) : HOM n m), (om z.1 : HOM n n))).
      apply: topological_pair_continuous; first exact: hc1.
      move=> z'; exact: continuous_comp (@first_projection_continuous O OP' z')
        (@orthogonal_element_continuous R (R_n R n) _ (hBn n) n _ (hbn n) z'.1).
    exact: (continuous_comp (hp z) (@hom_composition_continuous_general R (R_n R n) (R_n R n)
      (R_n R m) _ _ _ (hBn n) (hBn n) (hBn m) n _ n _ (hbn n) (hbn n) _)).
  move=> z; exact: (continuous_comp (hc2 z)
    (@exterior_map_norm_power_continuous R h2 (R_n R n) (R_n R m) _ _ (hBn n) (hBn m) n _
    (hbn n) m xi t hsx ht _)).
have hOPc : compact [set: OP'] := projection_space_compact hS'.
have hHK : compactly_supported_continuous_functions H.
  split=> //; apply: (real_function_compact_support_in_closed_set _ closedT).
  - by rewrite -setXTT; exact: compact_setX.
  - by move=> x hx; exfalso; exact: hx.
have hfub := compact_daniell_iterations_commute (lch_group_hausdorff hOlch) (lch_group_locally_compact hOlch)
  (@orthogonal_projections_hausdorff R (R_n R m) (R_n R (n - k)) _ _ (hBn m) (hBn (n - k)) (n - k) _
    (hbn (n - k))) (compact_space_locally_compact hOPc)
  (monotone_daniell_is_daniell hlM) (monotone_daniell_is_daniell hnuM) hHK.
rewrite /= in hfub.
have hone' := compact_space_constant_one R hOPc.
have hL : nu' (fun r => lam (fun g => H (g, r))) = real_power beta1 t * real_power X t.
  have -> : (fun r => lam (fun g => H (g, r))) =
      (fun r => (real_power beta1 t * real_power X t) * (fun _ => 1) r).
    by apply: funext=> r; rewrite hinner2 mulr1.
  rewrite (monotone_daniell_integral_scale hnuM _ hone') ?hnu'1 ?mulr1 //.
  by rewrite mulr_ge0 ?real_power_nonnegative.
have hRr : lam (fun g => nu' (fun r => H (g, r))) = real_power beta2 t * lam G1.
  have -> : (fun g => nu' (fun r => H (g, r))) = (fun g => real_power beta2 t * G1 g).
    by apply: funext=> g; rewrite hinner1.
  by rewrite (monotone_daniell_integral_scale hlM (real_power_nonnegative _ _) hG1).
have hlG1 : lam G1 * real_power beta2 t = real_power beta1 t * real_power X t.
  by rewrite mulrC -hRr -hfub hL.
rewrite hGG1 (monotone_daniell_integral_scale hlM (real_power_nonnegative _ _) hG1).
rewrite real_power_negative_exponent // -/X -/c.
have hb2t0 : real_power beta2 t != 0 by rewrite gt_eqF.
have hlam : lam G1 = real_power beta1 t * real_power X t / real_power beta2 t.
  by rewrite -hlG1 mulfK.
rewrite hlam.
set A1 := real_power beta1 t; set A2 := real_power beta2 t; set A3 := real_power X t.
set A4 := real_power c t.
ring.
Qed.

(** Source for [orthogonal_wedge_inverse]: "|<xi, Lambda_m g> wedge
    eta| = |xi wedge <eta, Lambda_k g^{-1}>| for g in O(n)", Federer
    2.7.16, p. 139. Direct formalisation for all xi and eta: Lambda g^{-1}
    is an isometry (1.7.6, p. 33) and an algebra homomorphism (1.3.1,
    p. 14). *)
Lemma orthogonal_wedge_inverse m k (g : O) (xi : exterior_power (R_n R n) m)
    (eta : exterior_power (R_n R n) k) :
  exterior_norm h2 (hBn n) (exterior_product (exterior_power_map (hom_as_linear (om g)) m xi) eta) =
  exterior_norm h2 (hBn n) (exterior_product xi (exterior_power_map (hom_as_linear (om (invS g))) k eta)).
Proof.
have hoi : is_orthogonal_map (CE n) (CE n) (hom_as_linear (om (invS g))).
  move=> x y; rewrite !hom_as_linearE; exact: orthogonal_element_inner.
rewrite -(exterior_norm_orthogonal_natural h2 (hBn n) (hBn n) hoi) exterior_power_map_product.
rewrite exterior_power_map_composition; congr (exterior_norm _ _ (exterior_product _ _)).
have [hgi _] := orthogonal_element_inv hS g.
rewrite (@exterior_power_map_ext R _ _ _ (linear_id (R_n R n))) ?exterior_power_map_identity //.
Qed.

End WedgeIntegrals.

Section RatioCorollary.
Variable R : realType.
Hypothesis h2 : (1 + 1 : R) != 0.
Local Notation hBn j := (@euclidean_inner_productP R j).
Local Notation hbn j := (@coordinate_basisP R j).

(** Source for [standard_frame_product]: for m <= n, the first m
    standard basis vectors of R^n are orthonormal and their product is a
    simple m-vector of norm 1, supporting the corollary of Federer
    2.7.16, p. 139. Supporting lemma. *)
Lemma standard_frame_product n m (hmn : (m <= n)%N) :
  exists xi : exterior_power (R_n R n) m, simple xi /\ exterior_norm h2 (hBn n) xi = 1.
Proof.
pose e0 (i : 'I_m) : R_n R n := @coordinate_basis R n (widen_ord hmn i).
have hw i j : (widen_ord hmn i == widen_ord hmn j) = (i == j).
  by apply/eqP/eqP=> [h|->] //; apply: val_inj; exact: (congr1 val h).
have he0 : orthonormal_family (@euclidean_inner_product R n) e0.
  move=> i j; rewrite /e0 euclidean_inner_basis /coordinate_basis ffunE.
  by rewrite hw eq_sym.
exists (e_lambda e0 (ord_tuple m)); split; first exact: product_simple.
exact: orthonormal_product_unit_norm.
Qed.

(** Source for [projection_constant_ratio]: "As a corollary we obtain
    the equation beta_t(n, m)/beta_t(n - k, m) = beta_t(n, k)/beta_t(n -
    m, k), because O(n) is unimodular and |<xi, Lambda_m g> wedge eta| =
    |xi wedge <eta, Lambda_k g^{-1}>| for g in O(n)", Federer 2.7.16,
    p. 139. Direct formalisation for t > 0 and m + k <= n. Proof: apply
    orthogonal_wedge_integral to unit simple xi, eta and to eta, xi; the
    two integrands correspond under g |-> g^{-1} (orthogonal_wedge_inverse
    and the symmetry of |xi wedge eta|), and the Haar integral of O(n) is
    inversion invariant. *)
Theorem projection_constant_ratio (t : R) n m k beta1 beta2 beta3 beta4 :
  0 < t -> (m + k <= n)%N ->
  is_projection_constant h2 t n m beta1 -> is_projection_constant h2 t (n - k) m beta2 ->
  is_projection_constant h2 t n k beta3 -> is_projection_constant h2 t (n - m) k beta4 ->
  beta1 / beta2 = beta3 / beta4.
Proof.
move=> ht hmkn hb1 hb2 hb3 hb4.
have [mulS [invS [eS hS]]] := orthogonal_group_restriction_exists (hBn n) (hbn n).
have [theta htheta] := orthogonal_normalised_haar_measure_exists hS.
have [[lam [hl hmt hrep _]] _] := htheta.
have [xi [hsx hx1]] := standard_frame_product (leq_trans (leq_addr k m) hmkn).
have [eta [hse he1]] := standard_frame_product (leq_trans (leq_addl m k) hmkn).
have i1 := orthogonal_wedge_integral hS ht hmkn hb1 hb2 htheta hsx hse.
have hkmn : (k + m <= n)%N by rewrite addnC.
have i2 := orthogonal_wedge_integral hS ht hkmn hb3 hb4 htheta hse hsx.
rewrite hx1 he1 real_power_one_base !mulr1 in i1 i2.
have hK1 := orthogonal_wedge_integrand_compact h2 hsx hse ht.
have hK2 := orthogonal_wedge_integrand_compact h2 hse hsx ht.
have e1 := measure_integral_unique (hrep _ hK1) i1.
have e2 := measure_integral_unique (hrep _ hK2) i2.
have hinv := compact_haar_integral_inversion (orthogonal_group_lch hS)
  (@orthogonal_group_compact_space R (R_n R n) _ (hBn n) n _ (hbn n)) hl hK2.
have hfun : (fun g => real_power (exterior_norm h2 (hBn n) (exterior_product
      (exterior_power_map (hom_as_linear (orthogonal_element_map g)) m xi) eta)) t) =
    (fun g => real_power (exterior_norm h2 (hBn n) (exterior_product
      (exterior_power_map (hom_as_linear (orthogonal_element_map g)) k eta) xi)) t) \o invS.
  apply: funext=> g; rewrite /= (orthogonal_wedge_inverse h2 hS) exterior_product_norm_swap.
  by [].
rewrite hfun hinv in e1.
move: e1; rewrite e2 => -[] he.
have hb1p := hb1.1; have hb2p := hb2.1; have hb3p := hb3.1; have hb4p := hb4.1.
have hq : real_power (beta1 / beta2) t = real_power (beta3 / beta4) t.
  rewrite !real_power_division ?ltW // -!real_power_negative_exponent //.
apply: (real_power_injective _ _ ht hq); apply: divr_ge0; exact: ltW.
Qed.

End RatioCorollary.
