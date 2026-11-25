(** Federer (1969), 2.7.16, example (3), printed pp. 137–138: "xi(G) is an
    open set whose complement has phi x psi measure 0 ... Therefore every
    Haar measure gamma of X is right Delta_G chi^{-1} covariant over G. ...
    For each g in G the commutative diagram in (2) now implies Delta_G(g)
    chi^{-1}(g) = chi'(wedge^1 g^{-1}), and since det(wedge^1 g) = det(g) =
    det(g|W) det(wedge^1 g|W') it follows that Delta_G(g) = |det(g|W)|^{-n}
    . |det g|^m. In particular, G is not unimodular." Here G is
    subspace_stabiliser of SubspaceStabiliser.v with any restricted group
    structure (mulS, invS, eS) of the sealed operations of the linear group,
    a locally compact Hausdorff group, and X is the space of
    StabiliserHomSpace.v with the topology of StabiliserHaarCovariance.v.
    The univalent members of X form an open set (preserving_units_open)
    whose complement is null for every Haar measure gamma of X
    (preserving_units_complement_null, by the polynomial |f(b_1) wedge ...
    wedge f(b_n)|^2 and 2.6.5); it is homeomorphic to G
    (preserving_unit_homeomorphism), and this is G as an open subset of X.
    For a Haar integral mu of X, gamma over G is represented by the integral
    nu(u) = mu(u'), u' the extension by 0 of u to X (stabiliser_restricted,
    by OpenSubspaceExtension.v). The module proves that nu is a nonzero
    monotone Daniell integral on K(G), left chi covariant
    (stabiliser_haar_left_covariant) and hence right Delta_G chi^{-1}
    covariant for every modular function Delta_G by 2.7.9(3)
    (stabiliser_haar_right_modular), and that nu is right |det|^n
    |det(.|W)|^{m-n} covariant (stabiliser_haar_right_covariant), the factor
    being |det(f |-> f o g^{-1})|^{-1} (StabiliserHaarCovariance.v).
    Comparing the two factors gives Delta_G(g) chi^{-1}(g) = |det g|^n
    |det(g|W)|^{m-n} (subspace_stabiliser_modular_ratio), which equals
    chi'(wedge^1 g^{-1}) (subspace_stabiliser_modular_dual), and Delta_G(g)
    = |det(g|W)|^{-n} |det g|^m (subspace_stabiliser_modular). The members
    of G acting as alpha on W and as beta on a complement Z
    (stabiliser_scaling_exists) have det(g|W) = alpha^m and det g = alpha^m
    beta^{n-m}; with alpha = 1, beta = 2 and 0 < m < n, Delta_G(g) =
    2^{m(n-m)} <> 1, so G is not unimodular
    (subspace_stabiliser_not_unimodular, 2.7.12). The instance V = R^n, W in
    G(n, m) is euclidean_subspace_stabiliser_modular and
    euclidean_subspace_stabiliser_not_unimodular. The image measure
    (wedge^1)_# gamma, the space X' and the group G' of Federer's proof are
    not formed: the right covariance is computed directly
    (StabiliserHomSpace.v), and chi' is written out only at wedge^1 g^{-1}. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground InnerProductUP InnerMetric LinearBasis FiniteDualDimension
  Bilinear Annihilator Hom HomInner CoefficientCoordinates ModuleQuotient SubspaceCarrier GrassmannSubspaces
  SymmetricEndomorphisms InnerProductRestriction InvariantRestriction TensorUP ExteriorDeterminant
  FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  BlockDeterminant HomCompositionDeterminant BlockTriangularDeterminant
  FunctionLatticeUP DaniellIntegralUP MonotoneDaniellIntegralUP MonotoneDaniellIntegralSum CompactSupportFunctionUP CompactCutoffUP
  CompactCutoff ProperMapUP HomeomorphismUP DaniellSpacePushforward EquivariantPushforward
  CovariantIntegralUP HaarIntegralUP TopologicalGroupUP TopologicalGroupLaws HaarIntegralExistence
  InvariantIntegralPositivity ModularFunctionUP ModularFunction CovariantHaarCharacterisation
  UnimodularGroupUP UnimodularGroups SubtypeCompactHausdorff IsotropyGroupTopology HomSpaceTopology
  LinearGroupTopology LinearGroupSealed OpenSubspaceExtension HomHaarCovariance FiniteHaarLinear
  OrthonormalFamilies OrthonormalisationUP GramSchmidt PolynomialFunctions PolynomialLinearComposition
  EuclideanLebesgueDimensions MeasureUP HomMonomorphisms
  SubspaceStabiliser StabiliserHomSpace StabiliserHaarCovariance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Scaling.
Variable R : realType.
Local Notation h2 := (euclidean_two_nonzero R).
Variable V : lmodType R.
Variable W : subspace V.
Variable m : nat.
Variable w : 'I_m -> subspace_space W.
Hypothesis hw : is_basis w.
Variable q : nat.
Variable e : 'I_(m + q) -> V.
Hypothesis heb : is_basis e.
Hypothesis hew : forall i, e (lshift q i) = subspace_val (w i).
Local Notation es := (dual_basis heb).
Variables alpha beta : R.

(** Source for [scaling_map]: the linear map acting as alpha on W and
    as beta on the complement Z spanned by e_{m+1}, ..., e_{m+q},
    x |-> alpha x + (beta - alpha) sum_j e_{m+j}*(x) e_{m+j}, a member of
    the group G of Federer 2.7.16, p. 137, for alpha, beta <> 0; used for
    "In particular, G is not unimodular", p. 138. Definition. *)
Definition scaling_map : Hom V V :=
  alpha *: hom_identity V + (beta - alpha) *: \sum_j hom_with_coefficient (e (rshift m j)) (es (rshift m j)).

(** Source for [scaling_mapE]: the values of the scaling map, Federer
    2.7.16, p. 138. Supporting lemma. *)
Lemma scaling_mapE x :
  scaling_map x = alpha *: x + (beta - alpha) *: \sum_j (es (rshift m j) x : R) *: e (rshift m j).
Proof.
rewrite hom_addE !hom_scaleE hom_identityE hom_sum_coefficientsE.
by congr (_ + _ *: _); apply: eq_bigr=> j _; rewrite hom_with_coefficientE.
Qed.

(** Source for [scaling_coordinate_sum]: e_k* of sum_j e_{m+j}*(x)
    e_{m+j} is e_k*(x) for k > m and 0 for k <= m, Federer 1.6.3,
    p. 25; supporting 2.7.16, p. 138. Supporting lemma. *)
Lemma scaling_coordinate_sum (k : 'I_(m + q)) x :
  (es k (\sum_j (es (rshift m j) x : R) *: e (rshift m j)) : R) =
    if (k < m)%N then 0 else es k x.
Proof.
rewrite (big_morph (es k) (linD (hom_linear _)) (lin0 (hom_linear _))).
case: (split_ordP k)=> [i ->|j0 ->].
  rewrite big1 // => j _.
  by rewrite (linZ (hom_linear _)) dual_basisE eq_sym eq_lrshift scaler0.
rewrite (bigD1 j0) // big1 ?Monoid.mulm1.
  by rewrite (linZ (hom_linear _)) dual_basisE eqxx; exact: mulr1.
move=> j /andP [_ hj]; rewrite (linZ (hom_linear _)) dual_basisE.
by rewrite (inj_eq (@rshift_inj m q)) (negbTE hj) scaler0.
Qed.

(** Source for [scaling_coordinate]: e_k*(g(x)) = alpha e_k*(x) for
    k <= m and beta e_k*(x) for k > m, Federer 2.7.16, p. 138.
    Supporting lemma. *)
Lemma scaling_coordinate (k : 'I_(m + q)) x :
  (es k (scaling_map x) : R) = (if (k < m)%N then alpha else beta) * es k x.
Proof.
rewrite scaling_mapE (linD (hom_linear _)) !(linZ (hom_linear _)) scaling_coordinate_sum.
case: (k < m)%N; first by rewrite scaler0 addr0.
by rewrite -scalerDl addrC subrK.
Qed.

(** Source for [scaling_map_injective]: the scaling map is univalent
    for alpha, beta <> 0, Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma scaling_map_injective : alpha != 0 -> beta != 0 -> injective scaling_map.
Proof.
move=> ha hb x y hxy.
rewrite (basis_vector_expansion heb x) (basis_vector_expansion heb y); apply: eq_bigr=> k _.
congr (_ *: _).
have h : (es k (scaling_map x) : R) = es k (scaling_map y) by rewrite hxy.
rewrite !scaling_coordinate in h.
by move: h; case: (k < m)%N=> /mulfI; apply.
Qed.

(** Source for [scaling_map_preserving]: the scaling map maps W into W,
    Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma scaling_map_preserving : preserving_pred W scaling_map.
Proof.
move=> x hx; rewrite scaling_mapE big1 ?scaler0 ?addr0.
  by apply: subspace_scale.
by move=> j _; rewrite ((adapted_subspaceE hw heb hew x).1 hx j) scale0r.
Qed.

(** Source for [scaling_restriction_det]: det(g|W) = alpha^m for the
    scaling map g, Federer 1.3.4, p. 16; supporting 2.7.16, p. 138.
    Supporting lemma. *)
Lemma scaling_restriction_det : det h2 hw (preserving_restriction scaling_map_preserving) = alpha ^+ m.
Proof.
apply: det_scalar_map=> x; apply: subspace_val_injective.
rewrite preserving_restrictionE scaling_mapE big1 ?scaler0 ?addr0; first by rewrite linearZ.
move=> j _; rewrite ((adapted_subspaceE hw heb hew _).1 (subspace_valP x) j) scale0r //.
Qed.

(** Source for [scaling_annihilator_det]: det(wedge^1 g|W') = beta^q
    for the scaling map g, since u o g = beta u for u in W', Federer
    1.3.4, p. 16; supporting 2.7.16, p. 138. Supporting lemma. *)
Lemma scaling_annihilator_det :
  det h2 (annihilator_basisP hw heb hew) (annihilator_restriction scaling_map_preserving) = beta ^+ q.
Proof.
apply: det_scalar_map=> u; apply: subspace_val_injective; apply: hom_ext=> x.
rewrite annihilator_restrictionE scaling_mapE (linD (hom_linear _)) !(linZ (hom_linear _)).
rewrite (big_morph (subspace_val u) (linD (hom_linear _)) (lin0 (hom_linear _))).
have -> : \sum_j subspace_val u ((es (rshift m j) x : R) *: e (rshift m j)) = subspace_val u x.
  rewrite {2}(annihilator_expansion heb hew (subspace_valP u)) hom_sum_coefficientsE.
  apply: eq_bigr=> j _; rewrite (linZ (hom_linear _)) hom_scaleE.
  exact: mulrC.
rewrite linearZ hom_scaleE -scalerDl addrC subrK.
by [].
Qed.

(** Source for [scaling_det]: det g = alpha^m beta^q for the scaling
    map g, by "det(g) = det(g|W) det(wedge^1 g|W')", Federer 2.7.16,
    p. 138. Supporting lemma. *)
Lemma scaling_det :
  det h2 heb (hom_as_linear scaling_map) = alpha ^+ m * beta ^+ q.
Proof.
by rewrite (restriction_annihilator_det hw heb hew scaling_map_preserving)
  scaling_restriction_det scaling_annihilator_det.
Qed.

End Scaling.

Section StabiliserModular.
Variable R : realType.
Local Notation h2 := (euclidean_two_nonzero R).
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation hH := (hom_inner_productP hB hB hb).
Local Notation H := (inner_metric_space hH).
Local Notation GL := (set_type (linear_group hB hb)).
Variable W : subspace V.
Variable m : nat.
Hypothesis hW : grassmann_pred m W.
Local Notation Xs := (subspace_preserving_maps W).
Local Notation hX := (@restricted_inner_productP R (Hom V V) _ hH Xs).
Local Notation X := (inner_metric_space hX).
Local Notation S := (set_type (subspace_stabiliser hB hb W)).
Local Notation KX := (@compactly_supported_continuous_functions R X).
Local Notation KS := (@compactly_supported_continuous_functions R S).
Local Notation chi := (stabiliser_character hW).

(** Source for [stabiliser_scaling_exists]: for alpha, beta <> 0 some
    g in G acts as alpha on W and as beta on a complement Z, so that
    det(g|W) = alpha^m and det g = alpha^m beta^{n-m}, Federer 2.7.16,
    p. 138; used for "In particular, G is not unimodular" and for the
    elements t of 2.7.16(4). Supporting theorem. *)
Theorem stabiliser_scaling_exists (alpha beta : R) : alpha != 0 -> beta != 0 ->
  exists t : S, stabiliser_restriction_det hW t = alpha ^+ m /\
    stabiliser_det t = alpha ^+ m * beta ^+ (n - m).
Proof.
move=> ha hbeta.
have [w hw] := hW.
have [e [heb hew]] := adapted_basis_exists hb hw.
pose t : GL := exist _ (scaling_map heb alpha beta : H) (mem_set (@scaling_map_injective R V m (n - m) e heb alpha beta ha hbeta)).
have ht : subspace_stabiliser hB hb W t.
  by apply/(subspace_stabiliser_iff hW)=> x hx; exact: (scaling_map_preserving hw heb hew alpha beta hx).
exists (exist _ t (mem_set ht)); split.
  rewrite -(stabiliser_restriction_det_basis hW hw).
  rewrite -(scaling_restriction_det hw heb hew alpha beta); apply: det_ext=> x.
  by apply: subspace_val_injective.
rewrite -(stabiliser_det_basis heb).
by rewrite -(scaling_det hw heb hew alpha beta).
Qed.

(** Source for [stabiliser_character_mul]: chi(g h) = chi(g) chi(h),
    Federer 1.3.4, p. 16, as required of chi in 2.7.9, p. 126, for the
    chi of 2.7.16, p. 137. Supporting lemma. *)
Lemma stabiliser_character_mul mulS invS eS :
  is_subgroup_restriction (linear_group_mul hB hb) (linear_group_inv hB hb) (linear_group_unit hB hb)
    (subspace_stabiliser hB hb W) mulS invS eS ->
  forall g h : S, chi (mulS g h) = chi g * chi h.
Proof.
move=> hS g h; rewrite /stabiliser_character (stabiliser_restriction_det_mul hW hS) (stabiliser_det_mul hS).
rewrite !normrM !exprMn !invfM.
by rewrite mulrACA.
Qed.

(** Source for [stabiliser_character_nonzero]: chi(g) <> 0, as required
    in 2.7.9, p. 126. Supporting lemma. *)
Lemma stabiliser_character_nonzero (g : S) : chi g != 0.
Proof.
rewrite /stabiliser_character mulf_neq0 // invr_eq0 expf_neq0 // normr_eq0.
  exact: stabiliser_restriction_det_nonzero.
exact: stabiliser_det_nonzero.
Qed.

(** Source for [stabiliser_character_positive]: chi(g) > 0, supporting
    Federer 2.7.16, p. 137. Supporting lemma. *)
Lemma stabiliser_character_positive (g : S) : 0 < chi g.
Proof.
rewrite /stabiliser_character mulr_gt0 // invr_gt0 exprn_gt0 // normr_gt0.
  exact: stabiliser_restriction_det_nonzero.
exact: stabiliser_det_nonzero.
Qed.

(** Source for [stabiliser_character_continuous]: chi is continuous,
    as required in 2.7.9, p. 126. Supporting lemma. *)
Lemma stabiliser_character_continuous : continuous (chi : S -> real_line_metric R).
Proof.
move=> g.
have h1 := @continuous_inverse_power R S (fun g : S => (stabiliser_restriction_det hW g : R^o)) m
  (@stabiliser_restriction_det_continuous R V B hB n b hb W m hW) (@stabiliser_restriction_det_nonzero R V B hB n b hb W m hW).
have h2' := @continuous_inverse_power R S (fun g : S => (stabiliser_det g : R^o)) (n - m)
  (@stabiliser_det_continuous R V B hB n b hb W) (@stabiliser_det_nonzero R V B hB n b hb W).
exact: (@continuousM R S _ _ g (h1 g) (h2' g)).
Qed.

(** Source for [stabiliser_character_inverse]: chi(g)^{-1} =
    |det(g|W)|^m |det g|^{n-m}, Federer 2.7.16, p. 137. Supporting
    lemma. *)
Lemma stabiliser_character_inverse (g : S) :
  (chi g)^-1 = `|stabiliser_restriction_det hW g| ^+ m * `|stabiliser_det g| ^+ (n - m).
Proof. by rewrite /stabiliser_character invfM !invrK. Qed.

(** Source for [preserving_units]: the univalent members of X, the set
    "xi(G)" of Federer 2.7.16, p. 137, as a subset of X. Definition. *)
Definition preserving_units : set X := [set f | injective (subspace_val f : Hom V V)].

(** Source for [preserving_units_open]: "xi(G) is an open set", Federer
    2.7.16, p. 137: it is the inverse image of the open linear group of
    V (p. 134) under the continuous inclusion of X into Hom(V, V).
    Direct formalisation. *)
Theorem preserving_units_open : open preserving_units.
Proof.
have -> : preserving_units = (fun f : X => (subspace_val f : H)) @^-1` linear_group hB hb by [].
apply: open_comp; last exact: linear_group_set_open.
by move=> f _; exact: preserving_val_continuous.
Qed.

(** Source for [preserving_units_complement_null]: "xi(G) is an open
    set whose complement has phi x psi measure 0", Federer 2.7.16,
    p. 137, for every Haar measure gamma of the additive group of X:
    gamma(S) = c L^N(Phi^{-1}(S)) for an isometry Phi of R^N onto X
    (FiniteHaarLinear.v), and Phi^{-1} of the complement is the zero set
    of the polynomial function |Phi(x)(b_1) wedge ... wedge
    Phi(x)(b_n)|^2 (HomMonomorphisms.v), which does not vanish at
    Phi^{-1}(1_V); hence it is L^N null by 2.6.5, p. 120. Direct
    formalisation. *)
Theorem preserving_units_complement_null (gamma : set X -> \bar R) :
  is_left_haar_measure (fun f g : X => f + g) gamma -> gamma (~` preserving_units) = 0%:E.
Proof.
move=> hg.
have [N [c hc]] := preserving_basis_exists hb hW.
have [e [he hoe]] := orthonormal_basis_exists hX hc.
have ho := orthonormalisation_orthonormal hoe.
have [k hk hkS] := finite_haar_measure_lebesgue hX he ho hg.
pose Phi : {linear R_n R N -> Hom V V} :=
  linear_comp (subspace_inclusion Xs) (GRing.Linear.clone _ _ _ _ (orthonormal_synthesis e) _).
have hP : is_polynomial_function (fun x : R_n R N => (hom_wedge_square b hB (Phi x) : R^o)).
  exact: (polynomial_linear_precompose Phi (hom_wedge_square_polynomial b hB hb)).
pose P := @PolynomialMap R (R_n R N) R^o _ (introT (asboolP _) hP).
have hid : preserving_pred W (hom_identity V) by move=> x hx; rewrite hom_identityE.
have hnz : exists x, P x <> 0.
  exists (orthonormal_analysis (@restricted_inner_product R (Hom V V) (hom_inner hB hB hb) Xs) e
    (@subspace_lift R (Hom V V) Xs _ hid)).
  rewrite /P /= /Phi /=.
  rewrite (orthonormal_analysisK hX he ho) subspace_liftE.
  move=> h0; apply: ((hom_wedge_square_eq0 hb hB _).1 h0).
  by move=> x y; rewrite !hom_identityE.
have hnull := euclidean_polynomial_zero_set_null hnz.
rewrite hkS.
have -> : (orthonormal_synthesis e : _ -> X) @^-1` (~` preserving_units) = [set x | P x = 0].
  apply/seteqP; split=> x /=.
    by move=> hx; apply/(hom_wedge_square_eq0 hb hB _).2.
  by move=> hx; apply/(hom_wedge_square_eq0 hb hB _).1.
by rewrite hnull mule0.
Qed.

Local Notation U := (set_type preserving_units).

(** Source for [preserving_unit_stabiliser]: a univalent member of X
    maps W onto W, so that G is the set of univalent members of X,
    Federer 2.7.16, p. 137. Supporting lemma. *)
Lemma preserving_unit_stabiliser (f : U) :
  subspace_stabiliser hB hb W (exist _ (subspace_val (set_val f) : H) (mem_set (set_valP f)) : GL).
Proof. by apply/(subspace_stabiliser_iff hW)=> x hx; exact: (subspace_valP (set_val f)). Qed.

(** Source for [preserving_unit_map]: the univalent members of X as
    members of G, Federer 2.7.16, p. 137. Definition. *)
Definition preserving_unit_map (f : U) : S :=
  exist _ (exist _ (subspace_val (set_val f) : H) (mem_set (set_valP f)) : GL) (mem_set (preserving_unit_stabiliser f)).

(** Source for [stabiliser_unit_map]: the members of G as univalent
    members of X, Federer 2.7.16, p. 137. Definition. *)
Definition stabiliser_unit_map (g : S) : U :=
  exist _ (@subspace_lift R (Hom V V) Xs (stabiliser_val g) (stabiliser_preserving g) : X)
    (mem_set (@stabiliser_val_injective _ _ _ _ _ _ _ W g)).

(** Source for [preserving_unit_homeomorphism]: G, with the relative
    topology of the linear group, is homeomorphic to the open subset
    xi(G) of X, Federer 2.7.16, p. 137. Supporting theorem. *)
Theorem preserving_unit_homeomorphism : is_homeomorphism_with_inverse preserving_unit_map stabiliser_unit_map.
Proof.
split.
- apply: set_type_continuous_into; apply: set_type_continuous_into.
  move=> f; apply: (@continuous_comp _ _ _ (set_val : U -> X) (fun f : X => (subspace_val f : H))).
    exact: set_type_val_continuous.
  exact: preserving_val_continuous.
- apply: set_type_continuous_into; apply: preserving_continuous_into.
  exact: stabiliser_val_continuous.
- by move=> f; apply: val_inj; apply: subspace_val_injective.
- by move=> g; apply: val_inj; apply: val_inj.
Qed.

(** Source for [preserving_space_hausdorff]: X is Hausdorff, Federer
    2.7.16, p. 137. Supporting lemma. *)
Lemma preserving_space_hausdorff : hausdorff_space X.
Proof. exact: (lch_group_hausdorff (preserving_additive_lch_group hB hb hW)). Qed.

(** Source for [stabiliser_restricted]: nu(u) = mu(u') for u in K(G),
    u' the extension by 0 of u to X through the homeomorphism of G with
    the open set xi(G): the integral over G of the Haar measure gamma of
    X with integral mu, "gamma ... over G", Federer 2.7.16, p. 137.
    Definition. *)
Definition stabiliser_restricted (mu : (X -> R) -> R) (u : S -> R) : R :=
  open_restricted_integral mu (u \o preserving_unit_map).

(** Source for [stabiliser_extension_compact]: u' belongs to K(X)
    whenever u in K(G), Federer 2.5.13, p. 106; supporting 2.7.16,
    p. 137. Supporting lemma. *)
Lemma stabiliser_extension_compact (u : S -> R) : KS u -> KX (open_extension (u \o preserving_unit_map)).
Proof.
move=> hu; apply: (open_extension_compact preserving_space_hausdorff preserving_units_open).
have hp := preserving_unit_homeomorphism.
exact: (compactly_supported_compose (homeomorphism_continuous hp) (homeomorphism_with_inverse_proper hp) hu).
Qed.

(** Source for [stabiliser_extension_left]: (u o L_g)' = u' o A_g,
    where L_g is left multiplication by g on G and A_g(f) = g o f on X:
    g o f is univalent if and only if f is; supporting "gamma ... left
    chi covariant over G", Federer 2.7.16, p. 137. Supporting lemma. *)
Lemma stabiliser_extension_left mulS invS eS :
  is_subgroup_restriction (linear_group_mul hB hb) (linear_group_inv hB hb) (linear_group_unit hB hb)
    (subspace_stabiliser hB hb W) mulS invS eS ->
  forall (u : S -> R) (g : S),
  open_extension ((u \o left_multiplication_action mulS g) \o preserving_unit_map) =
    open_extension (u \o preserving_unit_map) \o stabiliser_action g.
Proof.
move=> hS u g; apply: funext=> f /=.
case: (pselect (preserving_units f))=> hf.
- pose y : U := exist _ f (mem_set hf).
  have hgf : preserving_units (stabiliser_action g f).
    move=> x x' hx; apply: (hf); apply: (@stabiliser_val_injective _ _ _ _ _ _ _ W g).
    exact: hx.
  pose y' : U := exist _ (stabiliser_action g f) (mem_set hgf).
  rewrite -[f]/(set_val y) open_extensionE.
  rewrite -[stabiliser_action g (set_val y)]/(set_val y') open_extensionE /=.
  congr u; apply: val_inj; apply: val_inj.
  change (stabiliser_val (mulS g (preserving_unit_map y)) = stabiliser_val (preserving_unit_map y')).
  by rewrite (stabiliser_mulE hS).
- rewrite !open_extension_out //.
  move=> hgf; apply: hf=> x x' hx; apply: hgf.
  by change (stabiliser_val g (subspace_val f x) = stabiliser_val g (subspace_val f x')); rewrite hx.
Qed.

(** Source for [stabiliser_extension_right]: (u o R_g)' = u' o S_g,
    where R_g(x) = x g^{-1} on G and S_g(f) = f o g^{-1} on X; supporting
    "gamma ... right Delta_G chi^{-1} covariant over G", Federer 2.7.16,
    p. 137. Supporting lemma. *)
Lemma stabiliser_extension_right mulS invS eS :
  is_subgroup_restriction (linear_group_mul hB hb) (linear_group_inv hB hb) (linear_group_unit hB hb)
    (subspace_stabiliser hB hb W) mulS invS eS ->
  forall (u : S -> R) (g : S),
  open_extension ((u \o right_multiplication_action mulS invS g) \o preserving_unit_map) =
    open_extension (u \o preserving_unit_map) \o
      (fun f : X => preserving_right_composition (stabiliser_preserving (invS g)) f : X).
Proof.
move=> hS u g; have [hgi hig] := stabiliser_inv_cancel hS g.
apply: funext=> f /=.
case: (pselect (preserving_units f))=> hf.
- pose y : U := exist _ f (mem_set hf).
  have hfg : preserving_units (preserving_right_composition (stabiliser_preserving (invS g)) f).
    move=> x x' hx; apply: (can_inj hig); apply: (hf).
    exact: hx.
  pose y' : U := exist _ (preserving_right_composition (stabiliser_preserving (invS g)) f) (mem_set hfg).
  rewrite -[f]/(set_val y) open_extensionE.
  rewrite -[preserving_right_composition _ (set_val y)]/(set_val y') open_extensionE /=.
  congr u; apply: val_inj; apply: val_inj.
  change (stabiliser_val (mulS (preserving_unit_map y) (invS g)) = stabiliser_val (preserving_unit_map y')).
  by rewrite (stabiliser_mulE hS).
- rewrite !open_extension_out //.
  move=> hfg; apply: hf=> x x' hx; apply: (can_inj hgi); apply: hfg.
  change (subspace_val f (stabiliser_val (invS g) (stabiliser_val g x)) =
    subspace_val f (stabiliser_val (invS g) (stabiliser_val g x'))).
  by rewrite !hgi hx.
Qed.

Section HaarIntegral.
Variable mu : (X -> R) -> R.
Hypothesis hmu : is_left_haar_integral (fun f g : X => f + g) mu.

(** Source for [stabiliser_restricted_monotone]: nu is a monotone
    Daniell integral on K(G), Federer 2.5.2, p. 92, and 2.5.19,
    p. 113; supporting "gamma ... over G", 2.7.16, p. 137. Supporting
    lemma. *)
Lemma stabiliser_restricted_monotone : is_monotone_daniell_integral KS (stabiliser_restricted mu).
Proof.
have hp := preserving_unit_homeomorphism.
exact: (daniell_pushforward_monotone (homeomorphism_continuous hp) (homeomorphism_with_inverse_proper hp)
  (open_restricted_monotone preserving_space_hausdorff preserving_units_open
    (nonzero_invariant_integral_monotone hmu))).
Qed.

(** Source for [stabiliser_restricted_daniell]: nu is a Daniell
    integral on K(G), Federer 2.5.2, p. 92. Supporting lemma. *)
Lemma stabiliser_restricted_daniell : is_daniell_integral KS (stabiliser_restricted mu).
Proof. exact: monotone_daniell_integral_is_daniell stabiliser_restricted_monotone. Qed.

Section Restriction.
Variables (mulS : S -> S -> S) (invS : S -> S) (eS : S).
Hypothesis hS : is_subgroup_restriction (linear_group_mul hB hb) (linear_group_inv hB hb)
  (linear_group_unit hB hb) (subspace_stabiliser hB hb W) mulS invS eS.
(** Source for [hGc]: G is a locally compact Hausdorff group, Federer
    2.7.16, p. 137. *)
Let hGc := subspace_stabiliser_lch hW hS.

(** Source for [stabiliser_haar_left_covariant]: "gamma ... left chi
    covariant over G", Federer 2.7.16, p. 137, for the integral nu of
    gamma over G: nu(u o L_g) = chi(g) nu(u) whenever u in K(G), g in G,
    by the chi covariance of gamma with respect to the action of G on X.
    Direct formalisation for the associated integral. *)
Theorem stabiliser_haar_left_covariant : is_left_covariant_integral mulS chi (stabiliser_restricted mu).
Proof.
split; first exact: stabiliser_restricted_daniell.
move=> u g hu; rewrite /stabiliser_restricted /open_restricted_integral (stabiliser_extension_left hS).
exact: (covariant_integral_law (preserving_haar_integral_covariant hW hmu) g (stabiliser_extension_compact hu)).
Qed.

(** Source for [stabiliser_haar_right_modular]: "Therefore every Haar
    measure gamma of X is right Delta_G chi^{-1} covariant over G",
    Federer 2.7.16, p. 137, by 2.7.9(3), p. 127, for any modular
    function Delta of G (2.7.8, p. 126), for the integral nu. Direct
    formalisation for the associated integral. *)
Theorem stabiliser_haar_right_modular (Delta : S -> R) :
  is_modular_function mulS invS Delta ->
  is_right_covariant_integral mulS invS (fun g => Delta g * (chi g)^-1) (stabiliser_restricted mu).
Proof.
move=> hD.
exact: (left_covariant_right_modular hGc stabiliser_restricted_daniell (stabiliser_character_mul hS)
  stabiliser_character_nonzero stabiliser_character_continuous hD stabiliser_haar_left_covariant).
Qed.

(** Source for [stabiliser_haar_right_covariant]: the integral nu of
    gamma over G is right |det|^n |det(.|W)|^{m-n} covariant:
    nu(u o R_g) = |det g|^n |det(g|W)|^{m-n} nu(u), the factor being
    |det(f |-> f o g^{-1})|^{-1}; this is what "the commutative diagram
    in (2)" yields in Federer 2.7.16, p. 138. Direct formalisation; the
    determinant of right composition is computed instead of
    transporting gamma by wedge^1. *)
Theorem stabiliser_haar_right_covariant :
  is_right_covariant_integral mulS invS
    (fun g => `|stabiliser_det g| ^+ n * `|stabiliser_restriction_det hW g| ^- (n - m))
    (stabiliser_restricted mu).
Proof.
split; first exact: stabiliser_restricted_daniell.
move=> u g hu; rewrite /stabiliser_restricted /open_restricted_integral (stabiliser_extension_right hS).
rewrite (preserving_haar_integral_right hW (invS g) hmu (stabiliser_extension_compact hu)).
congr (_ * _).
rewrite (stabiliser_det_inv hS) (stabiliser_restriction_det_inv hW hS) !normrV ?unitfE;
  last exact: stabiliser_det_nonzero; last exact: stabiliser_restriction_det_nonzero.
by rewrite -!exprVn invrK.
Qed.

(** Source for [stabiliser_cutoff_positive]: nu(u0) > 0 for a cutoff
    function u0 in K(G)+ with u0(1_V) = 1 (2.5.13, p. 106), since
    u0' in K(X)+ does not vanish at 1_V and Haar integrals are positive
    on K(X)+ ~ {0}; supporting Federer 2.7.16, p. 138. Supporting
    lemma. *)
Lemma stabiliser_cutoff_positive : exists2 u0, KS u0 & 0 < stabiliser_restricted mu u0.
Proof.
pose u0 := compact_cutoff R (lch_group_hausdorff hGc) (lch_group_locally_compact hGc) (@compact_set1 S eS).
have hu := compact_cutoff_specification R (lch_group_hausdorff hGc) (lch_group_locally_compact hGc)
  (@compact_set1 S eS).
have hu0 : KS u0 := compact_cutoff_function hu.
have hu1 : u0 eS = 1 by exact: compact_cutoff_on_set hu eS erefl.
have hur x : 0 <= u0 x by have /andP[] := compact_cutoff_range hu x.
exists u0=> //.
apply: (left_haar_integral_positive (lch_group_topological (preserving_additive_lch_group hB hb hW)) hmu).
- exact: stabiliser_extension_compact.
- by move=> f; rewrite /open_extension; case: pselect=> // h; exact: hur.
- exists (set_val (stabiliser_unit_map eS)); rewrite open_extensionE /=.
  rewrite (homeomorphism_right_inverse preserving_unit_homeomorphism) hu1.
  by apply/eqP; exact: oner_neq0.
Qed.

End Restriction.

End HaarIntegral.

Section Modular.
Variables (mulS : S -> S -> S) (invS : S -> S) (eS : S).
Hypothesis hS : is_subgroup_restriction (linear_group_mul hB hb) (linear_group_inv hB hb)
  (linear_group_unit hB hb) (subspace_stabiliser hB hb W) mulS invS eS.
(** Source for [hGc]: G is a locally compact Hausdorff group, Federer
    2.7.16, p. 137. *)
Let hGc := subspace_stabiliser_lch hW hS.

(** Source for [modular_exponent_algebra]: the arithmetic of "it follows
    that Delta_G(g) = |det(g|W)|^{-n} |det g|^m", Federer 2.7.16,
    p. 138: from D a^p d^q = d^{p+q} a^{-q} with a, d <> 0 follows
    D = a^{-(p+q)} d^p. Supporting lemma. *)
Lemma modular_exponent_algebra (D a d : R) (p q : nat) : a != 0 -> d != 0 ->
  D * (a ^+ p * d ^+ q) = d ^+ (p + q) * a ^- q -> D = a ^- (p + q) * d ^+ p.
Proof.
move=> ha hd h.
have hq0 : a ^+ p * d ^+ q != 0 by rewrite mulf_neq0 // expf_neq0.
apply: (mulIf hq0); rewrite h !exprD invfM.
rewrite [RHS]mulrC !mulrA [a ^+ p * d ^+ q]mulrC -[d ^+ q * a ^+ p * _]mulrA mulfV ?expf_neq0 // mulr1.
by rewrite mulrC !mulrA [d ^+ p * d ^+ q]mulrC.
Qed.

(** Source for [dual_exponent_algebra]: the arithmetic of
    "Delta_G(g) chi^{-1}(g) = chi'(wedge^1 g^{-1})", Federer 2.7.16,
    p. 138: |d|^{p+q} |a|^{-q} = |a / d|^{-q} |d^{-1}|^{-p} for
    a, d <> 0. Supporting lemma. *)
Lemma dual_exponent_algebra (a d : R) (p q : nat) : a != 0 -> d != 0 ->
  `|d| ^+ (p + q) / `|a| ^+ q = `|a / d| ^- q / `|d^-1| ^+ p.
Proof.
move=> ha hd.
rewrite normrM !normrV ?unitfE // exprMn !exprVn invfM !invrK exprD.
by rewrite [LHS]mulrC -mulrA [`|d| ^+ q * _]mulrC.
Qed.

(** Source for [subspace_stabiliser_modular_ratio]: "every Haar
    measure gamma of X is right Delta_G chi^{-1} covariant over G" and
    the right covariance obtained from "the commutative diagram in (2)",
    Federer 2.7.16, pp. 137–138, give Delta_G(g) chi^{-1}(g) =
    |det g|^n |det(g|W)|^{m-n} for any modular function Delta of G
    (2.7.8, p. 126), since nu(u0) <> 0 for a cutoff u0; a Haar integral
    of X exists by 2.7.5, p. 125. Supporting theorem. *)
Theorem subspace_stabiliser_modular_ratio (Delta : S -> R) :
  is_modular_function mulS invS Delta ->
  forall g, Delta g * (chi g)^-1 = `|stabiliser_det g| ^+ n * `|stabiliser_restriction_det hW g| ^- (n - m).
Proof.
move=> hD g.
have [mu hmu] := left_haar_integral_exists R (preserving_additive_lch_group hB hb hW).
have [u0 hu0 hpos] := stabiliser_cutoff_positive hmu hS.
have h1 := covariant_integral_law (stabiliser_haar_right_modular hmu hS hD) g hu0.
have h2' := covariant_integral_law (stabiliser_haar_right_covariant hmu hS) g hu0.
rewrite h1 in h2'.
exact: (mulIf (lt0r_neq0 hpos) h2').
Qed.

(** Source for [subspace_stabiliser_modular_dual]: "For each g in G the
    commutative diagram in (2) now implies Delta_G(g) chi^{-1}(g) =
    chi'(wedge^1 g^{-1})", Federer 2.7.16, p. 138, with
    "chi'(h) = |det(h|W')|^{m-n} . |det h|^{-m}" evaluated at
    h = wedge^1 g^{-1} (dual_map), h|W' = annihilator_restriction, for
    an adapted base e. Direct formalisation; chi' is written out for the
    single element wedge^1 g^{-1}, and G' and X' are not formed. *)
Theorem subspace_stabiliser_modular_dual (w : 'I_m -> subspace_space W) (hw : is_basis w)
    (e : 'I_(m + (n - m)) -> V) (heb : is_basis e) (hew : forall i, e (lshift (n - m) i) = subspace_val (w i))
    (Delta : S -> R) :
  is_modular_function mulS invS Delta ->
  forall g, Delta g * (chi g)^-1 =
    `|det h2 (annihilator_basisP hw heb hew) (annihilator_restriction (stabiliser_preserving (invS g)))|
      ^- (n - m) *
    `|det h2 (dual_basisP heb) (dual_map (hom_as_linear (stabiliser_val (invS g))))| ^- m.
Proof.
move=> hD g; rewrite (subspace_stabiliser_modular_ratio hD).
have hmn := subspace_dimension_le hb hw.
have ha := stabiliser_restriction_det_nonzero hW g.
have hd := stabiliser_det_nonzero g.
have hrel := stabiliser_restriction_annihilator_det hW hw heb hew (invS g).
rewrite (stabiliser_det_inv hS) (stabiliser_restriction_det_inv hW hS) in hrel.
have hA : det h2 (annihilator_basisP hw heb hew) (annihilator_restriction (stabiliser_preserving (invS g))) =
    stabiliser_restriction_det hW g / stabiliser_det g.
  by rewrite -[LHS](mulVKf ha) -hrel.
rewrite hA (dual_map_det h2 heb) (stabiliser_det_basis heb) (stabiliser_det_inv hS).
by rewrite -dual_exponent_algebra // subnKC.
Qed.

(** Source for [subspace_stabiliser_modular]: "it follows that
    Delta_G(g) = |det(g|W)|^{-n} . |det g|^m", Federer 2.7.16, p. 138,
    for any modular function Delta of G (2.7.8, p. 126), from
    subspace_stabiliser_modular_ratio and chi(g) = |det(g|W)|^{-m}
    |det g|^{m-n}. Direct formalisation; the hypotheses 0 < m < n are
    not needed. *)
Theorem subspace_stabiliser_modular (Delta : S -> R) :
  is_modular_function mulS invS Delta ->
  forall g, Delta g = `|stabiliser_restriction_det hW g| ^- n * `|stabiliser_det g| ^+ m.
Proof.
move=> hD g.
have h3 := subspace_stabiliser_modular_ratio hD g.
rewrite stabiliser_character_inverse in h3.
have [w hw] := hW.
have hmn := subspace_dimension_le hb hw.
have ha : `|stabiliser_restriction_det hW g| != 0.
  by rewrite normr_eq0; exact: stabiliser_restriction_det_nonzero.
have hd : `|stabiliser_det g| != 0 by rewrite normr_eq0; exact: stabiliser_det_nonzero.
have := @modular_exponent_algebra (Delta g) _ _ m (n - m) ha hd.
by rewrite subnKC //; apply.
Qed.

(** Source for [subspace_stabiliser_not_unimodular]: "In particular, G
    is not unimodular", Federer 2.7.16, p. 138, in the sense of 2.7.12,
    p. 129: for 0 < m < n the member g of G acting as 1 on W and as 2
    on a complement has Delta_G(g) = 2^{m(n-m)} <> 1. Direct
    formalisation. *)
Theorem subspace_stabiliser_not_unimodular : (0 < m)%N -> (m < n)%N -> ~ is_unimodular R mulS invS.
Proof.
move=> hm hmn hU.
have [D hD] := modular_function_exists R hGc.
have h1 := (unimodular_iff_modular_unit hGc hD).1 hU.
have h20 : (1 + 1 : R) != 0 := h2.
have [t [ht1 ht2]] := stabiliser_scaling_exists (oner_neq0 R) h20.
have := h1 t; rewrite (subspace_stabiliser_modular hD) ht1 ht2 expr1n mul1r normr1 expr1n invr1 mul1r.
rewrite normrX -exprM ger0_norm ?addr_ge0 ?ler01 //.
move/eqP; rewrite eq_sym; apply/negP; rewrite neq_lt; apply/orP; left.
rewrite exprn_egt1; last by rewrite ltrDl ltr01.
by rewrite muln_eq0 negb_or -!lt0n subn_gt0 hmn hm.
Qed.

End Modular.

End StabiliserModular.

Section Euclidean.
Variable R : realType.
Variable n : nat.
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation hb := (@coordinate_basisP R n).
Variable m : nat.
Variable W : G (R_n R n) m.
Local Notation S := (set_type (subspace_stabiliser hB hb (grassmann_val W))).

(** Source for [euclidean_subspace_stabiliser_modular]: "Delta_G(g) =
    |det(g|W)|^{-n} . |det g|^m" for the group G = GL(n, R)^W of the
    linear automorphisms of R^n mapping W in G(n, m) onto W, Federer
    2.7.16, p. 138 (the group of 2.7.16(3), used in (4) and (5)).
    Direct formalisation of the instance. *)
Corollary euclidean_subspace_stabiliser_modular (mulS : S -> S -> S) (invS : S -> S) (eS : S) :
  is_subgroup_restriction (linear_group_mul hB hb) (linear_group_inv hB hb) (linear_group_unit hB hb)
    (subspace_stabiliser hB hb (grassmann_val W)) mulS invS eS ->
  forall Delta : S -> R, is_modular_function mulS invS Delta ->
  forall g, Delta g = `|stabiliser_restriction_det (grassmann_proof W) g| ^- n * `|stabiliser_det g| ^+ m.
Proof. by move=> hS Delta hD; exact: (subspace_stabiliser_modular (grassmann_proof W) hS hD). Qed.

(** Source for [euclidean_subspace_stabiliser_not_unimodular]: "In
    particular, G is not unimodular", Federer 2.7.16, p. 138, for
    G = GL(n, R)^W and 0 < m < n. Direct formalisation of the
    instance. *)
Corollary euclidean_subspace_stabiliser_not_unimodular (mulS : S -> S -> S) (invS : S -> S) (eS : S) :
  is_subgroup_restriction (linear_group_mul hB hb) (linear_group_inv hB hb) (linear_group_unit hB hb)
    (subspace_stabiliser hB hb (grassmann_val W)) mulS invS eS ->
  (0 < m)%N -> (m < n)%N -> ~ is_unimodular R mulS invS.
Proof. by move=> hS; exact: (subspace_stabiliser_not_unimodular (grassmann_proof W) hS). Qed.

End Euclidean.
