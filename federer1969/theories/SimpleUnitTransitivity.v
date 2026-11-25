(** Federer (1969), 2.7.16, printed p. 139, example (6), from the proof of
    the existence of beta_t(n, m): "In fact the integral is positively
    homogeneous of degree t with respect to xi, the group O(n) acts
    transitively on the set of all simple m vectors of norm 1, and the
    invariance of theta*_{n,m} implies the integrals corresponding to xi and
    (Lambda_m g) xi are equal whenever g in O(n)." The two facts are proved
    here as stated, for 0 < m (Federer's n >= m are positive integers).
    Transitivity: a simple unit m-vector is c e_1 wedge ... wedge e_m with e
    orthonormal and c = 1 or c = -1 (1.7.5, p. 32); replacing the first
    vector of the target frame by its negative changes the sign of the
    product (1.3.1, p. 13), and an orthogonal map of R^n carries one
    orthonormal frame onto another (OrthogonalInjectionSpaces.v).
    Invariance: |(Lambda_m p)((Lambda_m g) xi)| = |(Lambda_m A(g^{-1}, p))
    xi| with A(h, p) = p o h^{-1}, and the invariant integral of
    theta*_{n,m} is invariant under A. The existence proof of
    OrthogonalProjectionConstants.v uses the frame form of the transitivity,
    which also covers m = 0. The local erratum has no entry for p. 139. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  topology constructive_ereal.
From Federer Require Import TensorUP InnerProductUP InnerNorm InnerMetric LinearBasis Hom HomInner
  OrthogonalMaps OrthonormalFamilies AdjointUP Adjoint GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates CoordinateProjection OrthonormalFrameMap IsotropyGroupTopology TopologicalGroupUP
  TopologicalGroupLaws HomogeneousSpaceUP CompactSupportFunctionUP CovariantIntegralUP HaarIntegralUP
  RealIntegralFunctionalUP SummableRealFunctionUP MeasureUP MeasureIntegralUP
  MeasureIntegralUniqueness RealPower HomSpaceTopology LinearGroupTopology LinearGroupSealed
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure CompactGroupHomogeneousMeasures
  OrthogonalInjectionSpaces EuclideanOrthogonalInvariantMeasures ExteriorAlgebra ExteriorGrading
  ExteriorMaps ExteriorMapScaling ExteriorExpansion FiniteExteriorPowers InnerExterior ExteriorNorm
  AssociatedSubspace SimpleElementary SimpleOrthonormalFactor ExteriorMapNormContinuity
  OrthogonalProjectionConstants AlgebraUP GradedComponents GradedAlgebra ModuleQuotient Bilinear
  ExteriorNormNaturality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [e_lambda_negate_one]: replacing one factor by its
    negative changes the sign of a product of vectors, Federer 1.3.1,
    p. 13 (multilinearity), supporting "the group O(n) acts transitively
    on the set of all simple m vectors of norm 1", 2.7.16, p. 139.
    Supporting lemma. *)
Lemma e_lambda_negate_one (K : fieldType) (V : lmodType K) m (e : 'I_m -> V) (i0 : 'I_m) :
  e_lambda (fun i => (if i == i0 then -1 else 1) *: e i) (ord_tuple m) = - e_lambda e (ord_tuple m).
Proof.
apply: val_inj.
change (component_val (e_lambda (fun i => (if i == i0 then -1 else 1) *: e i) (ord_tuple m)) =
  component_val (- e_lambda e (ord_tuple m))).
rewrite linearN !e_lambdaE exterior_word_scaled.
rewrite (bigD1_seq i0) ?mem_enum ?enum_uniq //= eqxx big1_seq ?mulr1 ?scaleN1r //.
by move=> i /andP [/negPf -> _].
Qed.

Section Transitivity.
Variable R : realType.
Hypothesis h2 : (1 + 1 : R) != 0.
Variables n m : nat.
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hBm := (@euclidean_inner_productP R m).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation hbm := (@coordinate_basisP R m).
Local Notation O := (euclidean_orthogonal_group R n).
Local Notation om := (@orthogonal_element_map R (R_n R n) _ hBn n _ hbn).

(** Source for [simple_unit_transitive]: "the group O(n) acts
    transitively on the set of all simple m vectors of norm 1", Federer
    2.7.16, p. 139, for 0 < m: for simple xi, zeta with |xi| = 1 = |zeta|
    there is g in O(n) with (Lambda_m g) xi = zeta. Direct formalisation;
    the proof is supplied (see the header). *)
Theorem simple_unit_transitive (xi zeta : exterior_power (R_n R n) m) :
  (0 < m)%N -> simple xi -> simple zeta -> exterior_norm h2 hBn xi = 1 ->
  exterior_norm h2 hBn zeta = 1 ->
  exists g : O, exterior_power_map (hom_as_linear (om g)) m xi = zeta.
Proof.
move=> hm hsx hsz hx1 hz1.
have hnz (y : exterior_power (R_n R n) m) : exterior_norm h2 hBn y = 1 -> y != 0.
  by move=> hy; apply/eqP=> hy0; move: hy; rewrite hy0 exterior_norm_zero => /eqP; rewrite eq_sym oner_eq0.
have [e [c [he [hc hxe]]]] := simple_orthonormal_factor h2 hBn (hnz _ hx1) hsx.
have [f [d [hf [hd hzf]]]] := simple_orthonormal_factor h2 hBn (hnz _ hz1) hsz.
have hc1 : `|c| = 1 by move: hx1; rewrite hxe exterior_norm_scale orthonormal_product_unit_norm // mulr1.
have hd1 : `|d| = 1 by move: hz1; rewrite hzf exterior_norm_scale orthonormal_product_unit_norm // mulr1.
have hsign (a : R) : `|a| = 1 -> a = 1 \/ a = -1.
  move=> ha; case: (lerP 0 a)=> h0; first by left; rewrite -ha ger0_norm.
  by right; rewrite -ha ltr0_norm // opprK.
pose i0 : 'I_m := Ordinal hm.
pose s : R := if c == d then 1 else -1.
pose f' (i : 'I_m) := (if (i == i0) && (c != d) then -1 else 1) *: f i.
have hf' : orthonormal_family (@euclidean_inner_product R n) f'.
  move=> i j; rewrite /f' (bilZl (inner_bilinear hBn)) (bilZr (inner_bilinear hBn)) hf.
  case: (eqVneq i j)=> [->|hij]; last by rewrite !scaler0.
  by case: ifP=> _; rewrite scalerA ?mulrNN mulr1 scale1r.
have hzf' : zeta = c *: e_lambda f' (ord_tuple m).
  case: (eqVneq c d)=> [hcd|hcd].
    rewrite hzf hcd; congr (_ *: e_lambda _ _); apply: funext=> i.
    by rewrite /f' hcd eqxx andbF scale1r.
  have -> : f' = (fun i => (if i == i0 then -1 else 1) *: f i).
    by apply: funext=> i; rewrite /f' hcd andbT.
  rewrite e_lambda_negate_one scalerN -scaleNr hzf; congr (_ *: _).
  have [hc'|hc'] := hsign c hc1; have [hd'|hd'] := hsign d hd1; move: hcd; rewrite hc' hd' ?eqxx //.
  by move=> _; rewrite opprK.
have [phi [hphi hphie]] := orthonormal_frame_map_exists hBn he.
have [phi' [hphi' hphie']] := orthonormal_frame_map_exists hBn hf'.
have [g0 [hg0 hgf]] := orthogonal_injection_transitive hBm hBn hbm hbn hphi hphi'.
exists (orthogonal_element_of hBn hbn hg0).
rewrite hxe linearZ exterior_power_map_e_lambda hzf'; congr (_ *: e_lambda _ _).
apply: funext=> i.
change (hom_as_linear (om (orthogonal_element_of hBn hbn hg0)) (e i) = f' i).
rewrite hom_as_linearE orthogonal_element_ofE.
by rewrite -hphie hgf hphie'.
Qed.

Variables (mulS : O -> O -> O) (invS : O -> O) (eS : O).
Hypothesis hS : is_subgroup_restriction (linear_group_mul hBn hbn) (linear_group_inv hBn hbn)
  (linear_group_unit hBn hbn) O mulS invS eS.
Local Notation A := (orthogonal_projection_action hBm hBn hbn hS).

(** Source for [hOG]: the group laws of O(n), used in this section. *)
Let hOG : is_group_laws mulS invS eS :=
  topological_group_laws (lch_group_topological (orthogonal_group_lch hS)).

(** Source for [projection_norm_rotation]: |(Lambda_m p)((Lambda_m g)
    xi)| = |(Lambda_m A(g^{-1}, p)) xi|, where A(h, p) = p o h^{-1};
    supporting "the invariance of theta*_{n,m} implies the integrals
    corresponding to xi and (Lambda_m g) xi are equal", Federer 2.7.16,
    p. 139. Supporting lemma. *)
Lemma projection_norm_rotation (g : O) (xi : exterior_power (R_n R n) m) p :
  projection_norm h2 (exterior_power_map (hom_as_linear (om g)) m xi) p =
    projection_norm h2 xi (A (invS g) p).
Proof.
rewrite /projection_norm exterior_power_map_composition.
congr (exterior_norm _ _ _); apply: exterior_power_map_ext=> v.
rewrite [RHS]hom_as_linearE orthogonal_projection_actionE (group_invK hOG).
by rewrite /linear_comp /= ?hom_as_linearE.
Qed.

(** Source for [projection_integral_rotation]: "the invariance of
    theta*_{n,m} implies the integrals corresponding to xi and
    (Lambda_m g) xi are equal whenever g in O(n)", Federer 2.7.16,
    p. 139: for every normalised invariant measure phi over O*(n, m),
    t > 0, simple xi and g in O(n), int |(Lambda_m p)((Lambda_m g) xi)|^t
    dphi p = int |(Lambda_m p) xi|^t dphi p. Direct formalisation. *)
Theorem projection_integral_rotation (phi : set (set_type (euclidean_orthogonal_projections R n m)) -> \bar R)
    (t : R) (g : O) (xi : exterior_power (R_n R n) m) a :
  is_normalised_invariant_measure A phi -> 0 < t -> simple xi ->
  is_measure_integral phi (real_total_integrand (fun p => real_power (projection_norm h2 xi p) t)) a ->
  is_measure_integral phi (real_total_integrand (fun p =>
    real_power (projection_norm h2 (exterior_power_map (hom_as_linear (om g)) m xi) p) t)) a.
Proof.
move=> hphi ht hs ha.
have [nu [hnu hrep _ _]] := normalised_invariant_measure_integral hphi.
have hK := projection_norm_power_compact h2 hS hs ht.
have hK' := projection_norm_power_compact h2 hS (exterior_power_map_simple (hom_as_linear (om g)) hs) ht.
rewrite -(measure_integral_unique (hrep _ hK) ha).
have -> : nu (fun p => real_power (projection_norm h2 xi p) t) =
    nu (fun p => real_power (projection_norm h2 (exterior_power_map (hom_as_linear (om g)) m xi) p) t).
  have -> : (fun p => real_power (projection_norm h2 (exterior_power_map (hom_as_linear (om g)) m xi) p) t) =
      (fun p => real_power (projection_norm h2 xi p) t) \o A (invS g).
    by apply: funext=> p; rewrite /= projection_norm_rotation.
  rewrite (covariant_integral_law (nonzero_invariant_integral_invariant hnu) (invS g) hK).
  by rewrite mul1r.
exact: hrep _ hK'.
Qed.

End Transitivity.
