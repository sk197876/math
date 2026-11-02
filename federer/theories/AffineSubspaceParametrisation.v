(** Federer (1969), 2.7.16, printed pp. 140–141, example (7): "To prove this
    we consider the maps xi: O(n) x R^{n-m} -> X, xi(s, y) = s(p^{-1}{y}),
    delta: X -> R, delta(W) = distance(W, 0). Since im p* = im(p* o p) is
    the orthogonal complement of ker p, ... delta[(s o tau_z) ker p] =
    |p(z)| whenever z in R^n, s in O(n), (delta o xi)(s, y) = |y| whenever y
    in R^{n-m}, s in O(n), we see that xi is continuous and open, im xi = X,
    delta is continuous, xi is proper ... Then we use the fact that t xi(s,
    y) = xi(t s, y), tau_z xi(s, y) = xi(s, y + (p o s^{-1}) z) whenever s
    in O(n), y in R^{n-m}, t in O(n), z in R^n." Here X is the space of m
    dimensional affine subspaces of R^n with the topology of
    AffineSubspaceSpace.v, p is a point of O*(n, n - m), and p^{-1}{y} is
    projection_fibre (OrthogonalProjectionFibres.v). The proofs are
    supplied: xi(s, y) = (tau_{s(v)} o s)[ker p] whenever p(v) = y, so xi is
    the composite of (s, v) |-> (s, p(v))^{-1}, the homeomorphism (s, v) |->
    tau_{s(v)} o s of O(n) x R^n onto G and the open orbit map of G at ker
    p; im xi = X by the transitivity of G on X; the nearest point of xi(s,
    y) is s(p*(y)); and xi^{-1}(C) is a closed subset of O(n) x {y : |y| <=
    r} for compact C, delta being bounded on C. The local erratum has no
    entry for pp. 140–141. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground InnerProductUP InnerProductLaws InnerNorm InnerMetric
  InnerNormedTopology LinearBasis Bilinear TensorUP Hom HomInner ModuleQuotient GrassmannSubspaces
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct OrthogonalMaps ProperMapUP
  IsotropyGroupTopology TopologicalProductMaps TopologicalGroupUP TopologicalGroupLaws
  HomogeneousSpaceUP HomogeneousSpaceLaws HomeomorphismUP HomSpaceTopology LinearGroupTopology
  LinearGroupSealed OrthogonalGroupTopology OrthogonalGroupHaarMeasure OrthogonalInjectionSpaces
  GrassmannHomogeneousSpace EuclideanAdditiveGroup AffineGroupTopology IsometryGroupStructure
  AffineSubspaceSpace OrthogonalProjectionFibres.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Parametrisation.
Variable R : realType.
Variables n m : nat.
Hypothesis hmn : (m <= n)%N.
Local Notation k := (n - m)%N.
Local Notation Vn := (R_n R n).
Local Notation Vk := (R_n R k).
Local Notation Bn := (@euclidean_inner_product R n).
Local Notation Bk := (@euclidean_inner_product R k).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hBk := (@euclidean_inner_productP R k).
Local Notation hBm := (@euclidean_inner_productP R m).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation hbk := (@coordinate_basisP R k).
Local Notation hbm := (@coordinate_basisP R m).
Local Notation E := (inner_metric_space hBn).
Local Notation Ek := (inner_metric_space hBk).
Local Notation HVV := (inner_metric_space (hom_inner_productP hBn hBn hbn)).
Local Notation Hkn := (inner_metric_space (hom_inner_productP hBk hBn hbk)).
Local Notation GR := (grassmann_space hBm hBn hbm hbn).
Local Notation X := (affine_subspace_space hBm hBn hbm hbn).
Local Notation O := (orthogonal_group hBn hbn).
Local Notation G := (isometry_group hBn hbn).
Local Notation OP := (set_type (orthogonal_projections hBk hBn hbn)).
Local Notation pm := (@orthogonal_projection_map R Vk Vn Bk Bn hBk hBn n _ hbn).
Local Notation om := (@orthogonal_element_map R Vn Bn hBn n _ hbn).
Local Notation Aact := (affine_subspace_action hBm hBn hbm hbn).
Local Notation gact := (grassmann_action hBm hBn hbm hbn).
Local Notation nearest := (affine_nearest hBm hBn hbm).
Local Notation delta := (affine_origin_distance hBm hBn hbm).
Local Notation fibre := (projection_fibre hmn).

Variables (mulS : G -> G -> G) (invS : G -> G) (eS : G).
Hypothesis hS : is_subgroup_restriction (affine_group_mul hBn hbn) (affine_group_inv hBn hbn)
  (affine_group_unit hBn hbn) G mulS invS eS.
Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction (linear_group_mul hBn hbn) (linear_group_inv hBn hbn)
  (linear_group_unit hBn hbn) O mulO invO eO.
Variable p : OP.
Local Notation pstar := (projection_adjoint p).

(** Source for [hXA]: X is a homogeneous space of G, used in this
    section (AffineSubspaceSpace.v). *)
Let hXA : is_homogeneous_space mulS Aact := affine_subspace_homogeneous hBm hbm hS hO.
(** Source for [hOc]: O(n) is compact, Federer 2.7.16, p. 139, used in
    this section. *)
Let hOc : compact [set: O] := @orthogonal_group_compact_space R Vn Bn hBn n _ hbn.

(** Source for [affine_parametrisation]: the map
    xi(s, y) = s(p^{-1}{y}) of O(n) x R^{n-m} into X, Federer 2.7.16,
    p. 140. Definition. *)
Definition affine_parametrisation (q : O * Ek) : X := Aact (isometry_of q.1 0) (fibre p q.2).

Local Notation xi := affine_parametrisation.

(** Source for [affine_parametrisationE]: x belongs to s(p^{-1}{y}) if
    and only if x = s(w) for some w with p(w) = y, Federer 2.7.16,
    p. 140. Supporting lemma. *)
Lemma affine_parametrisationE (s : O) (y : Ek) x :
  affine_points (xi (s, y)) x <-> exists2 w, pm p w = y & om s w = x.
Proof.
rewrite /xi affine_subspace_actionE; split.
- by move=> [w /projection_fibreE hw <-]; exists w=> //; rewrite isometry_of_mapE add0r.
- by move=> [w hw <-]; exists w; [exact/projection_fibreE|rewrite isometry_of_mapE add0r].
Qed.

(** Source for [affine_parametrisation_direction]: dir xi(s, y) =
    s[ker p], Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma affine_parametrisation_direction (s : O) (y : Ek) :
  affine_direction (xi (s, y)) = gact s (projection_kernel hmn p).
Proof.
by rewrite /xi affine_subspace_action_direction isometry_of_linear projection_fibre_direction.
Qed.

(** Source for [affine_parametrisation_nearest]: the point of xi(s, y)
    nearest to 0 is s(p*(y)), Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma affine_parametrisation_nearest (s : O) (y : Ek) : nearest (xi (s, y)) = om s (pstar y).
Proof.
apply: esym; apply: affine_nearest_unique.
- by apply/affine_parametrisationE; exists (pstar y)=> //; exact: projection_adjointK.
- move=> w; rewrite affine_parametrisation_direction grassmann_actionE=> -[w' hw' <-].
  rewrite (orthogonal_element_inner s); apply: projection_adjoint_perp.
  exact/projection_kernelE.
Qed.

(** Source for [affine_parametrisation_distance]: "(delta o xi)(s, y) =
    |y| whenever y in R^{n-m}, s in O(n)", Federer 2.7.16, p. 140.
    Direct formalisation. *)
Theorem affine_parametrisation_distance (s : O) (y : Ek) : delta (xi (s, y)) = inner_norm hBk y.
Proof.
rewrite /affine_origin_distance affine_parametrisation_nearest.
rewrite (orthogonal_map_norm hBn hBn (orthogonal_element_orthogonal s)).
apply: esym; apply: (inner_norm_value hBk (inner_norm_nonnegative hBn (pstar y))).
by rewrite (inner_norm_sqr hBn) projection_adjoint_orthogonal.
Qed.

(** Source for [affine_rotated_translate]: (s o tau_v)[ker p] =
    s(p^{-1}{p(v)}), Federer 2.7.16, p. 140, from
    "tau_z ker p = tau_{(p* o p) z} ker p". Supporting lemma. *)
Lemma affine_rotated_translate (s : O) (v : Vn) : Aact (isometry_of s (om s v)) (fibre p 0) = xi (s, pm p v).
Proof.
apply: affine_subspace_ext=> x; split.
- move=> /affine_subspace_actionE [w /projection_fibreE hw <-].
  apply/affine_parametrisationE; exists (v + w).
    by rewrite (linearD (hom_as_linear (pm p))) /= hw addr0.
  by rewrite isometry_of_mapE (linearD (hom_as_linear (om s))).
- move=> /affine_parametrisationE [w hw <-]; apply/affine_subspace_actionE; exists (w - v).
    apply/projection_fibreE; rewrite (linearB (hom_as_linear (pm p))) /= hw; exact: subrr.
  by rewrite isometry_of_mapE -(linearD (hom_as_linear (om s))) /= addrC subrK.
Qed.

(** Source for [affine_rotated_translate_distance]: "delta[(s o tau_z)
    ker p] = |p(z)| whenever z in R^n, s in O(n)", Federer 2.7.16,
    p. 140. Direct formalisation; (s o tau_z)[ker p] is the image of
    p^{-1}{0} = ker p under tau_{s(z)} o s. *)
Theorem affine_rotated_translate_distance (s : O) (z : Vn) :
  delta (Aact (isometry_of s (om s z)) (fibre p 0)) = inner_norm hBk (pm p z).
Proof. by rewrite affine_rotated_translate affine_parametrisation_distance. Qed.

(** Source for [affine_parametrisation_rotate]: "t xi(s, y) =
    xi(t s, y)", Federer 2.7.16, p. 141. Direct formalisation. *)
Theorem affine_parametrisation_rotate (t s : O) (y : Ek) :
  Aact (isometry_of t 0) (xi (s, y)) = xi (mulO t s, y).
Proof.
apply: affine_subspace_ext=> x; split.
- move=> /affine_subspace_actionE [w' /affine_parametrisationE [w hw <-] <-].
  apply/affine_parametrisationE; exists w=> //.
  by rewrite isometry_of_mapE add0r (orthogonal_element_mulE hO).
- move=> /affine_parametrisationE [w hw <-]; apply/affine_subspace_actionE.
  exists (om s w); first by apply/affine_parametrisationE; exists w.
  by rewrite isometry_of_mapE add0r (orthogonal_element_mulE hO).
Qed.

(** Source for [affine_parametrisation_translate]: "tau_z xi(s, y) =
    xi(s, y + (p o s^{-1}) z)", Federer 2.7.16, p. 141. Direct
    formalisation. *)
Theorem affine_parametrisation_translate (z : Vn) (s : O) (y : Ek) :
  Aact (isometry_of eO z) (xi (s, y)) = xi (s, y + pm p (om (invO s) z)).
Proof.
have [hsi his] := orthogonal_element_inv hO s.
have hl (u w : Vn) : pm p (u + w) = pm p u + pm p w := linearD (hom_as_linear (pm p)) u w.
have hls (u w : Vn) : om s (u + w) = om s u + om s w := linearD (hom_as_linear (om s)) u w.
apply: affine_subspace_ext=> x; split.
- move=> /affine_subspace_actionE [w' /affine_parametrisationE [w hw <-] <-].
  apply/affine_parametrisationE; exists (w + om (invO s) z).
    by rewrite hl hw.
  by rewrite isometry_of_mapE (orthogonal_element_unit hO) hls his addrC.
- move=> /affine_parametrisationE [w hw <-]; apply/affine_subspace_actionE.
  exists (om s (w - om (invO s) z)).
    apply/affine_parametrisationE; exists (w - om (invO s) z)=> //.
    rewrite (linearB (hom_as_linear (pm p))) /= hw; exact: addrK.
  rewrite isometry_of_mapE (orthogonal_element_unit hO) (linearB (hom_as_linear (om s))) /= his.
  by rewrite addrC subrK.
Qed.

(** Source for [projection_adjoint_continuous]: p* is continuous,
    Federer 1.7.6, p. 33. Supporting lemma. *)
Lemma projection_adjoint_continuous : continuous (pstar : Ek -> E).
Proof.
move=> y; apply: (@continuous_comp Ek (Hkn * Ek)%type E (fun y : Ek => ((hom_of_linear pstar : Hkn), y))
  (fun q : Hkn * Ek => ((q.1 : Hom Vk Vn) q.2 : E))).
  by apply: topological_pair_continuous; [exact: cst_continuous|move=> ?].
exact: (@hom_evaluation_continuous R Vk Vn Bk Bn hBk hBn k _ hbk).
Qed.

(** Source for [projection_map_continuous]: p is continuous, Federer
    1.7.6, p. 33. Supporting lemma. *)
Lemma projection_map_continuous : continuous (pm p : E -> Ek).
Proof.
pose Hnk := inner_metric_space (hom_inner_productP hBn hBk hbn).
move=> v; apply: (@continuous_comp E (Hnk * E)%type Ek (fun v : E => ((pm p : Hnk), v))
  (fun q : Hnk * E => ((q.1 : Hom Vn Vk) q.2 : Ek))).
  by apply: topological_pair_continuous; [exact: cst_continuous|move=> ?].
exact: (@hom_evaluation_continuous R Vn Vk Bn Bk hBn hBk n _ hbn).
Qed.

(** Source for [orthogonal_evaluation_continuous]: (s, v) |-> s(v) is
    continuous on O(n) x R^n, Federer 2.7.16, pp. 134 and 140.
    Supporting lemma. *)
Lemma orthogonal_evaluation_continuous : continuous (fun q : O * E => (om q.1 q.2 : E)).
Proof.
apply: (@hom_evaluation_continuous_comp R Vn Bn hBn n _ hbn (O * E)%type (fun q : O * E => (om q.1 : HVV))
  (fun q : O * E => q.2)); last exact: second_projection_continuous.
move=> q; apply: (@continuous_comp (O * E)%type O HVV (@fst O E) (fun s : O => (om s : HVV)) q).
  exact: first_projection_continuous.
exact: orthogonal_element_continuous.
Qed.

(** Source for [affine_parametrisation_continuous]: "xi is continuous",
    Federer 2.7.16, p. 141. Direct formalisation: dir xi(s, y) =
    s[ker p] and nearest xi(s, y) = s(p*(y)) depend continuously on
    (s, y). *)
Theorem affine_parametrisation_continuous : continuous xi.
Proof.
have hGr := grassmann_space_homogeneous hBm hbm hO.
apply: affine_subspace_continuous_into.
- have -> : (fun q : O * Ek => (affine_direction (xi q) : GR)) =
      (orbit_map gact (projection_kernel hmn p : GR)) \o (@fst O Ek).
    by apply: funext=> -[s y]; rewrite affine_parametrisation_direction.
  move=> q; apply: continuous_comp; first exact: first_projection_continuous.
  exact: (orbit_map_continuous hGr).
- have -> : (fun q : O * Ek => (nearest (xi q) : E)) =
      (fun q : O * E => (om q.1 q.2 : E)) \o (fun q : O * Ek => (q.1, (pstar q.2 : E))).
    by apply: funext=> -[s y]; rewrite affine_parametrisation_nearest.
  move=> q; apply: continuous_comp; last exact: orthogonal_evaluation_continuous.
  apply: (@topological_pair_continuous (O * Ek)%type O E); first exact: first_projection_continuous.
  move=> r; apply: (@continuous_comp (O * Ek)%type Ek E (@snd O Ek) (pstar : Ek -> E) r).
    exact: second_projection_continuous.
  exact: projection_adjoint_continuous.
Qed.

(** Source for [rotation_shear]: the map (s, v) |-> tau_{s(v)} o s of
    O(n) x R^n onto G, a homeomorphism, supporting "xi is open",
    Federer 2.7.16, p. 141. Definition. *)
Definition rotation_shear (q : O * E) : G := isometry_of q.1 (om q.1 q.2).

(** Source for [rotation_shear_open]: (s, v) |-> tau_{s(v)} o s is an
    open map, being the composite of the homeomorphism
    (s, v) |-> (s, s(v)) of O(n) x R^n, with inverse
    (s, w) |-> (s, s^{-1}(w)), and the homeomorphism (s, z) |-> tau_z o s
    of O(n) x R^n onto G (IsometryGroupStructure.v). Supporting lemma
    for Federer 2.7.16, p. 141. *)
Lemma rotation_shear_open : is_open_map rotation_shear.
Proof.
have hOT := lch_group_topological (orthogonal_group_lch hO).
pose psi := fun q : O * E => (q.1, (om q.1 q.2 : E)).
pose psi' := fun q : O * E => (q.1, (om (invO q.1) q.2 : E)).
have hpsi : is_homeomorphism_with_inverse psi psi'.
  split.
  - apply: (@topological_pair_continuous (O * E)%type O E); first exact: first_projection_continuous.
    exact: orthogonal_evaluation_continuous.
  - apply: (@topological_pair_continuous (O * E)%type O E); first exact: first_projection_continuous.
    move=> q; apply: (@continuous_comp (O * E)%type (O * E)%type E (fun q : O * E => (invO q.1, q.2))
      (fun q : O * E => (om q.1 q.2 : E))); last exact: orthogonal_evaluation_continuous.
    apply: (@topological_pair_continuous (O * E)%type O E); last exact: second_projection_continuous.
    move=> r; apply: (@continuous_comp (O * E)%type O O (@fst O E) invO r).
      exact: first_projection_continuous.
    exact: (topological_group_inv_continuous hOT).
  - by move=> [s v]; rewrite /psi /psi' /= (orthogonal_element_inv hO s).1.
  - by move=> [s v]; rewrite /psi /psi' /= (orthogonal_element_inv hO s).2.
have h1 := homeomorphism_with_inverse_open_map hpsi.
have h2 := homeomorphism_with_inverse_open_map (isometry_product_homeomorphism hBn hbn).
move=> U hU; have -> : rotation_shear @` U = (fun q : O * E => isometry_of q.1 q.2) @` (psi @` U).
  apply/seteqP; split=> g.
  - by move=> [q hq <-]; exists (psi q)=> //; exists q.
  - by move=> [_ [q hq <-] <-]; exists q.
exact: h2 _ (h1 _ hU).
Qed.

(** Source for [affine_parametrisation_image]: xi(U) is the image under
    the orbit map of G at ker p of the image under (s, v) |->
    tau_{s(v)} o s of {(s, v) : (s, p(v)) in U}, Federer 2.7.16,
    p. 141. Supporting lemma. *)
Lemma affine_parametrisation_image (U : set (O * Ek)) :
  xi @` U = orbit_map Aact (fibre p 0) @` (rotation_shear @` ((fun q : O * E => (q.1, (pm p q.2 : Ek))) @^-1` U)).
Proof.
apply/seteqP; split=> S.
- move=> [[s y] hq <-]; exists (rotation_shear (s, (pstar y : E))).
    exists (s, (pstar y : E)); last by [].
    by change (U (s, pm p (pstar y))); rewrite projection_adjointK.
  rewrite /orbit_map /rotation_shear; change (Aact (isometry_of s (om s (pstar y))) (fibre p 0) = xi (s, y)).
  by rewrite affine_rotated_translate projection_adjointK.
- move=> [_ [[s v] hq <-] <-]; exists (s, (pm p v : Ek)); first exact: hq.
  rewrite /orbit_map /rotation_shear; change (xi (s, pm p v) = Aact (isometry_of s (om s v)) (fibre p 0)).
  by rewrite affine_rotated_translate.
Qed.

(** Source for [affine_parametrisation_open]: "xi is ... open", Federer
    2.7.16, p. 141. Direct formalisation, by
    affine_parametrisation_image, the continuity of (s, v) |-> (s, p(v)),
    rotation_shear_open and the openness of the orbit maps of G on X. *)
Theorem affine_parametrisation_open : is_open_map xi.
Proof.
move=> U hU; rewrite affine_parametrisation_image.
apply: (homogeneous_orbit_open hXA); apply: rotation_shear_open.
apply: open_comp hU=> q _.
apply: (@topological_pair_continuous (O * E)%type O Ek); first exact: first_projection_continuous.
move=> r; apply: (@continuous_comp (O * E)%type E Ek (@snd O E) (pm p : E -> Ek) r).
  exact: second_projection_continuous.
exact: projection_map_continuous.
Qed.

(** Source for [affine_parametrisation_onto]: "im xi = X", Federer
    2.7.16, p. 141. Direct formalisation: by the transitivity of G on X,
    S = (tau_z o s)[ker p] for some s, z, and this is
    xi(s, p(s^{-1}(z))). *)
Theorem affine_parametrisation_onto (S : X) : exists q, xi q = S.
Proof.
have [g <-] := affine_subspace_action_transitive (fibre p 0) S.
exists (isometry_linear g, (pm p (om (invO (isometry_linear g)) (isometry_translation g)) : Ek)).
rewrite -affine_rotated_translate (orthogonal_element_inv hO _).2.
by rewrite isometry_ofK.
Qed.

(** Source for [affine_parametrisation_proper]: "xi is proper", Federer
    2.7.16, p. 141. Direct formalisation: for compact C contained in X,
    delta is bounded on C by some r (delta is continuous), so
    xi^{-1}(C) is a closed subset of the compact set
    O(n) x {y : |y| <= r}, because delta(xi(s, y)) = |y|. *)
Theorem affine_parametrisation_proper : is_proper_map xi.
Proof.
move=> C hC.
have hdc : compact ((fun S : X => (delta S : R)) @` C).
  apply: continuous_compact hC; apply: continuous_subspaceT.
  exact: affine_origin_distance_continuous.
have [M [_ hM]] := @compact_bounded R R^o _ hdc.
pose r := `|M| + 1.
have hMr : M < r by apply: le_lt_trans (ler_norm M) _; rewrite ltrDl ltr01.
apply: (@subclosed_compact _ _ ([set: O] `*` [set y : Ek | `|y - 0| <= r])).
- apply: preimage_closed.
    by move=> q _; exact: affine_parametrisation_continuous.
  by apply: compact_closed hC; exact: affine_subspace_space_hausdorff.
- by apply: compact_setX=> //; exact: (@euclidean_closed_ball_compact R k).
- move=> [s y] hq; split=> //=; rewrite subr0.
  have hd := hM _ hMr (delta (xi (s, y))) (ex_intro2 _ _ (xi (s, y)) hq erefl).
  apply: le_trans hd; rewrite affine_parametrisation_distance; exact: ler_norm.
Qed.

(** Source for [affine_parametrisation_fibre]: "s[p^{-1}{y}] =
    (p s^{-1})^{-1}{y} for s in O(n), y in R^{n-m}", Federer 2.7.16,
    p. 141: xi(s, y) is the fibre over y of the point p o s^{-1} of
    O*(n, n - m). Direct formalisation; the printed "y in R^n" is read
    as y in R^{n-m}. *)
Theorem affine_parametrisation_fibre (s : O) (y : Ek) :
  xi (s, y) = fibre (orthogonal_projection_action hBk hBn hbn hO s p) y.
Proof.
have [hsi his] := orthogonal_element_inv hO s.
apply: affine_subspace_ext=> x; split.
- move=> /affine_parametrisationE [w hw <-]; apply/projection_fibreE.
  by rewrite orthogonal_projection_actionE hsi.
- move=> /projection_fibreE; rewrite orthogonal_projection_actionE=> hx.
  by apply/affine_parametrisationE; exists (om (invO s) x); [exact: hx|exact: his].
Qed.

End Parametrisation.

Arguments affine_parametrisation {R n m} hmn p q.
