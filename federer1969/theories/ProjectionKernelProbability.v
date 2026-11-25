(** Supporting Federer (1969), 2.10.46, p. 204: the exceptional projections
    annihilating a prescribed nonzero vector have theta-star measure zero.
    Freilich (1950), Lemmas 4.1–4.4, pp. 238–240, uses spherical measure for
    this step. Here the already proved Lebesgue kernel-incidence Fubini
    result is combined with orthogonal invariance and normalization of a
    nonzero vector. This avoids a new spherical-measure construction or any
    choice of measurable adapted frames. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  Hom InnerProductUP InnerNorm InnerNormalization OrthogonalMaps EuclideanNormalChart CoordinateProjection
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanOrthogonalInvariantMeasures
  OrthogonalProjectionProbabilityUP OrthogonalProjectionProbability OrthogonalGroupTopology
  OrthogonalGroupHaarMeasure OrthogonalInjectionSpaces IsotropyGroupTopology LinearGroupSealed
  TopologicalGroupUP HomogeneousSpaceUP InvariantMeasureTranslates
  EuclideanLebesgueDimensions EuclideanLebesgueHaar EuclideanProjectionKernelNull ProjectionKernelIncidence
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projection_kernel_probability_orthogonal]: supporting
    invariance of the annihilation event in 2.10.46,
    p. 204, by 2.7.16(6), p. 139;
    Freilich (1950), Lemmas 4.1–4.4, pp. 238–240.
    The probability is unchanged by an orthogonal change of
    the prescribed source vector. *)
Lemma projection_kernel_probability_orthogonal (R : realType) n m (hmn : (m<=n)%N)
    (c : {linear R_n R n -> R_n R n}) (x : R_n R n) :
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) c ->
  @orthogonal_projection_probability R n m hmn [set p | euclidean_projection_linear p (c x)=0%R]=
  @orthogonal_projection_probability R n m hmn [set p | euclidean_projection_linear p x=0%R].
Proof.
move=> hc.
have [mulO [invO [eO hO]]] := orthogonal_group_restriction_exists
  (@euclidean_inner_productP R n) (@coordinate_basisP R n).
pose g := orthogonal_element_of (@euclidean_inner_productP R n) (@coordinate_basisP R n) hc.
pose A := orthogonal_projection_action (@euclidean_inner_productP R m)
  (@euclidean_inner_productP R n) (@coordinate_basisP R n) hO.
have hG := topological_group_laws (lch_group_topological (orthogonal_group_lch hO)).
have hA := orthogonal_projections_homogeneous (@euclidean_inner_productP R m) (@coordinate_basisP R m) hO.
have htheta := (@orthogonal_projection_probability_specification R n m hmn) mulO invO eO hO.
have hh := invariant_measure_preimage hG hA htheta.1 g
  [set p | euclidean_projection_linear p (c x)=0%R].
have he : A g @^-1` [set p | euclidean_projection_linear p (c x)=0%R]=
    [set p | euclidean_projection_linear p x=0%R].
  apply/seteqP; split=> p;
    change (orthogonal_projection_map (A g p) (c x)=0%R -> orthogonal_projection_map p x=0%R) ||
    change (orthogonal_projection_map p x=0%R -> orthogonal_projection_map (A g p) (c x)=0%R);
    rewrite /A orthogonal_projection_actionE
    -(@orthogonal_element_ofE R (R_n R n) (@euclidean_inner_product R n)
      (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n) c hc x)
    (orthogonal_element_inv hO g).1; by [].
rewrite he in hh; exact: esym hh.
Qed.

(** Source for [projection_kernel_probability_scale]: supporting
    nonzero scalar invariance of the annihilation event for
    2.10.46, p. 204. This follows from linearity;
    it permits normalization before applying orthogonal invariance. *)
Lemma projection_kernel_probability_scale (R : realType) n m (hmn : (m<=n)%N)
    (r : R) (x : R_n R n) : r!=0%R ->
  @orthogonal_projection_probability R n m hmn [set p | euclidean_projection_linear p (r*:x)=0%R]=
  @orthogonal_projection_probability R n m hmn [set p | euclidean_projection_linear p x=0%R].
Proof.
move=> hr; congr (orthogonal_projection_probability _ _).
apply/seteqP; split=> p hp.
- have he : (euclidean_projection_linear p (r*:x)==0%R) by apply/eqP.
  rewrite linearZ scaler_eq0 (negbTE hr) orFb in he; exact/eqP.
- change (euclidean_projection_linear p (r*:x)=0%R).
  apply/eqP; rewrite linearZ scaler_eq0; apply/orP; right; exact/eqP.
Qed.

(** Source for [projection_kernel_probability_direction]: supporting
    direction-independence of the exceptional probability in
    Freilich (1950), Lemmas 4.1–4.4, pp. 238–240,
    for 2.10.46, p. 204. Normalize the vector,
    then use the sealed prescribed-normal orthogonal chart. *)
Lemma projection_kernel_probability_direction (R : realType) n m (hmn : (m<=n.+1)%N)
    (x : R_n R n.+1) : x!=0%R ->
  @orthogonal_projection_probability R n.+1 m hmn [set p | euclidean_projection_linear p x=0%R]=
  @orthogonal_projection_probability R n.+1 m hmn
    [set p | euclidean_projection_linear p (@coordinate_basis R n.+1 ord0)=0%R].
Proof.
move=> hx.
pose hB := @euclidean_inner_productP R n.+1.
have hu := inner_normalize_square hB hx.
have hc := euclidean_normal_chart_orthogonal ord0 hu.
have hh := @projection_kernel_probability_orthogonal R n.+1 m hmn _
  (@coordinate_basis R n.+1 ord0) hc.
rewrite euclidean_normal_chart_axis in hh.
have hn : inner_norm hB x!=0%R by rewrite inner_norm_eq0.
rewrite -(inner_normalizeK hB hx) (@projection_kernel_probability_scale R n.+1 m hmn (inner_norm hB x) (inner_normalize hB x) hn).
exact hh.
Qed.

(** Source for [nonzero_vector_projection_kernel_probability_null]:
    supporting exceptional-set nullity in Federer 2.10.46,
    p. 204; Freilich (1950), Lemma 4.4,
    p. 240. The direction-independent probability vanishes
    almost everywhere by Fubini, hence at every nonzero
    vector. The positive-dimensional unit cube prevents a
    vacuous almost-everywhere argument. *)
Theorem nonzero_vector_projection_kernel_probability_null (R : realType) n m
    (hmn : (m.+1<=n.+1)%N) (x : R_n R n.+1) : x!=0%R ->
  @orthogonal_projection_probability R n.+1 m.+1 hmn
    [set p | euclidean_projection_linear p x=0%R]=0.
Proof.
move=> hx.
pose X := inner_metric_space (@euclidean_inner_productP R n.+1).
pose Leb := @euclidean_lebesgue_measure R n.+1.
pose hm := euclidean_lebesgue_is_measure R n.+1.
pose theta := @orthogonal_projection_probability R n.+1 m.+1 hmn.
have hae := @projection_kernel_incidence_almost_null R n m theta
  (@theta_star_is_measure R n.+1 m.+1 hmn) (@theta_star_borel_regular R n.+1 m.+1 hmn)
  ltac:(by rewrite /theta theta_star_total ltry).
pose e := @coordinate_basis R n.+1 ord0.
have he : euclidean_inner_product e e= 1%R.
  by rewrite /e euclidean_inner_basis /coordinate_basis ffunE eqxx.
have hzero : Leb [set (0%R : X)]=0.
  apply: (@measure_null_subset R [the choiceType of X] Leb hm _
    [set z : X | euclidean_inner_product z e=0%R]); last exact (@euclidean_unit_normal_hyperplane_null R n.+1 ord0 e he).
  move=> z ->; change (euclidean_inner_product (0%R : R_n R n.+1) e=0%R).
  by rewrite /e euclidean_inner_basis ffunE.
have hnz : measure_almost_everywhere Leb (~` [set (0%R : X)]).
  by rewrite /measure_almost_everywhere setCK.
have hgood := measure_almost_everywhere_and hm hae hnz.
have hex : exists y : X, theta [set p | euclidean_projection_linear p y=0%R]=0 /\ y!=0%R.
  apply: contrapT=> hnone.
  have hempty : [set y : X | theta [set p | euclidean_projection_linear p y=0%R]=0] `&`
      (~` [set (0%R : X)])=set0.
    apply/seteqP; split=> y // [hy hn]; apply: hnone; exists y; split=> //; exact/eqP.
  have hz : Leb setT=0 by move: hgood; rewrite /measure_almost_everywhere hempty setC0.
  have hh := @measure_mono R [the choiceType of X] Leb hm
    [set z : X | forall i, (0<=z i<= 1)%R] setT (subsetT _).
  rewrite /Leb in hz hh.
  by rewrite (euclidean_unit_closed_cube R n.+1).2 hz lee_fin ler10 in hh.
have [y [hy hny]] := hex.
rewrite (projection_kernel_probability_direction hmn hx).
by rewrite -(projection_kernel_probability_direction hmn hny).
Qed.
