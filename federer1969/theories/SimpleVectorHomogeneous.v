(** Federer (1969), 2.7.16, example (4), printed p. 138: "However, the
    action of GL(n, R) on the space of all nonzero simple m vectors of R^n
    admits a |det|^{-m} covariant integral." The application of 2.7.11, p.
    128, requires that this space X be a locally compact Hausdorff
    homogeneous space of GL(n, R) (2.7.1, p. 121); Federer gives no proof.
    Continuity and transitivity are in SimpleVectorAction.v. The orbit maps
    are open: by transport along the action (orbit_open_from_point) it
    suffices that N xi_0 is a neighbourhood of xi_0 for every neighbourhood
    N of 1 and one point xi_0 = u_1 wedge ... wedge u_m with u orthonormal.
    The orthogonal group O(V), a compact group, acts continuously and
    transitively on the simple m-vectors of norm 1 (SimpleVectorFrames.v),
    so its orbit maps there are open (compact_transitive_homogeneous).
    Choose neighbourhoods N_a, N_b of 1 with N_a N_b c N. For zeta near xi_0
    write zeta = r eta with r = |zeta| near 1 and eta = zeta / |zeta| near
    xi_0 among the simple m-vectors of norm 1; then eta = (wedge_m s) xi_0
    with s in O(V) cap N_a, and the map d_r, multiplying u_1 by r and fixing
    the orthogonal complement of u_1, lies in N_b and satisfies (wedge_m
    d_r) xi_0 = r xi_0; hence zeta = (wedge_m (s d_r)) xi_0 with s d_r in N.
    X is then locally compact, being a Hausdorff homogeneous space of a
    locally compact group. The module assumes 0 < m <= n, as in the context
    "0 < m < n" of example (4). *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From mathcomp Require Import fingroup perm.
From Federer Require Import RealMetricBackground InnerProductUP InnerProductLaws InnerNorm InnerNormInequalities
  InnerMetric InnerNormedTopology LinearBasis Bilinear TensorUP Hom HomInner FiniteDualDimension
  CoefficientCoordinates ModuleQuotient SubspaceCarrier GrassmannSubspaces ExteriorGrading ExteriorAlgebra
  ExteriorMaps FiniteExteriorPowers ExteriorMapScaling InnerExterior InnerExteriorProducts
  InnerExteriorPositivity ExteriorAdjointConsequences AssociatedSubspace SimpleElementary
  OrthonormalFamilies OrthonormalisationUP GramSchmidt OrthogonalMaps IsotropyGroupTopology
  SubtypeCompactHausdorff TopologicalProductMaps TopologicalGroupUP TopologicalGroupLaws HomeomorphismUP
  HomogeneousSpaceUP HomogeneousSpaceLaws HomSpaceTopology LinearGroupTopology LinearGroupSealed
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure CompactGroupHomogeneousMeasures SpecialLinearCommutators
  EuclideanLinearMaps AffineGroupTopology SubgroupOrbitOpen SimpleVectorAction SimpleVectorFrames.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section OrbitOpenFromPoint.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X).
Hypothesis hT : is_topological_group mul inv e.
Hypothesis hAc : continuous (fun p : G * X => A p.1 p.2).
Hypothesis hAm : forall g h x, A (mul g h) x = A g (A h x).
Hypothesis hAe : forall x, A e x = x.
Hypothesis hAt : forall x y, exists g, A g x = y.
Variable x0 : X.
Hypothesis hx0 : forall N : set G, nbhs e N -> nbhs x0 (orbit_map A x0 @` N).

(** Source for [orbit_open_from_point]: "for each x in X the map A^x
    ... is open", Federer 2.7.1, p. 121, for a continuous transitive
    action, from the local openness of one orbit map at e: if
    A(h, x_0) = x, g in U and k = g h, then
    A^x(U) contains A_k(A^{x_0}(N)) for the neighbourhood
    N = {a : k a h^{-1} in U} of e, and A_k is a homeomorphism.
    Supporting lemma for 2.7.16, p. 138. *)
Lemma orbit_open_from_point x : is_open_map (orbit_map A x).
Proof.
have hgl := topological_group_laws hT.
move=> U hU; rewrite openE=> y [g hg <-]; rewrite /interior.
have [h hh] := hAt x0 x.
pose k := mul g h.
pose F := fun a : G => mul (mul k a) (inv h).
have hF : continuous F.
  move=> a; apply: (@continuous_comp G G G (mul k) (fun z => mul z (inv h))).
    exact: (left_translation_continuous hT k).
  exact: (right_translation_continuous hT (inv h)).
have hFe : F e = g by rewrite /F (group_mulg1 hgl) /k (group_mulgK hgl).
have hN : nbhs e (F @^-1` U) by apply: hF; rewrite hFe; exact: open_nbhs_nbhs.
have hS := hx0 hN.
have hAk : continuous (fun z => A (inv k) z).
  move=> z; apply: (@continuous_comp X (G * X)%type X (fun z => (inv k, z)) (fun p : G * X => A p.1 p.2)).
    by apply: topological_pair_continuous; [exact: cst_continuous|move=> ?].
  exact: hAc.
have hy : A (inv k) (A g x) = x0 by rewrite -hh -!hAm /k -(group_mulA hgl) (group_mulVg hgl) hAe.
have hpre : nbhs (A g x) ((fun z => A (inv k) z) @^-1` (orbit_map A x0 @` (F @^-1` U))).
  by apply: hAk; rewrite hy.
apply: (@filterS _ _ (nbhs_filter _) _ _ _ hpre)=> z [a ha hza].
rewrite /orbit_map in hza.
exists (F a)=> //; rewrite /orbit_map /F !hAm.
have -> : A (inv h) x = x0 by rewrite -hh -hAm (group_mulVg hgl) hAe.
rewrite hza -!hAm /k (group_mulgV hgl) hAe.
by [].
Qed.

End OrbitOpenFromPoint.

Section SimpleHomogeneous.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable m : nat.
Hypothesis hm : (0 < m)%N.
Hypothesis hmn : (m <= n)%N.
Local Notation h2 := (euclidean_two_nonzero R).
Local Notation HVV := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation L := (inner_metric_space (exterior_inner_productP h2 hB m)).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation mul := (linear_group_mul hB hb).
Local Notation inv := (linear_group_inv hB hb).
Local Notation unit := (linear_group_unit hB hb).
Local Notation hG := (linear_group_operations hB hb).
Local Notation onorm := (hom_operator_norm hB hB hb).
Local Notation X := (set_type (nonzero_simple_set hB m)).
Local Notation gw := (exterior_group_map hB hb m).
Local Notation A := (simple_vector_action hB hb m).
Local Notation O := (orthogonal_group hB hb).
Local Notation om := (@orthogonal_element_map R V B hB n b hb).

(** Source for [hgl]: the group laws of GL(V), used in this section. *)
Let hgl := linear_group_group_laws hG.
(** Source for [hGT]: GL(V) is a topological group, used in this
    section. *)
Let hGT := lch_group_topological (linear_group_operations_lch hB hb).

(** Source for [unit_simple_set]: the simple m-vectors of norm 1,
    Federer 1.6.1, p. 23, and 1.7.5, p. 32, supporting 2.7.16, p. 138.
    Definition. *)
Definition unit_simple_set : set L := [set x : L | `|x| = 1 /\ simple x].

Local Notation S1 := (set_type unit_simple_set).

(** Source for [exterior_orthogonal_norm]: |(wedge_m s) xi| = |xi| for s
    in O(n), Federer 1.7.5, p. 32 (exterior_power_orthogonal).
    Supporting lemma. *)
Lemma exterior_orthogonal_norm (s : O) (x : L) : `|(gw (set_val s) x : L)| = `|x|.
Proof.
have ho := exterior_power_orthogonal h2 hB hB (orthogonal_element_orthogonal s) (m := m).
rewrite !inner_norm_topologyE; apply: inner_norm_value; first exact: inner_norm_nonnegative.
by rewrite inner_norm_sqr; symmetry; exact: (ho x x).
Qed.

(** Source for [unit_simple_mem]: (wedge_m s) xi is a simple m-vector of
    norm 1 when xi is and s in O(n), Federer 2.7.16, p. 138. Supporting
    lemma. *)
Lemma unit_simple_mem (s : O) (x : S1) : unit_simple_set (gw (set_val s) (set_val x)).
Proof.
have [h1 h2'] := set_valP x; split; first by rewrite exterior_orthogonal_norm.
exact: exterior_group_map_simple.
Qed.

(** Source for [unit_simple_action]: the action of O(n) on the simple
    m-vectors of norm 1 by wedge_m, Federer 2.7.16, pp. 138–139.
    Definition. *)
Definition unit_simple_action (s : O) (x : S1) : S1 := exist _ (gw (set_val s) (set_val x)) (mem_set (unit_simple_mem s x)).

Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction mul inv unit O mulO invO eO.

(** Source for [hOT]: O(n) is a topological group, used in this
    section. *)
Let hOT : is_topological_group mulO invO eO := lch_group_topological (orthogonal_group_lch hO).

(** Source for [unit_simple_action_continuous]: the action of O(n) on
    the simple m-vectors of norm 1 is continuous, Federer 2.7.1,
    p. 121. Supporting lemma. *)
Lemma unit_simple_action_continuous : continuous (fun q : O * S1 => unit_simple_action q.1 q.2).
Proof.
apply: set_type_continuous_into=> q.
have hp : continuous (fun q : O * S1 => (set_val q.1, (set_val q.2 : L))).
  apply: (@topological_pair_continuous (O * S1)%type GL L).
  - move=> r; apply: (@continuous_comp (O * S1)%type O GL (@fst O S1) set_val r).
      exact: first_projection_continuous.
    exact: set_type_val_continuous.
  - move=> r; apply: (@continuous_comp (O * S1)%type S1 L (@snd O S1) set_val r).
      exact: second_projection_continuous.
    exact: set_type_val_continuous.
have hq : {for (set_val q.1, (set_val q.2 : L)), continuous (fun r : GL * L => (gw r.1 r.2 : L))}.
  exact: (@exterior_action_continuous_at R V B hB n b hb m (set_val q.1) (set_val q.2) (set_valP q.2).2).
exact: (@continuous_comp (O * S1)%type (GL * L)%type L (fun q : O * S1 => (set_val q.1, (set_val q.2 : L)))
  (fun r : GL * L => (gw r.1 r.2 : L)) q (hp q) hq).
Qed.

(** Source for [unit_simple_action_compatible]: A(st, xi) =
    A(s, A(t, xi)), Federer 2.7.1, p. 121. Supporting lemma. *)
Lemma unit_simple_action_compatible (s t : O) (x : S1) :
  unit_simple_action (mulO s t) x = unit_simple_action s (unit_simple_action t x).
Proof.
apply: val_inj.
change (gw (set_val (mulO s t)) (set_val x) = gw (set_val s) (gw (set_val t) (set_val x))).
by rewrite (subgroup_restriction_mul hO) exterior_group_map_mul.
Qed.

(** Source for [unit_simple_action_transitive]: O(n) acts transitively
    on the simple m-vectors of norm 1, Federer 1.7.2, p. 28, and 2.7.16,
    p. 138: both are products of orthonormal families
    (unit_simple_frame), which correspond under an orthogonal map
    (orthonormal_frames_orthogonal). Supporting lemma. *)
Lemma unit_simple_action_transitive (x y : S1) : exists s, unit_simple_action s x = y.
Proof.
have [hx1 hxs] := set_valP x; have [hy1 hys] := set_valP y.
have [u [hu hxu]] := unit_simple_frame hm hx1 hxs.
have [u' [hu' hyu]] := unit_simple_frame hm hy1 hys.
have [s [hs hsu]] := orthonormal_frames_orthogonal hB hb hu hu'.
exists (orthogonal_element_of hB hb hs); apply: val_inj.
change (gw (set_val (orthogonal_element_of hB hb hs)) (set_val x) = set_val y).
rewrite !set_valE hxu hyu exterior_group_map_word /word_image.
apply: (congr1 (fun e : 'I_m -> V => e_lambda e (ord_tuple m))).
by apply: funext=> i; rewrite -hsu.
Qed.

(** Source for [unit_simple_space_hausdorff]: the simple m-vectors of
    norm 1 form a Hausdorff space, Federer 2.7.1, p. 121. Supporting
    lemma. *)
Lemma unit_simple_space_hausdorff : hausdorff_space S1.
Proof.
apply: set_type_hausdorff.
exact: (@inner_space_hausdorff R (exterior_power V m) _ (exterior_inner_productP h2 hB m)).
Qed.

(** Source for [unit_simple_homogeneous]: the simple m-vectors of norm
    1 form a homogeneous space of the compact group O(n), Federer 2.7.1,
    p. 121, and 2.7.16, p. 139 (compact_transitive_homogeneous).
    Supporting theorem. *)
Theorem unit_simple_homogeneous : is_homogeneous_space mulO unit_simple_action.
Proof.
apply: (compact_transitive_homogeneous hOT (@orthogonal_group_compact_space R V B hB n b hb)
  unit_simple_space_hausdorff unit_simple_action_continuous unit_simple_action_compatible).
exact: unit_simple_action_transitive.
Qed.

End SimpleHomogeneous.

Arguments unit_simple_set {R V B} hB m x.
Arguments unit_simple_action {R V B} hB {n b} hb m s x.

Section SimpleOpenness.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable m : nat.
Hypothesis hm : (0 < m)%N.
Hypothesis hmn : (m <= n)%N.
Local Notation h2 := (euclidean_two_nonzero R).
Local Notation HVV := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation L := (inner_metric_space (exterior_inner_productP h2 hB m)).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation mul := (linear_group_mul hB hb).
Local Notation inv := (linear_group_inv hB hb).
Local Notation unit := (linear_group_unit hB hb).
Local Notation hG := (linear_group_operations hB hb).
Local Notation onorm := (hom_operator_norm hB hB hb).
Local Notation X := (set_type (nonzero_simple_set hB m)).
Local Notation gw := (exterior_group_map hB hb m).
Local Notation A := (simple_vector_action hB hb m).
Local Notation O := (orthogonal_group hB hb).
Local Notation S1 := (set_type (unit_simple_set hB m)).
Local Notation N := (inner_norm hB).

(** Source for [hgl]: the group laws of GL(V), used in this section. *)
Let hgl := linear_group_group_laws hG.
(** Source for [hGT]: GL(V) is a topological group, used in this
    section. *)
Let hGT := lch_group_topological (linear_group_operations_lch hB hb).

(** Source for [simple_vector_action_unit]: A(1, xi) = xi, Federer
    2.7.1, p. 121. Supporting lemma. *)
Lemma simple_vector_action_unit (x : X) : A unit x = x.
Proof. by apply: val_inj; exact: exterior_group_map_unit. Qed.

(** Source for [normalise_mem]: xi / |xi| is a simple m-vector of norm
    1 for a nonzero simple m-vector xi, Federer 1.6.1, p. 23, and 1.7.5,
    p. 32. Supporting lemma for 2.7.16, p. 138. *)
Lemma normalise_mem (x : X) : unit_simple_set hB m (`|set_val x|^-1 *: (set_val x : L)).
Proof.
have [hx0 hxs] := set_valP x.
have hn : `|(set_val x : L)| != 0 by rewrite normr_eq0.
split; last exact: simple_scale hm hxs.
by rewrite normrZ normrV ?unitfE // normr_id mulVf.
Qed.

(** Source for [normalise]: the map xi |-> xi / |xi| of the nonzero
    simple m-vectors onto those of norm 1, Federer 2.7.16, p. 138.
    Definition. *)
Definition normalise (x : X) : S1 := exist _ (`|set_val x|^-1 *: (set_val x : L)) (mem_set (normalise_mem x)).

(** Source for [simple_norm_continuous]: xi |-> |xi| is continuous on
    the nonzero simple m-vectors, Federer 1.7.5, p. 32. Supporting
    lemma. *)
Lemma simple_norm_continuous : continuous (fun x : X => `|(set_val x : L)|).
Proof.
move=> x; apply: (@continuous_comp X L R (set_val : X -> L) Num.norm).
  exact: set_type_val_continuous.
exact: norm_continuous.
Qed.

(** Source for [normalise_continuous]: xi |-> xi / |xi| is continuous,
    Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma normalise_continuous : continuous normalise.
Proof.
apply: set_type_continuous_into=> x.
have hn : `|(set_val x : L)| != 0 by rewrite normr_eq0; exact: (set_valP x).1.
apply: (@continuousZ R L X (fun y : X => `|(set_val y : L)|^-1) (fun y : X => (set_val y : L)) x).
  by apply: continuousV=> //; exact: simple_norm_continuous.
exact: set_type_val_continuous.
Qed.

Section Frame.
Variable u : 'I_m -> V.
Hypothesis hu : orthonormal_family B u.

(** Source for [frame_point_mem]: u_1 wedge ... wedge u_m is a nonzero
    simple m-vector of norm 1, Federer 1.6.1, p. 23, and 1.7.5, p. 32.
    Supporting lemma. *)
Lemma frame_point_mem : `|(e_lambda u (ord_tuple m) : L)| = 1 /\ simple (e_lambda u (ord_tuple m)).
Proof. by split; [exact: orthonormal_word_norm|exact: product_simple]. Qed.

(** Source for [frame_point]: the base point u_1 wedge ... wedge u_m of
    the space of nonzero simple m-vectors, Federer 2.7.16, p. 138.
    Definition. *)
Definition frame_point : X.
Proof.
apply: (exist _ (e_lambda u (ord_tuple m) : L)); apply: mem_set; split; last exact: frame_point_mem.2.
by apply/eqP=> h0; have := frame_point_mem.1; rewrite h0 normr0=> /esym/eqP; rewrite oner_eq0.
Defined.

(** Source for [frame_unit_point]: u_1 wedge ... wedge u_m as a simple
    m-vector of norm 1, Federer 2.7.16, p. 138. Definition. *)
Definition frame_unit_point : S1 := exist _ (e_lambda u (ord_tuple m) : L) (mem_set frame_point_mem).

Local Notation i0 := (Ordinal hm).

(** Source for [frame_dilation_functional]: x |-> (r - 1) (x . u_1),
    Federer 2.7.16, p. 138. Definition. *)
Definition frame_dilation_functional (r : R) : Hom V R^o := (r - 1) *: hom_of_linear (inner_coordinate hB (u i0)).

(** Source for [frame_dilation_functionalE]: the values (r - 1)
    (x . u_1), Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma frame_dilation_functionalE r x : (frame_dilation_functional r x : R) = (r - 1) * B x (u i0).
Proof. by rewrite hom_scaleE hom_of_linearE inner_coordinateE. Qed.

(** Source for [frame_dilation_injective]: the map d_r multiplying u_1
    by r and fixing the orthogonal complement of u_1 is univalent for
    r <> 0, Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma frame_dilation_injective (r : R) : r != 0 ->
  injective (rank_one_shift (frame_dilation_functional r) (u i0)).
Proof.
move=> hr; apply: rank_one_shift_injective.
by rewrite frame_dilation_functionalE hu eqxx mulr1 subrK.
Qed.

(** Source for [frame_dilation]: d_r as a member of GL(n, R), Federer
    2.7.16, p. 138. Definition. *)
Definition frame_dilation (r : R) (hr : r != 0) : GL :=
  exist _ (rank_one_shift (frame_dilation_functional r) (u i0) : HVV) (mem_set (frame_dilation_injective hr)).

(** Source for [frame_dilation_point]: (wedge_m d_r)(u_1 wedge ... wedge
    u_m) = r u_1 wedge ... wedge u_m, Federer 1.3.4, p. 16
    (word_diagonal_scale). Supporting lemma. *)
Lemma frame_dilation_point (r : R) (hr : r != 0) :
  gw (frame_dilation hr) (e_lambda u (ord_tuple m)) = r *: e_lambda u (ord_tuple m).
Proof.
pose d := fun i : 'I_m => if i == i0 then r else 1.
rewrite exterior_group_map_word /word_image.
have -> : (fun i => (set_val (frame_dilation hr) : Hom V V) (u i)) = (fun i => d i *: u i).
  apply: funext=> i.
  change (rank_one_shift (frame_dilation_functional r) (u i0) (u i) = d i *: u i).
  rewrite rank_one_shiftE frame_dilation_functionalE hu /d.
  case: (eqVneq i i0)=> [->|hi]; first by rewrite mulr1 -{1}[u i0]scale1r -scalerDl addrC subrK.
  by rewrite mulr0 scale0r addr0 scale1r.
rewrite word_diagonal_scale; congr (_ *: _).
by rewrite (bigD1 i0) //= big1 ?mulr1 /d ?eqxx // => i hi; rewrite (negbTE hi).
Qed.

(** Source for [frame_dilation_close]: ||d_r - 1|| <= |r - 1|, Federer
    1.7.6, p. 33, and Cauchy's inequality, 1.7.1, p. 28. Supporting
    lemma. *)
Lemma frame_dilation_close (r : R) (hr : r != 0) :
  onorm (set_val (frame_dilation hr) - set_val unit) <= `|r - 1|.
Proof.
apply: hom_operator_norm_least; first exact: normr_ge0.
move=> x.
have -> : ((set_val (frame_dilation hr) - set_val unit : HVV) : Hom V V) x =
    (frame_dilation_functional r x : R) *: u i0.
  change ((rank_one_shift (frame_dilation_functional r) (u i0)) x - (set_val unit : Hom V V) x =
    (frame_dilation_functional r x : R) *: u i0).
  by rewrite rank_one_shiftE (linear_group_unitE hG) hom_identityE addrC addKr.
rewrite inner_normZ frame_dilation_functionalE normrM.
have hu1 : N (u i0) = 1.
  apply: inner_norm_value; first exact: ler01.
  by rewrite hu eqxx expr1n.
rewrite hu1 mulr1 ler_wpM2l ?normr_ge0 //.
apply: le_trans (inner_cauchy hB x (u i0)) _.
by rewrite hu1 mulr1.
Qed.

Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction mul inv unit O mulO invO eO.

(** Source for [frame_orbit_nbhs]: N xi_0 is a neighbourhood of
    xi_0 = u_1 wedge ... wedge u_m for every neighbourhood N of 1 in
    GL(n, R), Federer 2.7.1, p. 121, for 2.7.16, p. 138. Supporting
    lemma: with N_a N_b c N, zeta = |zeta| (wedge_m s) xi_0 with s in
    O(n) cap N_a and d_{|zeta|} in N_b. *)
Lemma frame_orbit_nbhs (Nn : set GL) : nbhs unit Nn -> nbhs frame_point (orbit_map A frame_point @` Nn).
Proof.
move=> hN.
have hmc := topological_group_mul_continuous hGT.
have hN' : nbhs (mul unit unit) Nn by rewrite (group_mul1g hgl).
have [[Na Nb] [hNa hNb] hNab] := hmc (unit, unit) Nn hN'.
have [eps heps hball] : exists2 eps : R, 0 < eps &
    forall g : GL, onorm (set_val g - set_val unit) < eps -> Nb g.
  move: hNb; rewrite (@nbhsE GL)=> -[W [[O' hO' <-] hWu] hWNb].
  have hO'u : nbhs (set_val unit : HVV) O' by apply: open_nbhs_nbhs; split.
  have [r hr hrO] := (hom_space_nbhs_operator (set_val unit : HVV) O').1 hO'u.
  by exists r=> // g hg; apply: hWNb; apply: hrO.
have hNO : nbhs eO [set s : O | Na (set_val s)].
  apply: (@set_type_val_continuous GL O eO).
  by rewrite (subgroup_restriction_unit hO).
pose M := orbit_map (unit_simple_action hB hb m) frame_unit_point @` (interior [set s : O | Na (set_val s)]).
have hMo : open M.
  rewrite /M; apply: (homogeneous_orbit_open (unit_simple_homogeneous hm hO) frame_unit_point).
  exact: open_interior.
have hM0 : M frame_unit_point.
  exists eO; first exact: hNO.
  apply: val_inj; rewrite /= (subgroup_restriction_unit hO).
  exact: exterior_group_map_unit.
have hnf : normalise frame_point = frame_unit_point.
  apply: val_inj; rewrite /= frame_point_mem.1 invr1.
  exact: scale1r.
have hZ1 : nbhs frame_point (normalise @^-1` M).
  by apply: normalise_continuous; rewrite hnf; apply: open_nbhs_nbhs.
have hZ2 : nbhs frame_point [set x : X | Num.norm (`|(set_val x : L)| - 1) < eps].
  have hsn := simple_norm_continuous.
  have := (proj1 (@cvgrPdist_lt _ R^o _ (nbhs frame_point) (nbhs_filter frame_point)
    (fun x : X => (`|(set_val x : L)| : R^o)) (`|(set_val frame_point : L)| : R^o)))
    (hsn frame_point) eps heps.
  have h1 : `|(set_val frame_point : L)| = 1 := frame_point_mem.1.
  apply: filterS=> x hx /=.
  by move: hx; rewrite h1 distrC.
apply: (@filterS _ _ (nbhs_filter _) _ _ _ (filterI hZ1 hZ2))=> x [[s hs hsx] hx2].
pose r := `|(set_val x : L)|.
have hr : r != 0 by rewrite normr_eq0; exact: (set_valP x).1.
pose g := mul (set_val s) (frame_dilation hr).
have hgN : Nn g.
  apply: (hNab (set_val s, frame_dilation hr)); split; first exact: interior_subset hs.
  by apply: hball; apply: le_lt_trans (frame_dilation_close hr) _.
exists g=> //; apply: val_inj.
have hsx' : gw (set_val s) (e_lambda u (ord_tuple m)) = r^-1 *: (set_val x : L).
  exact: (congr1 set_val hsx).
change (gw g (e_lambda u (ord_tuple m)) = set_val x).
rewrite exterior_group_map_mul frame_dilation_point linearZ_LR hsx' scalerA mulfV //.
exact: scale1r.
Qed.

End Frame.

(** Source for [simple_vector_homogeneous]: the space of nonzero simple
    m-vectors of V is a homogeneous space of GL(V) through
    A(g, xi) = (wedge_m g) xi, Federer 2.7.1, p. 121, as presupposed in
    2.7.16, p. 138, for 0 < m <= n. Direct formalisation; Federer gives
    no proof. *)
Theorem simple_vector_homogeneous : is_homogeneous_space mul A.
Proof.
have [o [ho hgs]] := orthonormal_basis_exists hB hb.
have hoo := orthonormalisation_orthonormal hgs.
pose u := fun i : 'I_m => o (widen_ord hmn i).
have hu : orthonormal_family B u.
  have hinj : injective (widen_ord hmn) by move=> i j /(congr1 val) /= hij; exact: val_inj.
  by move=> i j; rewrite /u hoo (inj_eq hinj).
have [mulO [invO [eO hO]]] := orthogonal_group_restriction_exists hB hb.
split.
- exact: simple_vector_action_continuous.
- exact: simple_vector_action_compatible.
- apply: (orbit_open_from_point hGT (@simple_vector_action_continuous R V B hB n b hb m)
    (@simple_vector_action_compatible R V B hB n b hb m) simple_vector_action_unit
    (@simple_vector_action_transitive R V B hB n b hb m) (x0 := frame_point hu)).
  exact: (frame_orbit_nbhs hu hO).
- move=> x; apply/seteqP; split=> // y _.
  have [g hg] := @simple_vector_action_transitive R V B hB n b hb m x y.
  by exists g.
Qed.

(** Source for [simple_vector_space_locally_compact]: the space of
    nonzero simple m-vectors is a locally compact Hausdorff space, the
    standing hypothesis of Federer 2.7.1, p. 121, for 2.7.16, p. 138.
    Supporting lemma. *)
Lemma simple_vector_space_locally_compact : hausdorff_space X /\ locally_compact [set: X].
Proof.
have hH : hausdorff_space X by exact: simple_vector_space_hausdorff.
split=> //.
exact: (homogeneous_space_locally_compact (linear_group_operations_lch hB hb) simple_vector_homogeneous hH).
Qed.

End SimpleOpenness.
