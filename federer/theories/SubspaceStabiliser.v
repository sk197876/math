(** Federer (1969), 2.7.16, example (3), printed p. 137: "Suppose W c V are
    vectorspaces with 0 < dim W = m < dim V = n < oo, and G is the group of
    those linear automorphisms of V which map W onto W." Here V carries an
    inner product and a finite base, so that its linear group GL(V) is the
    locally compact Hausdorff group of LinearGroupTopology.v with the sealed
    operations of LinearGroupSealed.v; W is a subspace of V
    (ModuleQuotient.v) with a base of m members (grassmann_pred of
    GrassmannSubspaces.v). The group G is the subset subspace_stabiliser of
    GL(V), defined by "g maps W onto W" (maps_subspace_onto: W = g[W]). It
    is a closed subgroup (subspace_stabiliser_subgroup,
    subspace_stabiliser_closed), hence, with the relative topology and any
    restricted group structure (is_subgroup_restriction of
    IsotropyGroupTopology.v), a locally compact Hausdorff topological group
    (subspace_stabiliser_lch). The closedness uses a base of V adapted to W:
    e_1, ..., e_m form a base of W and e_1, ..., e_n one of V
    (adapted_basis_exists, by the extension of 1.6.1, p. 23), so that W is
    the set of common zeros of the dual functionals e_j* with j > m
    (adapted_subspaceE), and a univalent g with g[W] c W maps W onto W, W
    being finite dimensional. For g in G the restriction g|W is
    invariant_restriction of InvariantRestriction.v, and det(g|W) is its
    determinant (1.3.4, p. 16) with respect to any base of W
    (stabiliser_restriction_det, stabiliser_restriction_detE); it is
    multiplicative, nonzero and continuous on G. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From mathcomp Require Import fingroup perm.
From Federer Require Import RealMetricBackground InnerProductUP InnerNorm InnerMetric InnerNormedTopology
  LinearBasis FiniteIndependence FiniteBasisCriterion FiniteBasisComparison FiniteDualDimension
  Bilinear Annihilator Hom HomInner ModuleQuotient SubspaceCarrier GrassmannSubspaces SymmetricEndomorphisms
  InnerProductRestriction InvariantRestriction FiniteBasisExtension SimpleAdaptedBasis
  OrthonormalFamilies OrthonormalisationUP GramSchmidt InnerFiniteSynthesis InnerCoordinateContinuity
  TensorUP ExteriorDeterminant ExteriorLeibniz InversionCount TopExteriorInjectivity EuclideanLinearMaps
  TopologicalGroupUP TopologicalGroupLaws IsotropyGroupTopology HomSpaceTopology LinearGroupTopology
  LinearGroupSealed HomCompositionDeterminant HomHaarCovariance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [det_basis_any]: the determinant of 1.3.4, p. 16, does
    not depend on the base, also for bases indexed by different (equal)
    numbers of ordinals; supporting the adapted bases of Federer 2.7.16,
    p. 137. Supporting lemma. *)
Lemma det_basis_any (K : fieldType) (h2 : (1 + 1 : K) != 0) (V : lmodType K) k l
    (e : 'I_k -> V) (d : 'I_l -> V) (he : is_basis e) (hd : is_basis d) (f : {linear V -> V}) :
  det h2 he f = det h2 hd f.
Proof. have hkl := finite_basis_size he hd; subst l; exact: det_basis_independent. Qed.

Section AdaptedBasis.
Variable K : fieldType.
Variable V : lmodType K.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable W : subspace V.
Variable m : nat.
Variable w : 'I_m -> subspace_space W.
Hypothesis hw : is_basis w.

(** Source for [subspace_basis_independent]: a base of W is an
    independent family of V, Federer 1.1.2, p. 10; supporting
    "W c V ... dim W = m", 2.7.16, p. 137. Supporting lemma. *)
Lemma subspace_basis_independent : finite_independent (fun i => subspace_val (w i)).
Proof.
exact: (finite_independent_map (f := @subspace_inclusion K V W) (@subspace_val_injective K V W)
  (finite_basis_independent hw)).
Qed.

(** Source for [subspace_dimension_le]: dim W <= dim V for a subspace W
    of V, Federer 1.6.1, p. 23 (extension of a base of W to a base of
    V); supporting "0 < dim W = m < dim V = n", 2.7.16, p. 137.
    Supporting lemma. *)
Lemma subspace_dimension_le : (m <= n)%N.
Proof.
have [n' [hkn [f [hf _]]]] := finite_basis_extension subspace_basis_independent hb.
by rewrite -(finite_basis_size hf hb).
Qed.

(** Source for [is_adapted_basis]: a base e_1, ..., e_{m+q} of V whose
    first m members form the given base of W, as in "we choose a
    subspace Z of V so that V = W (+) Z", Federer 2.7.16, p. 137: Z is
    spanned by the remaining q members. Definition. *)
Definition is_adapted_basis (q : nat) (e : 'I_(m + q) -> V) : Prop :=
  is_basis e /\ forall i, e (lshift q i) = subspace_val (w i).

(** Source for [adapted_basis_exists]: "we choose a subspace Z of V so
    that V = W (+) Z", Federer 2.7.16, p. 137: the base of W extends to
    a base of V (1.6.1, p. 23), indexed by m + (n - m). Existence
    theorem. *)
Theorem adapted_basis_exists : exists e : 'I_(m + (n - m)) -> V, is_adapted_basis e.
Proof.
have hmn := subspace_dimension_le.
have [f [hf hfw]] := finite_basis_extension_fixed hmn subspace_basis_independent hb.
pose hc : (m + (n - m) = n)%N := subnKC hmn.
have hs : bijective (cast_ord hc) by exists (cast_ord (esym hc)); [exact: cast_ordK|exact: cast_ordKV].
exists (fun i => f (cast_ord hc i)); split.
- apply: finite_basis_criterion.
    exact: (reindexed_family_independent hs (finite_basis_independent hf)).
  apply: (reindexed_family_spanning hs)=> v.
  by exists (fun i => (dual_basis hf i v : K)); exact: basis_vector_expansion.
- move=> i; rewrite -hfw; congr f; exact: val_inj.
Qed.

Variable q : nat.
Variable e : 'I_(m + q) -> V.
Hypothesis heb : is_basis e.
Hypothesis hew : forall i, e (lshift q i) = subspace_val (w i).

(** Source for [adapted_subspace_vector]: a member x of W is
    sum_i w_i*(x) e_i, the sum over the first m members of the adapted
    base, Federer 1.6.3, p. 25; supporting 2.7.16, p. 137. Supporting
    lemma. *)
Lemma adapted_subspace_vector (x : subspace_space W) :
  subspace_val x = \sum_i (dual_basis hw i x : K) *: e (lshift q i).
Proof.
rewrite {1}(basis_vector_expansion hw x).
rewrite (linear_sum (@subspace_inclusion K V W)); apply: eq_bigr=> i _.
by rewrite linearZ /= hew.
Qed.

(** Source for [adapted_dual_left]: e_i*(x) = w_i*(x) for x in W and
    i <= m, Federer 1.6.3, p. 25; supporting 2.7.16, p. 137. Supporting
    lemma. *)
Lemma adapted_dual_left (x : subspace_space W) i :
  dual_basis heb (lshift q i) (subspace_val x) = dual_basis hw i x.
Proof.
rewrite adapted_subspace_vector.
rewrite (big_morph (dual_basis heb (lshift q i)) (linD (hom_linear _)) (lin0 (hom_linear _))).
rewrite (bigD1 i) // big1 ?Monoid.mulm1.
  by rewrite (linZ (hom_linear _)) dual_basisE eqxx; exact: mulr1.
move=> j /andP [_ hj]; rewrite (linZ (hom_linear _)) dual_basisE.
by rewrite (inj_eq (@lshift_inj m q)) (negbTE hj) scaler0.
Qed.

(** Source for [adapted_dual_right]: e_{m+j}*(x) = 0 for x in W,
    Federer 1.6.3, p. 25; supporting 2.7.16, p. 137. Supporting
    lemma. *)
Lemma adapted_dual_right (x : subspace_space W) j :
  dual_basis heb (rshift m j) (subspace_val x) = 0.
Proof.
rewrite adapted_subspace_vector.
rewrite (big_morph (dual_basis heb (rshift m j)) (linD (hom_linear _)) (lin0 (hom_linear _))).
apply: big1=> i _; rewrite (linZ (hom_linear _)) dual_basisE.
by rewrite eq_lrshift scaler0.
Qed.

(** Source for [adapted_subspaceE]: W is the set of common zeros of
    e_{m+1}*, ..., e_{m+q}*, so that W = wedge^1 V cap ... is the
    annihilator of its annihilator W' of Federer 2.7.16, p. 137, with
    1.6.3, p. 25. Supporting lemma. *)
Lemma adapted_subspaceE (y : V) : W y <-> forall j, dual_basis heb (rshift m j) y = 0.
Proof.
split.
  move=> hy j; have := adapted_dual_right (subspace_lift hy) j.
  by rewrite subspace_liftE.
move=> hy; rewrite (basis_vector_expansion heb y).
apply: big_ind; [exact: subspace_zero|move=> u v; exact: subspace_add|move=> k _].
case: (split_ordP k)=> [i ->|j ->].
  apply: subspace_scale; rewrite hew; exact: subspace_valP.
rewrite hy scale0r; exact: subspace_zero.
Qed.

End AdaptedBasis.

Section LinearFunctionalContinuity.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation VT := (inner_metric_space hB).

(** Source for [linear_functional_continuous]: every linear functional
    on V is continuous, since omega(y) = sum_i (y . e_i) omega(e_i) for
    an orthonormal base e (1.7.1, p. 28); supporting the closedness of
    the group of 2.7.16, p. 137. Supporting lemma. *)
Lemma linear_functional_continuous (omega : Hom V R^o) : continuous (fun y : VT => (omega y : R^o)).
Proof.
have [o [ho hoo]] := orthonormal_basis_exists hB hb.
have hon := orthonormalisation_orthonormal hoo.
have -> : (fun y : VT => (omega y : R^o)) =
    (fun y : VT => \sum_i (omega (o i) : R^o) * (inner_coordinate hB (o i) y : R^o)).
  apply: funext=> y.
  have h := @inner_finite_synthesis_coordinates R V B hB n o ho hon y.
  rewrite /inner_finite_synthesis in h.
  have hl : forall z : V, omega z = hom_as_linear omega z by [].
  rewrite -[in LHS]h hl linear_sum; apply: eq_bigr=> i _.
  by rewrite linearZ_LR /= mulrC.
apply: continuous_big; first exact: add_continuous.
move=> i _ y; apply: (@continuous_comp _ _ _ (fun y : VT => (inner_coordinate hB (o i) y : R^o))
  ( *%R (omega (o i) : R^o))); last exact: mulrl_continuous.
exact: inner_coordinate_continuous.
Qed.

End LinearFunctionalContinuity.

Section RealPowers.
Variable R : realType.
Variable T : topologicalType.

(** Source for [continuous_inverse_power]: |f|^{-k} is continuous for a
    continuous f without zeros, supporting "a continuous homomorphism
    chi", Federer 2.7.9, p. 126, for chi(g) = |det(g|W)|^{-m}
    |det g|^{m-n} of 2.7.16, p. 137. Supporting lemma. *)
Lemma continuous_inverse_power (f : T -> R^o) (k : nat) :
  continuous f -> (forall x, f x != 0) -> continuous (fun x => (`|f x| ^- k : R^o)).
Proof.
move=> hf hf0.
have ha : continuous (fun x => (`|f x| : R^o)).
  move=> x; apply: (@continuous_comp _ _ _ f (fun y : R^o => `|y|)); first exact: hf.
  exact: norm_continuous.
have hp : forall j, continuous (fun x => (`|f x| ^+ j : R^o)).
  elim=> [|j ih] x.
    have -> : (fun x => (`|f x| ^+ 0 : R^o)) = (fun _ => (1 : R^o)) by apply: funext=> y; rewrite expr0.
    exact: cst_continuous.
  have -> : (fun x => (`|f x| ^+ j.+1 : R^o)) = (fun x => (`|f x| : R^o) * `|f x| ^+ j).
    by apply: funext=> y; rewrite exprS.
  exact: (@continuousM R T _ _ x (ha x) (ih x)).
move=> x.
have h0 : `|f x| ^+ k != 0 by rewrite expf_neq0 // normr_eq0.
exact: (@continuousV R T (fun x => (`|f x| ^+ k : R^o)) x h0 (hp k x)).
Qed.

(** Source for [continuous_positive_power]: |f|^k is continuous for a
    continuous f, supporting "Delta_G(g) = |det(g|W)|^{-n} |det g|^m",
    Federer 2.7.16, p. 138, as a continuous function (2.7.8, p. 126).
    Supporting lemma. *)
Lemma continuous_positive_power (f : T -> R^o) (k : nat) :
  continuous f -> continuous (fun x => (`|f x| ^+ k : R^o)).
Proof.
move=> hf.
have ha : continuous (fun x => (`|f x| : R^o)).
  move=> x; apply: (@continuous_comp _ _ _ f (fun y : R^o => `|y|)); first exact: hf.
  exact: norm_continuous.
elim: k=> [|j ih] x.
  have -> : (fun x => (`|f x| ^+ 0 : R^o)) = (fun _ => (1 : R^o)) by apply: funext=> y; rewrite expr0.
  exact: cst_continuous.
have -> : (fun x => (`|f x| ^+ j.+1 : R^o)) = (fun x => (`|f x| : R^o) * `|f x| ^+ j).
  by apply: funext=> y; rewrite exprS.
exact: (@continuousM R T _ _ x (ha x) (ih x)).
Qed.

End RealPowers.

Section Stabiliser.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation H := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation VT := (inner_metric_space hB).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation mul := (linear_group_mul hB hb).
Local Notation inv := (linear_group_inv hB hb).
Local Notation unit := (linear_group_unit hB hb).
Local Notation hG := (linear_group_operations hB hb).
Local Notation h2 := (euclidean_two_nonzero R).
Variable W : subspace V.
Variable m : nat.
Hypothesis hW : grassmann_pred m W.

(** Source for [maps_subspace_onto]: "linear automorphisms of V which
    map W onto W", Federer 2.7.16, p. 137: W = f[W]. Definition. *)
Definition maps_subspace_onto (f : Hom V V) : Prop := forall y, W y <-> exists2 x, W x & f x = y.

(** Source for [subspace_stabiliser]: "G is the group of those linear
    automorphisms of V which map W onto W", Federer 2.7.16, p. 137, as
    a subset of the linear group of V. Definition. *)
Definition subspace_stabiliser : set GL := [set g | maps_subspace_onto (set_val g)].

(** Source for [subspace_stabiliser_invariant]: a member of G maps W
    into W, Federer 2.7.16, p. 137. Supporting lemma. *)
Lemma subspace_stabiliser_invariant (g : GL) :
  subspace_stabiliser g -> forall x, W x -> W ((set_val g : Hom V V) x).
Proof. by move=> hg x hx; apply/hg; exists x. Qed.

(** Source for [subspace_stabiliser_subgroup]: G is a subgroup of the
    linear group of V, "G is the group", Federer 2.7.16, p. 137.
    Supporting lemma. *)
Lemma subspace_stabiliser_subgroup : is_subgroup mul inv unit subspace_stabiliser.
Proof.
split.
- move=> y; rewrite /= (linear_group_unitE hG); split.
    by move=> hy; exists y=> //; rewrite hom_identityE.
  by move=> [x hx <-]; rewrite hom_identityE.
- move=> g h hg hh y; rewrite /= (linear_group_mulE hG); split.
    move=> /hg [x /hh [z hz <-] <-]; exists z=> //; by rewrite hom_compE.
  move=> [x hx <-]; rewrite hom_compE.
  by apply: (subspace_stabiliser_invariant hg); exact: (subspace_stabiliser_invariant hh).
- move=> g hg y; have [hgi hig] := linear_group_inv_cancel hG g; split.
    move=> hy; exists ((set_val g : Hom V V) y); last exact: hgi.
    exact: (subspace_stabiliser_invariant hg).
  move=> [x hx <-]; have [z hz hzx] := (hg x).1 hx.
  by rewrite -hzx hgi.
Qed.

(** Source for [subspace_stabiliser_restriction_exists]: G is a group
    with the operations of the linear group of V, Federer 2.7.16,
    p. 137. Existence of the restricted operations
    (subgroup_restriction_exists). *)
Theorem subspace_stabiliser_restriction_exists :
  exists mulS invS eS, is_subgroup_restriction mul inv unit subspace_stabiliser mulS invS eS.
Proof. exact: subgroup_restriction_exists subspace_stabiliser_subgroup. Qed.

(** Source for [subspace_stabiliser_iff]: a univalent linear map g of V
    maps W onto W if g[W] c W, since W is finite dimensional
    (1.1.2, p. 10); "G is the group of those linear automorphisms of V
    which map W onto W", Federer 2.7.16, p. 137. Supporting lemma. *)
Lemma subspace_stabiliser_iff (g : GL) :
  subspace_stabiliser g <-> forall x, W x -> W ((set_val g : Hom V V) x).
Proof.
split; first exact: subspace_stabiliser_invariant.
move=> hg; have [w hw] := hW.
pose r : {linear subspace_space W -> subspace_space W} :=
  GRing.Linear.clone _ _ _ _ (@invariant_restriction R V (hom_as_linear (set_val g : Hom V V)) W hg) _.
have hrE x : subspace_val (r x) = (set_val g : Hom V V) (subspace_val x) by [].
have hri : injective r.
  move=> x y hxy; apply: subspace_val_injective; apply: (set_valP g).
  by rewrite -!hrE hxy.
have hrs := finite_injective_surjective hw hri.
move=> y; split.
  move=> hy; have [x hx] := hrs (subspace_lift hy).
  exists (subspace_val x); first exact: subspace_valP.
  by rewrite -hrE hx subspace_liftE.
by move=> [x hx <-]; exact: (hg x hx).
Qed.

(** Source for [subspace_stabiliser_closed]: G is a closed subgroup of
    the linear group of V ("a closed subgroup", as used for the Haar
    integrals of G), Federer 2.7.16, p. 137: with an adapted base,
    g[W] c W means e_{m+j}*(g(x)) = 0 for x in W, and these are closed
    conditions on g by the continuity of evaluation (1.7.9, p. 35).
    Supporting theorem. *)
Theorem subspace_stabiliser_closed : closed subspace_stabiliser.
Proof.
have [w hw] := hW.
have [e [heb hew]] := adapted_basis_exists hb hw.
have -> : subspace_stabiliser =
    \bigcap_(x in [set x : V | W x]) \bigcap_(j in [set: 'I_(n - m)])
      [set g : GL | (dual_basis heb (rshift m j) ((set_val g : Hom V V) x) : R) = 0].
  apply/seteqP; split=> g.
    move=> hg x hx j _.
    exact: ((adapted_subspaceE hw heb hew _).1 (subspace_stabiliser_invariant hg hx) j).
  move=> hg; apply/subspace_stabiliser_iff=> x hx.
  by apply/(adapted_subspaceE hw heb hew)=> j; exact: (hg x hx j).
apply: closed_bigI=> x _; apply: closed_bigI=> j _.
have hc : continuous (fun g : GL => (dual_basis heb (rshift m j) ((set_val g : Hom V V) x) : R^o)).
  move=> g; apply: (@continuous_comp _ _ _ (fun g : GL => ((set_val g : Hom V V) x : VT))
    (fun y : VT => (dual_basis heb (rshift m j) y : R^o))); last first.
    exact: (linear_functional_continuous hb).
  apply: (@continuous_comp _ _ _ (set_val : GL -> H) (fun f : H => ((f : Hom V V) x : VT))).
    exact: set_type_val_continuous.
  exact: hom_evaluation_point_continuous.
have -> : [set g : GL | (dual_basis heb (rshift m j) ((set_val g : Hom V V) x) : R) = 0] =
    (fun g : GL => (dual_basis heb (rshift m j) ((set_val g : Hom V V) x) : R^o)) @^-1` [set 0].
  by [].
by apply: preimage_closed; [move=> g _; exact: hc|exact: closed_eq].
Qed.

Local Notation S := (set_type subspace_stabiliser).

(** Source for [stabiliser_val]: the linear automorphism of V given by
    a member of G, Federer 2.7.16, p. 137. Definition. *)
Definition stabiliser_val (g : S) : Hom V V := set_val (set_val g).

(** Source for [stabiliser_val_invariant]: g(W) c W for g in G,
    Federer 2.7.16, p. 137, in the form required by
    invariant_restriction (1.7.3, p. 29). Supporting lemma. *)
Lemma stabiliser_val_invariant (g : S) : invariant_subspace (hom_as_linear (stabiliser_val g)) W.
Proof. exact: (subspace_stabiliser_invariant (set_valP g)). Qed.

(** Source for [stabiliser_val_injective]: members of G are univalent,
    Federer 2.7.16, p. 137. Supporting lemma. *)
Lemma stabiliser_val_injective (g : S) : injective (stabiliser_val g).
Proof. exact: (set_valP (set_val g)). Qed.

(** Source for [stabiliser_restriction]: the restriction g|W of g in G,
    a linear automorphism of W, as in "det(g|W)", Federer 2.7.16,
    p. 137. Definition. *)
Definition stabiliser_restriction (g : S) : {linear subspace_space W -> subspace_space W} :=
  GRing.Linear.clone _ _ _ _ (invariant_restriction (stabiliser_val_invariant g)) _.

(** Source for [stabiliser_restrictionE]: (g|W)(x) = g(x), Federer
    2.7.16, p. 137. Supporting lemma. *)
Lemma stabiliser_restrictionE (g : S) x :
  subspace_val (stabiliser_restriction g x) = stabiliser_val g (subspace_val x).
Proof. by []. Qed.

(** Source for [stabiliser_restriction_det]: "det(g|W)", Federer
    2.7.16, p. 137, the determinant of 1.3.4, p. 16, of g|W with respect
    to a base of W chosen from grassmann_pred; it does not depend on the
    base (stabiliser_restriction_detE). Definition. *)
Definition stabiliser_restriction_det (g : S) : R :=
  det h2 (projT2 (cid hW)) (stabiliser_restriction g).

(** Source for [stabiliser_restriction_detE]: det(g|W) may be computed
    with any base of W, Federer 1.3.4, p. 16; supporting 2.7.16,
    p. 137. Supporting lemma. *)
Lemma stabiliser_restriction_detE (w : 'I_m -> subspace_space W) (hw : is_basis w) (g : S) :
  stabiliser_restriction_det g = det h2 hw (stabiliser_restriction g).
Proof. exact: det_basis_independent. Qed.

(** Source for [stabiliser_det]: "det g" for g in G, Federer 2.7.16,
    p. 137, the determinant of g as a member of the linear group of V
    (linear_group_det of HomHaarCovariance.v). Definition. *)
Definition stabiliser_det (g : S) : R := linear_group_det hB hb (set_val g).

(** Source for [stabiliser_restriction_injective]: g|W is univalent,
    Federer 2.7.16, p. 137. Supporting lemma. *)
Lemma stabiliser_restriction_injective (g : S) : injective (stabiliser_restriction g).
Proof.
move=> x y hxy; apply: subspace_val_injective; apply: (@stabiliser_val_injective g).
by rewrite -!stabiliser_restrictionE hxy.
Qed.

(** Source for [stabiliser_restriction_det_nonzero]: det(g|W) <> 0,
    Federer 1.3.4, p. 16, since g|W is univalent; supporting
    "|det(g|W)|^{-m}", 2.7.16, p. 137. Supporting lemma. *)
Lemma stabiliser_restriction_det_nonzero (g : S) : stabiliser_restriction_det g != 0.
Proof. by apply/(det_nonzero_injective _ _ _).2; exact: stabiliser_restriction_injective. Qed.

(** Source for [stabiliser_det_nonzero]: det g <> 0 for g in G, Federer
    1.3.4, p. 16. Supporting lemma. *)
Lemma stabiliser_det_nonzero (g : S) : stabiliser_det g != 0.
Proof. exact: linear_group_det_nonzero. Qed.

(** Source for [stabiliser_val_continuous]: the inclusion of G into
    Hom(V, V) is continuous for the relative topology, Federer 2.7.16,
    p. 137, with 2.7.1, p. 121. Supporting lemma. *)
Lemma stabiliser_val_continuous : continuous (fun g : S => (stabiliser_val g : H)).
Proof.
move=> g; apply: (@continuous_comp _ _ _ (set_val : S -> GL) (set_val : GL -> H)).
  exact: set_type_val_continuous.
exact: set_type_val_continuous.
Qed.

(** Source for [stabiliser_restriction_det_continuous]: g |-> det(g|W)
    is continuous on G: for an orthonormal base u of W (1.7.1, p. 28,
    1.7.3, p. 29) it is the sum over the permutations s of
    index(s) prod_i g(u_i) . u_{s(i)} (1.3.4, p. 16); supporting "a
    continuous homomorphism chi", 2.7.9, p. 126, for the chi of 2.7.16,
    p. 137. Supporting lemma. *)
Lemma stabiliser_restriction_det_continuous : continuous (fun g : S => (stabiliser_restriction_det g : R^o)).
Proof.
have [w hw] := hW.
have hBW := @restricted_inner_productP R V B hB W.
have [u [hu huo]] := orthonormal_basis_exists hBW hw.
have ho := orthonormalisation_orthonormal huo.
have hf : (fun g : S => (stabiliser_restriction_det g : R^o)) =
    (fun g : S => \sum_(s : 'S_m) FedererPermutation.index R s *
      \prod_(i < m) (B (stabiliser_val g (subspace_val (u i))) (subspace_val (u (s i))) : R^o)).
  apply: funext=> g; rewrite (stabiliser_restriction_detE hu).
  rewrite (det_formula h2 hu (f := stabiliser_restriction g)
    (b := fun i j => B (stabiliser_val g (subspace_val (u i))) (subspace_val (u j)))) // => i.
  have h := @inner_finite_synthesis_coordinates R (subspace_space W) _ hBW m u hu ho
    (stabiliser_restriction g (u i)).
  rewrite /inner_finite_synthesis in h; rewrite -[in LHS]h.
  by apply: eq_bigr=> j _; rewrite inner_coordinateE.
rewrite hf; apply: continuous_big; first exact: add_continuous.
move=> s _ g; apply: (@continuous_comp _ _ _
  (fun g : S => \prod_(i < m) (B (stabiliser_val g (subspace_val (u i))) (subspace_val (u (s i))) : R^o))
  ( *%R (FedererPermutation.index R s))); last exact: mulrl_continuous.
apply: continuous_big; first exact: mul_continuous.
move=> i _ h; apply: (@continuous_comp _ _ _ (fun g : S => (stabiliser_val g (subspace_val (u i)) : VT))
  (fun x : VT => (B x (subspace_val (u (s i))) : R^o))).
  apply: (@continuous_comp _ _ _ (fun g : S => (stabiliser_val g : H))
    (fun f : H => ((f : Hom V V) (subspace_val (u i)) : VT))).
    exact: stabiliser_val_continuous.
  exact: hom_evaluation_point_continuous.
have -> : (fun x : VT => (B x (subspace_val (u (s i))) : R^o)) =
    (fun x : VT => inner_coordinate hB (subspace_val (u (s i))) x).
  by apply: funext=> x; rewrite inner_coordinateE.
exact: inner_coordinate_continuous.
Qed.

(** Source for [stabiliser_det_continuous]: g |-> det g is continuous
    on G, Federer 2.7.16, pp. 135–137. Supporting lemma. *)
Lemma stabiliser_det_continuous : continuous (fun g : S => (stabiliser_det g : R^o)).
Proof.
move=> g; apply: (@continuous_comp _ _ _ (set_val : S -> GL) (linear_group_det hB hb : GL -> R^o)).
  exact: set_type_val_continuous.
exact: linear_group_det_continuous.
Qed.

Section Restriction.
Variables (mulS : S -> S -> S) (invS : S -> S) (eS : S).
Hypothesis hS : is_subgroup_restriction mul inv unit subspace_stabiliser mulS invS eS.

(** Source for [subspace_stabiliser_lch]: G, a closed subgroup of the
    linear group of V, is a locally compact Hausdorff topological group
    with the relative topology, Federer 2.7.16, p. 137, with 2.7.1,
    p. 121. Direct formalisation. *)
Theorem subspace_stabiliser_lch : is_locally_compact_hausdorff_group mulS invS eS.
Proof.
apply: (subgroup_restriction_locally_compact_hausdorff hS); last exact: subspace_stabiliser_closed.
exact: linear_group_operations_lch.
Qed.

(** Source for [stabiliser_mulE]: the multiplication of G is
    composition, Federer 2.7.16, p. 137. Supporting lemma. *)
Lemma stabiliser_mulE (g h : S) : stabiliser_val (mulS g h) = hom_comp (stabiliser_val g) (stabiliser_val h).
Proof. by rewrite /stabiliser_val (subgroup_restriction_mul hS) (linear_group_mulE hG). Qed.

(** Source for [stabiliser_unitE]: the identity of G is 1_V, Federer
    2.7.16, p. 137. Supporting lemma. *)
Lemma stabiliser_unitE : stabiliser_val eS = hom_identity V.
Proof. by rewrite /stabiliser_val (subgroup_restriction_unit hS) (linear_group_unitE hG). Qed.

(** Source for [stabiliser_inv_cancel]: g^{-1}(g(x)) = x and
    g(g^{-1}(x)) = x for g in G, Federer 2.7.16, p. 137. Supporting
    lemma. *)
Lemma stabiliser_inv_cancel (g : S) :
  cancel (stabiliser_val g) (stabiliser_val (invS g)) /\ cancel (stabiliser_val (invS g)) (stabiliser_val g).
Proof. by rewrite /stabiliser_val (subgroup_restriction_inv hS); exact: (linear_group_inv_cancel hG). Qed.

(** Source for [stabiliser_group_laws]: the group laws of G, Federer
    2.7.1, p. 121. Supporting lemma. *)
Lemma stabiliser_group_laws : is_group_laws mulS invS eS.
Proof. exact: topological_group_laws (lch_group_topological subspace_stabiliser_lch). Qed.

(** Source for [stabiliser_det_mul]: det(g h) = det g . det h on G,
    Federer 1.3.4, p. 16. Supporting lemma. *)
Lemma stabiliser_det_mul (g h : S) : stabiliser_det (mulS g h) = stabiliser_det g * stabiliser_det h.
Proof. by rewrite /stabiliser_det (subgroup_restriction_mul hS) linear_group_det_mul. Qed.

(** Source for [stabiliser_restriction_mul]: (g h)|W = (g|W) o (h|W),
    Federer 2.7.16, p. 137. Supporting lemma. *)
Lemma stabiliser_restriction_mul (g h : S) x :
  stabiliser_restriction (mulS g h) x = stabiliser_restriction g (stabiliser_restriction h x).
Proof. by apply: subspace_val_injective; rewrite !stabiliser_restrictionE stabiliser_mulE hom_compE. Qed.

(** Source for [stabiliser_restriction_det_mul]: det((g h)|W) =
    det(g|W) det(h|W), Federer 1.3.4, p. 16, so that
    g |-> |det(g|W)|^{-m} is a homomorphism of G (2.7.1, p. 122);
    supporting 2.7.16, p. 137. Supporting lemma. *)
Lemma stabiliser_restriction_det_mul (g h : S) :
  stabiliser_restriction_det (mulS g h) = stabiliser_restriction_det g * stabiliser_restriction_det h.
Proof.
rewrite /stabiliser_restriction_det -det_comp; apply: det_ext=> x.
exact: stabiliser_restriction_mul.
Qed.

(** Source for [stabiliser_restriction_det_unit]: det(1_V|W) = 1,
    Federer 1.3.4, p. 16. Supporting lemma. *)
Lemma stabiliser_restriction_det_unit : stabiliser_restriction_det eS = 1.
Proof.
rewrite /stabiliser_restriction_det -(det_id h2 (projT2 (cid hW))); apply: det_ext=> x.
by apply: subspace_val_injective; rewrite stabiliser_restrictionE stabiliser_unitE hom_identityE.
Qed.

(** Source for [stabiliser_restriction_det_inv]: det(g^{-1}|W) =
    det(g|W)^{-1}, Federer 1.3.4, p. 16. Supporting lemma. *)
Lemma stabiliser_restriction_det_inv (g : S) :
  stabiliser_restriction_det (invS g) = (stabiliser_restriction_det g)^-1.
Proof.
apply: (mulIf (stabiliser_restriction_det_nonzero g)).
rewrite -stabiliser_restriction_det_mul (group_mulVg stabiliser_group_laws).
by rewrite stabiliser_restriction_det_unit mulVf // stabiliser_restriction_det_nonzero.
Qed.

(** Source for [stabiliser_det_inv]: det(g^{-1}) = (det g)^{-1} on G,
    Federer 1.3.4, p. 16. Supporting lemma. *)
Lemma stabiliser_det_inv (g : S) : stabiliser_det (invS g) = (stabiliser_det g)^-1.
Proof. by rewrite /stabiliser_det (subgroup_restriction_inv hS) linear_group_det_inv. Qed.

End Restriction.

End Stabiliser.

Arguments maps_subspace_onto {R V} W f.
Arguments subspace_stabiliser {R V B} hB {n b} hb W.
Arguments stabiliser_val {R V B hB n b hb W} g.
Arguments stabiliser_restriction {R V B hB n b hb W} g.
Arguments stabiliser_restriction_det {R V B hB n b hb W m} hW g.
Arguments stabiliser_det {R V B hB n b hb W} g.
Arguments stabiliser_restriction_det_continuous {R V B hB n b hb W m} hW {x t} _.
