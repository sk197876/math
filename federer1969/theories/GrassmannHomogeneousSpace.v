(** Federer (1969), 2.7.16, printed p. 139, example (6): "In particular we
    thus obtain the O(n) invariant measures ... gamma_{n,m} over G(n, m)".
    G(n, m) is the set of m dimensional vector subspaces of R^n (1.6.2, p.
    24; GrassmannSubspaces.v), on which O(n) acts by A(g, W) = g[W]. Federer
    gives G(n, m) no topology at this place; in 3.2.28(4), pp. 266-267, he
    identifies G(n, m) with a submanifold of a Euclidean space. This module
    supplies a topology following the standard identification of a subspace
    W with the orthogonal projection P_W of R^n onto W (1.7.4, p. 30): G(V,
    m) carries the initial topology of W |-> P_W into Hom(V, V) (1.7.9, p.
    35; HomSpaceTopology.v). P_W is specified by the laws P_W(x) in W and (x
    - P_W(x)) . w = 0 for w in W, which determine it; it exists because W is
    the image of an orthogonal injection f of an m dimensional space U into
    V (an orthonormal basis of W, 1.7.1, p. 28), and then P_W(x) = sum_i (x
    . f(e_i)) f(e_i) for an orthonormal basis e of U. The map W |-> P_W is
    univalent, so G(V, m) is Hausdorff; P_{g[W]} = g o P_W o g^{-1} for g in
    O(V), so the action is continuous; O(V) acts transitively on G(V, m)
    because it acts transitively on O(U, V) (OrthogonalInjectionSpaces.v).
    By CompactGroupHomogeneousMeasures.v, G(V, m) is a compact homogeneous
    space of O(V) in the sense of 2.7.1, p. 121, with exactly one O(V)
    invariant measure of total measure 1. neither topologises it. The local
    erratum has no entry for p. 139. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology.
From Federer Require Import InnerProductUP InnerProductLaws InnerMetric LinearBasis FiniteDualDimension Annihilator
  FiniteSpans Bilinear TensorUP Hom HomInner ModuleQuotient SubspaceCarrier SubspaceEquality
  GrassmannSubspaces InnerProductRestriction OrthogonalMaps OrthonormalFamilies
  OrthonormalProjection OrthonormalisationUP GramSchmidt OrthogonalBasisCriteria BasisInterpolation
  IsotropyGroupTopology TopologicalProductMaps TopologicalGroupUP TopologicalGroupLaws
  HomogeneousSpaceUP MeasurePushforward HomSpaceTopology LinearGroupTopology LinearGroupSealed
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure CompactGroupHaarNormalisation
  CompactGroupHomogeneousMeasures OrthogonalInjectionSpaces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section LinearImages.
Variable R : realType.
Variables U V : lmodType R.
Variable m : nat.
Variable c : 'I_m -> U.
Hypothesis hc : is_basis c.
Variable f : {linear U -> V}.

(** Source for [linear_image_subspace]: the image f[U] of a linear map,
    a vector subspace of V, Federer 1.6.2, p. 24, and 1.7.4, p. 30;
    supporting the action A(g, W) = g[W] of O(n) on G(n, m) in 2.7.16,
    p. 139. Definition. *)
Definition linear_image_subspace : subspace V.
Proof.
apply: (@Subspace R V (fun y => exists u, f u = y)).
- by exists 0; rewrite linear0.
- by move=> x y [u <-] [w <-]; exists (u + w); rewrite linearD.
- by move=> a x [u <-]; exists (a *: u); rewrite linearZ.
Defined.

(** Source for [linear_image_subspaceE]: y belongs to f[U] if and only
    if y = f(u) for some u, Federer 1.6.2, p. 24. Supporting lemma. *)
Lemma linear_image_subspaceE y : linear_image_subspace y <-> exists u, f u = y.
Proof. by []. Qed.

Hypothesis hf : injective f.

(** Source for [linear_image_grassmann_pred]: if f is univalent and U
    has a basis of m vectors, then f[U] is m dimensional, Federer 1.6.2,
    p. 24: the images of the basis vectors form a basis of f[U].
    Supporting lemma. *)
Lemma linear_image_grassmann_pred : grassmann_pred m linear_image_subspace.
Proof.
pose S := linear_image_subspace.
have hmem i : S (f (c i)) by exists (c i).
pose e i : subspace_space S := subspace_lift (hmem i).
have hval x : subspace_val (basis_synthesis e x) = f (basis_synthesis c x).
  have h1 := @basis_synthesis_comp R _ _ _ e (subspace_inclusion S) x.
  have h2 := @basis_synthesis_comp R _ _ _ c f x.
  exact: (eq_trans (esym h1) h2).
exists e; apply/basisP; split.
- move=> x y hxy; apply: (basis_synthesis_injective hc); apply: hf.
  by rewrite -!hval hxy.
- move=> v; have [u hu] : S (subspace_val v) := subspace_valP v.
  exists (basis_coordinates hc u); apply: subspace_val_injective.
  by rewrite hval basis_coordinatesK hu.
Qed.

(** Source for [linear_image_grassmann]: f[U] as a member of G(V, m),
    Federer 1.6.2, p. 24. Definition. *)
Definition linear_image_grassmann : G V m := GrassmannSubspace linear_image_grassmann_pred.

(** Source for [linear_image_grassmannE]: the members of
    linear_image_grassmann are the vectors f(u), Federer 1.6.2, p. 24.
    Supporting lemma. *)
Lemma linear_image_grassmannE y : grassmann_val linear_image_grassmann y <-> exists u, f u = y.
Proof. by []. Qed.

End LinearImages.

Section Frames.
Variable R : realType.
Variables U V : lmodType R.
Variables (C : U -> U -> R) (B : V -> V -> R).
Hypotheses (hC : is_inner_product C) (hB : is_inner_product B).
Variable m : nat.
Variable c : 'I_m -> U.
Hypothesis hc : is_basis c.

(** Source for [grassmann_orthogonal_frame]: every W in G(n, m) is the
    image of a member of O(n, m), Federer 1.7.1-1.7.2, p. 28, supporting
    2.7.16, p. 139: an orthonormal basis of W (1.7.1) and one of U define
    an orthogonal injection f of U into V with f[U] = W. Supporting
    lemma. *)
Lemma grassmann_orthogonal_frame (W : G V m) :
  exists f : {linear U -> V}, is_orthogonal_map C B f /\
    forall y, grassmann_val W y <-> exists u, f u = y.
Proof.
pose S := grassmann_val W.
have [e he] := grassmann_proof W.
have hCS := restricted_inner_productP hB S.
have [e' [he' hgs]] := orthonormal_basis_exists hCS he.
have ho' := orthonormalisation_orthonormal hgs.
pose a i := subspace_val (e' i).
have ha : orthonormal_family B a := ho'.
have [eU [heU hgsU]] := orthonormal_basis_exists hC hc.
have hoU := orthonormalisation_orthonormal hgsU.
pose f := basis_interpolation heU a.
have hfa i : f (eU i) = a i := basis_interpolationE heU a i.
exists f; split.
  apply: (orthogonal_map_basis_criterion hC hB heU hoU)=> i j.
  by apply: (eq_trans _ (ha i j)); congr B; exact: hfa.
pose g := linear_comp (subspace_inclusion S) (basis_interpolation heU e').
have hfg : forall u, f u = g u.
  apply: (basis_linear_ext heU f g)=> i; apply: (eq_trans (hfa i)).
  rewrite /g /linear_comp /=; congr subspace_val; exact: esym (basis_interpolationE heU e' i).
pose k := basis_interpolation he' eU.
have hgk : forall v, basis_interpolation heU e' (k v) = v.
  apply: (basis_linear_ext he' (linear_comp (basis_interpolation heU e') k) (linear_id _))=> i.
  rewrite /linear_comp /= /k.
  apply: (eq_trans (congr1 (basis_interpolation heU e') (basis_interpolationE he' eU i))).
  exact: basis_interpolationE.
move=> y; split.
- move=> hy; exists (k (subspace_lift hy)); apply: (eq_trans (hfg _)).
  rewrite /g /linear_comp /=.
  exact: (eq_trans (congr1 subspace_val (hgk (subspace_lift hy))) (subspace_liftE hy)).
- move=> [u <-]; rewrite hfg; exact: subspace_valP.
Qed.

(** Source for [orthogonal_injection_image_span]: for an orthogonal
    injection f and an orthonormal basis e of U, f[U] is the span of the
    orthonormal family f(e), Federer 1.7.1-1.7.2, p. 28. Supporting
    lemma. *)
Lemma orthogonal_injection_image_span (eU : 'I_m -> U) (heU : is_basis eU) (f : {linear U -> V}) y :
  (exists u, f u = y) <-> in_finite_span (fun i => f (eU i)) y.
Proof.
split.
- move=> [u <-]; exists (fun i => dual_basis heU i u).
  rewrite {1}(basis_vector_expansion heU u) linear_sum; apply: eq_bigr=> i _; exact: linearZ.
- move=> [d ->]; exists (\sum_i d i *: eU i); rewrite linear_sum; apply: eq_bigr=> i _.
  exact: linearZ.
Qed.

(** Source for [is_grassmann_projection]: the orthogonal projection
    P_W of V onto W in G(V, m), Federer 1.7.4, p. 30, used to topologise
    G(n, m) for 2.7.16, p. 139. Definition by its laws: P_W(x) belongs
    to W and x - P_W(x) is perpendicular to W. *)
Definition is_grassmann_projection (W : G V m) (P : Hom V V) : Prop :=
  (forall x, grassmann_val W (P x)) /\ (forall x w, grassmann_val W w -> B (x - P x) w = 0).

(** Source for [grassmann_projection_exists]: the orthogonal projection
    onto W in G(V, m) exists, Federer 1.7.1, p. 28, and 1.7.4, p. 30:
    P_W(x) = sum_i (x . a_i) a_i for an orthonormal basis a of W.
    Existence proof for is_grassmann_projection. *)
Lemma grassmann_projection_exists (W : G V m) : exists P : Hom V V, is_grassmann_projection W P.
Proof.
have [f [hf hW]] := grassmann_orthogonal_frame W.
have [eU [heU hgsU]] := orthonormal_basis_exists hC hc.
have hoU := orthonormalisation_orthonormal hgsU.
pose a i := f (eU i).
have ha : orthonormal_family B a := orthogonal_map_orthonormal hf hoU.
pose P := @orthonormal_projection R V B hB (Finite.clone 'I_m _) a.
exists (hom_of_linear (GRing.Linear.clone _ _ _ _ P _)); split.
- move=> x; apply/hW/(orthogonal_injection_image_span heU).
  exact: orthonormal_projection_in_span.
- move=> x w /hW /(orthogonal_injection_image_span heU) [d ->].
  change (B (x - P x) (\sum_i d i *: a i) = 0).
  rewrite (inner_symmetric hB) -(inner_coordinateE hB) linear_sum big1 // => i _.
  rewrite linearZ inner_coordinateE (inner_symmetric hB).
  rewrite (@orthonormal_residual_orthogonal R V B hB (Finite.clone 'I_m _) a ha x i).
  exact: mulr0.
Qed.

(** Source for [grassmann_perpendicular_member_zero]: a vector of W
    perpendicular to W is 0, Federer 1.7.1, p. 28, supporting the
    uniqueness of the orthogonal projection P_W, 1.7.4, p. 30.
    Supporting lemma. *)
Lemma grassmann_perpendicular_member_zero (W : G V m) d :
  grassmann_val W d -> (forall w, grassmann_val W w -> B d w = 0) -> d = 0.
Proof.
move=> hd h; apply/eqP; rewrite -(inner_self_eq0 hB); apply/eqP; exact: h.
Qed.

(** Source for [grassmann_projection_unique]: the orthogonal projection
    onto W is unique, Federer 1.7.4, p. 30. Supporting lemma: P(x) - Q(x)
    lies in W and is perpendicular to W. *)
Lemma grassmann_projection_unique (W : G V m) (P Q : Hom V V) :
  is_grassmann_projection W P -> is_grassmann_projection W Q -> P = Q.
Proof.
move=> [hP1 hP2] [hQ1 hQ2]; apply: hom_ext=> x; apply/eqP; rewrite -subr_eq0; apply/eqP.
apply: (grassmann_perpendicular_member_zero (subspace_sub (hP1 x) (hQ1 x)))=> w hw.
have -> : P x - Q x = (x - Q x) - (x - P x) by rewrite opprB [RHS]addrC addrA subrK.
by rewrite (bilBl (inner_bilinear hB)) hQ2 // hP2 // subrr.
Qed.

(** Source for [grassmann_projection]: the orthogonal projection P_W of
    V onto W in G(V, m), Federer 1.7.4, p. 30; supporting the topology
    of G(n, m) used in 2.7.16, p. 139. Definition by choice of the
    unique map with is_grassmann_projection; later results use only
    grassmann_projectionP and grassmann_projection_unique. *)
Definition grassmann_projection (W : G V m) : Hom V V := projT1 (cid (grassmann_projection_exists W)).

(** Source for [grassmann_projectionP]: P_W satisfies the laws of the
    orthogonal projection onto W, Federer 1.7.4, p. 30. Specification
    of grassmann_projection. *)
Lemma grassmann_projectionP (W : G V m) : is_grassmann_projection W (grassmann_projection W).
Proof. exact: (projT2 (cid (grassmann_projection_exists W))). Qed.

(** Source for [grassmann_projection_fixed]: P_W(w) = w for w in W,
    Federer 1.7.4, p. 30. Supporting lemma. *)
Lemma grassmann_projection_fixed (W : G V m) w : grassmann_val W w -> grassmann_projection W w = w.
Proof.
move=> hw; have [h1 h2] := grassmann_projectionP W.
apply/eqP; rewrite eq_sym -subr_eq0; apply/eqP.
apply: (grassmann_perpendicular_member_zero (subspace_sub hw (h1 w)))=> w' hw'.
exact: h2.
Qed.

(** Source for [grassmann_projection_injective]: W |-> P_W is
    univalent on G(V, m), Federer 1.7.4, p. 30: W is the set of fixed
    points of P_W. Supporting lemma for the Hausdorff property of
    G(n, m), 2.7.16, p. 139. *)
Lemma grassmann_projection_injective : injective grassmann_projection.
Proof.
move=> W W' he; apply: grassmann_ext=> v; split=> hv.
- rewrite -(grassmann_projection_fixed hv) he; exact: (grassmann_projectionP W').1.
- rewrite -(grassmann_projection_fixed hv) -he; exact: (grassmann_projectionP W).1.
Qed.

End Frames.

Section SubspaceImages.
Variable R : realType.
Variables U V : lmodType R.
Variables (C : U -> U -> R) (B : V -> V -> R).
Hypotheses (hC : is_inner_product C) (hB : is_inner_product B).
Variable m : nat.
Variable c : 'I_m -> U.
Hypothesis hc : is_basis c.
Variable g : {linear V -> V}.
Hypothesis hg : injective g.

(** Source for [subspace_image]: the image g[S] of a subspace S under a
    linear map g, Federer 2.7.16, p. 139, for the action of O(n) on
    G(n, m). Definition. *)
Definition subspace_image (S : subspace V) : subspace V.
Proof.
apply: (@Subspace R V (fun y => exists2 w, S w & g w = y)).
- by exists 0; [exact: subspace_zero|rewrite linear0].
- move=> x y [w hw <-] [z hz <-]; exists (w + z); last by rewrite linearD.
  exact: subspace_add.
- move=> a x [w hw <-]; exists (a *: w); last by rewrite linearZ.
  exact: subspace_scale.
Defined.

(** Source for [grassmann_image_pred]: g[W] is m dimensional for W in
    G(V, m) and univalent g, Federer 1.6.2, p. 24. Supporting lemma: W
    is the image of an orthogonal injection f of U, so g[W] is the image
    of g o f. *)
Lemma grassmann_image_pred (W : G V m) : grassmann_pred m (subspace_image (grassmann_val W)).
Proof.
have [f [hf hW]] := grassmann_orthogonal_frame hC hB hc W.
have he : subspace_image (grassmann_val W) = linear_image_subspace (linear_comp g f).
  apply: subspace_ext=> y; split.
  - by move=> [w /hW [u <-] <-]; exists u.
  - move=> [u <-]; exists (f u)=> //; apply/hW; by exists u.
rewrite he; apply: (linear_image_grassmann_pred hc).
by move=> x y /hg /(orthogonal_map_injective hC hB hf).
Qed.

(** Source for [grassmann_image]: g[W] as a member of G(V, m), Federer
    2.7.16, p. 139. Definition. *)
Definition grassmann_image (W : G V m) : G V m := GrassmannSubspace (grassmann_image_pred W).

(** Source for [grassmann_imageE]: y belongs to g[W] if and only if
    y = g(w) for some w in W, Federer 2.7.16, p. 139. Supporting lemma. *)
Lemma grassmann_imageE (W : G V m) y :
  grassmann_val (grassmann_image W) y <-> exists2 w, grassmann_val W w & g w = y.
Proof. by []. Qed.

End SubspaceImages.

Section GrassmannSpace.
Variable R : realType.
Variables U V : lmodType R.
Variables (C : U -> U -> R) (B : V -> V -> R).
Hypotheses (hC : is_inner_product C) (hB : is_inner_product B).
Variables (m : nat) (c : 'I_m -> U) (n : nat) (b : 'I_n -> V).
Hypotheses (hc : is_basis c) (hb : is_basis b).
Local Notation HVV := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation O := (orthogonal_group hB hb).
Local Notation om := (@orthogonal_element_map R V B hB n b hb).

(** Source for [grassmann_carrier]: the set G(V, m) of m dimensional
    subspaces of V, Federer 1.6.2, p. 24, as a type with a choice
    structure, supporting its topology for 2.7.16, p. 139. Definition. *)
Definition grassmann_carrier : Type := G V m.
HB.instance Definition _ := gen_eqMixin grassmann_carrier.
HB.instance Definition _ := gen_choiceMixin grassmann_carrier.

(** Source for [grassmann_space]: G(n, m) as a topological space,
    Federer 2.7.16, p. 139, "gamma_{n,m} over G(n, m)": the initial
    topology of W |-> P_W into Hom(V, V). Definition; this topology is
    supplied, see the header. *)
Definition grassmann_space :=
  initial_topology (fun W : grassmann_carrier => (grassmann_projection hC hB hc W : HVV)).

(** Source for [grassmann_space_projection_continuous]: W |-> P_W is
    continuous on G(n, m), by definition of the topology, Federer
    2.7.16, p. 139. Supporting lemma. *)
Lemma grassmann_space_projection_continuous :
  continuous (fun W : grassmann_space => (grassmann_projection hC hB hc W : HVV)).
Proof. exact: initial_continuous. Qed.

(** Source for [grassmann_space_hausdorff]: G(n, m) is a Hausdorff
    space, Federer 2.7.1, p. 121, and 2.7.16, p. 139: W |-> P_W is
    univalent and Hom(V, V) is Hausdorff. Supporting lemma. *)
Lemma grassmann_space_hausdorff : hausdorff_space grassmann_space.
Proof.
move=> W W' hcl; apply: (@grassmann_projection_injective R U V C B hC hB m c hc).
apply: (@hom_space_hausdorff R V V B B hB hB n b hb)=> S T hS hT.
have hcont := grassmann_space_projection_continuous.
have [w [hwS hwT]] := hcl _ _ (hcont W S hS) (hcont W' T hT).
by exists (grassmann_projection hC hB hc w).
Qed.

(** Source for [grassmann_action]: the action A(g, W) = g[W] of O(n) on
    G(n, m), Federer 2.7.16, p. 139. Definition. *)
Definition grassmann_action (g : O) (W : grassmann_space) : grassmann_space :=
  grassmann_image hC hB hc
    (orthogonal_map_injective hB hB (orthogonal_element_orthogonal g)) W.

(** Source for [grassmann_actionE]: y belongs to g[W] if and only if
    y = g(w) for some w in W, Federer 2.7.16, p. 139. Supporting lemma. *)
Lemma grassmann_actionE (g : O) (W : grassmann_space) y :
  grassmann_val (grassmann_action g W : G V m) y <-> exists2 w, grassmann_val (W : G V m) w & om g w = y.
Proof. by []. Qed.

Variables (mulS : O -> O -> O) (invS : O -> O) (eS : O).
Hypothesis hS : is_subgroup_restriction (linear_group_mul hB hb) (linear_group_inv hB hb)
  (linear_group_unit hB hb) O mulS invS eS.

(** Source for [hOT]: O(n) is a topological group, Federer 2.7.16,
    p. 139, used in this section. *)
Let hOT : is_topological_group mulS invS eS := lch_group_topological (orthogonal_group_lch hS).
(** Source for [hOc]: O(n) is compact, Federer 2.7.16, p. 139, used in
    this section. *)
Let hOc : compact [set: O] := @orthogonal_group_compact_space R V B hB n b hb.

(** Source for [grassmann_action_projection]: P_{g[W]} = g o P_W o
    g^{-1} for g in O(n), Federer 1.7.4, p. 30, supporting the
    continuity of the action of O(n) on G(n, m), 2.7.16, p. 139.
    Supporting lemma, by grassmann_projection_unique. *)
Lemma grassmann_action_projection (g : O) (W : grassmann_space) :
  grassmann_projection hC hB hc (grassmann_action g W) =
    hom_comp (hom_comp (om g) (grassmann_projection hC hB hc W)) (om (invS g)).
Proof.
apply: (grassmann_projection_unique hB (grassmann_projectionP hC hB hc _)).
have [h1 h2] := grassmann_projectionP hC hB hc W.
have [hgi hig] := orthogonal_element_inv hS g.
split.
- move=> x; rewrite !hom_compE; exists (grassmann_projection hC hB hc W (om (invS g) x))=> //.
- move=> x w' [w hw <-]; rewrite !hom_compE.
  rewrite -{1}(hig x) -(linearB (hom_as_linear (om g))) /=.
  change (B (om g (om (invS g) x - grassmann_projection hC hB hc W (om (invS g) x))) (om g w) = 0).
  by rewrite (orthogonal_element_inner g) h2.
Qed.

(** Source for [grassmann_action_continuous]: the action of O(n) on
    G(n, m) is continuous, Federer 2.7.1, p. 121, and 2.7.16, pp. 134
    and 139. Supporting lemma: (g, W) |-> g o P_W o g^{-1} is
    continuous, composition and inversion being continuous. *)
Lemma grassmann_action_continuous :
  continuous (fun p : O * grassmann_space => grassmann_action p.1 p.2).
Proof.
apply: continuous_comp_initial.
have -> : (fun W : grassmann_carrier => (grassmann_projection hC hB hc W : HVV)) \o
    (fun p : O * grassmann_space => grassmann_action p.1 p.2) =
    (fun q : HVV * HVV => (hom_comp (q.1 : Hom V V) (q.2 : Hom V V) : HVV)) \o
      (fun p : O * grassmann_space =>
        ((hom_comp (om p.1) (grassmann_projection hC hB hc p.2) : HVV), (om (invS p.1) : HVV))).
  by apply: funext=> p; rewrite /= grassmann_action_projection.
have hcomp := @hom_composition_continuous R V B hB n b hb.
have hom1 := @orthogonal_element_continuous R V B hB n b hb.
have hP := grassmann_space_projection_continuous.
have hp1 : continuous (fun p : O * grassmann_space =>
    ((om p.1 : HVV), (grassmann_projection hC hB hc p.2 : HVV))).
  apply: (@topological_pair_continuous (O * grassmann_space)%type HVV HVV).
  - by move=> q; exact: continuous_comp (@first_projection_continuous O grassmann_space q) (hom1 q.1).
  - by move=> q; exact: continuous_comp (@second_projection_continuous O grassmann_space q) (hP q.2).
have hp : continuous (fun p : O * grassmann_space =>
    ((hom_comp (om p.1) (grassmann_projection hC hB hc p.2) : HVV), (om (invS p.1) : HVV))).
  apply: (@topological_pair_continuous (O * grassmann_space)%type HVV HVV).
  - by move=> q; exact: (continuous_comp (hp1 q) (hcomp _)).
  - move=> q.
    have h1 := @first_projection_continuous O grassmann_space q.
    have h2 : {for q.1, continuous invS} := @topological_group_inv_continuous _ _ _ _ hOT q.1.
    exact: (continuous_comp h1 (continuous_comp h2 (hom1 (invS q.1)))).
by move=> p; exact: (continuous_comp (hp p) (hcomp _)).
Qed.

(** Source for [grassmann_action_compatible]: A(gh, W) = A(g, A(h, W)),
    Federer 2.7.1, p. 121, for the action of O(n) on G(n, m), 2.7.16,
    p. 139. Supporting lemma. *)
Lemma grassmann_action_compatible g h (W : grassmann_space) :
  grassmann_action (mulS g h) W = grassmann_action g (grassmann_action h W).
Proof.
apply: grassmann_ext=> y; split.
- move=> [w hw <-]; exists (om h w); first by exists w.
  exact: esym (orthogonal_element_mulE hS g h w).
- move=> [w' [w hw <-] <-]; exists w=> //.
  exact: (orthogonal_element_mulE hS g h w).
Qed.

(** Source for [grassmann_action_transitive]: O(n) acts transitively on
    G(n, m), Federer 2.7.16, p. 139. Proof supplied: W_1, W_2 are the
    images of orthogonal injections f_1, f_2 of U, and g o f_1 = f_2 for
    some g in O(n) (orthogonal_injection_transitive). *)
Lemma grassmann_action_transitive (W1 W2 : grassmann_space) : exists g, grassmann_action g W1 = W2.
Proof.
have [f1 [hf1 hW1]] := grassmann_orthogonal_frame hC hB hc (W1 : G V m).
have [f2 [hf2 hW2]] := grassmann_orthogonal_frame hC hB hc (W2 : G V m).
have [g [hg hgf]] := orthogonal_injection_transitive hC hB hc hb hf1 hf2.
exists (orthogonal_element_of hB hb hg); apply: grassmann_ext=> y; split.
- move=> [w /hW1 [u <-] <-]; apply/hW2; exists u.
  exact: esym (hgf u).
- move=> /hW2 [u <-]; exists (f1 u); first by apply/hW1; exists u.
  exact: (hgf u).
Qed.

(** Source for [grassmann_space_homogeneous]: G(n, m) is a homogeneous
    space of O(n) through A(g, W) = g[W], Federer 2.7.1, p. 121, as used
    in 2.7.16, p. 139. Supporting theorem, by
    compact_transitive_homogeneous. *)
Theorem grassmann_space_homogeneous : is_homogeneous_space mulS grassmann_action.
Proof.
apply: (compact_transitive_homogeneous hOT hOc grassmann_space_hausdorff
  grassmann_action_continuous grassmann_action_compatible).
exact: grassmann_action_transitive.
Qed.

(** Source for [grassmann_space_compact]: G(n, m) is compact, Federer
    2.7.16, p. 139, being the image of O(n). Supporting lemma. *)
Lemma grassmann_space_compact : compact [set: grassmann_space].
Proof. exact: compact_homogeneous_space_compact hOc grassmann_space_homogeneous. Qed.

(** Source for [grassmann_invariant_measure]: "the O(n) invariant
    measures ... gamma_{n,m} over G(n, m)", Federer 2.7.16, p. 139: for
    a point W_0 of G(V, m) there is exactly one O(V) invariant measure
    over G(V, m) with total measure 1, and it equals (A^W)_# theta for
    every W in G(V, m) and the normalised Haar measure theta of O(V).
    Direct formalisation. *)
Theorem grassmann_invariant_measure (W0 : grassmann_space) :
  exists phi : set grassmann_space -> \bar R,
    [/\ is_normalised_invariant_measure grassmann_action phi,
      forall psi, is_normalised_invariant_measure grassmann_action psi -> psi = phi &
      forall theta W, is_normalised_haar_measure mulS theta ->
        measure_pushforward (orbit_map grassmann_action W) theta = phi].
Proof.
exact: (normalised_invariant_measure_exists R (orthogonal_group_lch hS) hOc
  grassmann_space_homogeneous grassmann_space_hausdorff W0).
Qed.

End GrassmannSpace.

Arguments grassmann_projection {R U V C B} hC hB {m c} hc W.
Arguments grassmann_action {R U V C B} hC hB {m c n b} hc hb g W.
