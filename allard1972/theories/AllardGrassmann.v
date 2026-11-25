(** Allard (1972), 2.3, printed pp. 421–422: the Grassmann manifold
    G(n, k); blueprint labels al:2.3 and new:grass_compact. Following
    Allard's identification of a k dimensional subspace of R^n with the
    orthogonal projection onto it, G(n, k) is here the set of orthogonal
    projectors S ∈ Hom(R^n, R^n) of rank k (S ∘ S = S, S^* = S,
    trace S = k), see AllardOrthogonalProjectors.v. It is a subset of
    Hom(R^n, R^n) with the metric of the norm |f| = (f • f)^{1/2} of
    Allard 2.2 (Federer 1.7.9), and it is compact. The type
    [projection_grassmann R n k] is this metric space; the product
    [grassmann_bundle R n k] = R^n × G(n, k), on which k dimensional
    varifolds in R^n live (Allard 3.1), carries the maximum of the two
    distances (MetricProductBackground.v). *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  cardinality reals topology subtype_topology.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerNormInequalities InnerMetric
  InnerNormedTopology InnerCoordinateContinuity LinearBasis Bilinear TensorUP Hom HomInner
  HomInnerCoordinates HomSpaceTopology LinearGroupTopology TopologicalProductMaps AdjointUP
  Adjoint OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates
  TraceDefinition MetricSubsetBackground MetricProductBackground MetricSubsetSeparability
  InnerSpaceCountableBase CountableBaseDenseSet CompactCauchyLimits CompleteMetricUP
  MetricProductCompleteness HomCompositionDeterminant SubtypeCompactHausdorff AffineGroupTopology
  InnerMetricSeparability MetricProductSeparability.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section TopologyBackground.

(** Source for [closed_equalizer]: general topology supporting
    new:grass_compact: the set where two continuous maps into a Hausdorff
    space agree is closed. Supporting lemma. *)
Lemma closed_equalizer (X Y : topologicalType) (f g : X -> Y) :
  hausdorff_space Y -> continuous f -> continuous g -> closed [set x | f x = g x].
Proof.
move=> hY hf hg x hx; apply: hY => U V hU hV.
have hUV : nbhs x (f @^-1` U `&` g @^-1` V) by apply: filterI; [exact: hf | exact: hg].
have [z [hz1 [hzU hzV]]] := hx _ hUV.
by exists (f z); split=> //; rewrite hz1.
Qed.

End TopologyBackground.

Section Euclidean.
Variable R : realType.
Variables n k : nat.
Local Notation Rn := (R_n R n).
Local Notation Bn := (@euclidean_inner_product R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation hH := (hom_inner_productP hBn hBn hbn).
Local Notation HE := (inner_metric_space hH).
Local Notation tr := (@trace_Hom R (real_two_nonzero R) Rn (Finite.clone 'I_n _)
  (@coordinate_basis R n) hbn).
Local Notation ident := (hom_of_linear (linear_id Rn)).

(** Source for [orthogonal_projectors]: Allard 2.3, p. 421: G(n, k) as
    the set of orthogonal projections S of R^n onto k dimensional
    subspaces, characterized by S ∘ S = S, S^* = S and trace S = k;
    blueprint al:2.3 and new:grass_compact. Definition, as a subset of
    Hom(R^n, R^n) with the metric of Allard 2.2. *)
Definition orthogonal_projectors : set HE := [set S | is_orthogonal_projector hBn hbn k S].

(** Source for [projection_grassmann]: Allard 2.3, p. 421, "the Grassmann
    manifold G(n, k)", identified with [orthogonal_projectors] and metrised
    by |S - T| = ((S - T) • (S - T))^{1/2}, Allard 2.2. Definition. *)
Definition projection_grassmann : metricType R :=
  [the metricType R of @metric_subset R HE orthogonal_projectors].

(** Source for [projection_grassmannP]: Allard 2.3, p. 421: every member
    of G(n, k) is an orthogonal projector of rank k. Supporting lemma. *)
Lemma projection_grassmannP (S : projection_grassmann) :
  is_orthogonal_projector hBn hbn k (set_val S : Hom Rn Rn).
Proof. exact: set_valP S. Qed.

(** Source for [projection_grassmann_of]: Allard 2.3, p. 421: an
    orthogonal projector of rank k as a member of G(n, k). Definition. *)
Definition projection_grassmann_of (S : Hom Rn Rn) (hS : is_orthogonal_projector hBn hbn k S) :
  projection_grassmann := @exist HE (fun x => x \in orthogonal_projectors) S (mem_set hS).

(** Source for [projection_grassmann_ofE]: the underlying map of
    [projection_grassmann_of]. Supporting lemma. *)
Lemma projection_grassmann_ofE (S : Hom Rn Rn) (hS : is_orthogonal_projector hBn hbn k S) :
  set_val (projection_grassmann_of hS) = S.
Proof. by []. Qed.

(** Source for [projection_grassmann_ext]: members of G(n, k) are equal
    when the underlying maps are equal. Supporting lemma. *)
Lemma projection_grassmann_ext (S T : projection_grassmann) :
  (set_val S : Hom Rn Rn) = set_val T -> S = T.
Proof. exact: val_inj. Qed.

(** Source for [projection_grassmann_frame]: Allard 2.3, p. 421;
    blueprint al:2.3: for S ∈ G(n, k) there is an orthonormal family
    u_1, …, u_k of R^n with S(x) = Σ_i (x • u_i) u_i. Supporting
    restatement of [orthogonal_projector_frame]. *)
Lemma projection_grassmann_frame (S : projection_grassmann) :
  exists u : 'I_k -> Rn, orthonormal_family Bn u /\ (set_val S : Hom Rn Rn) = frame_projector hBn u.
Proof. exact/(orthogonal_projector_frame hBn hbn)/projection_grassmannP. Qed.

(** Source for [projection_grassmann_distanceE]: Allard 2.2, p. 421: the
    distance of S, T ∈ G(n, k) is |S - T|. Supporting lemma. *)
Lemma projection_grassmann_distanceE (S T : projection_grassmann) :
  mdist S T = hom_norm hBn hBn hbn ((set_val S : Hom Rn Rn) - set_val T).
Proof. by []. Qed.

(** Source for [hom_comp_diagonal_continuous]: continuity of
    [S ↦ S ∘ S] on Hom(R^n, R^n), Federer 2.7.16, p. 134; supporting
    new:grass_compact. Supporting lemma. *)
Lemma hom_comp_diagonal_continuous : continuous (fun S : HE => (hom_comp S S : HE)).
Proof.
move=> S.
have hd : continuous (fun T : HE => (T, T)).
  by apply: topological_pair_continuous=> T; exact: cvg_id.
exact: (continuous_comp (hd S) (@hom_composition_continuous R Rn Bn hBn n _ hbn (S, S))).
Qed.

(** Source for [hom_inner_continuous]: Federer 1.7.1, p. 28 (Cauchy's
    inequality): [S ↦ S • T] is continuous on Hom(R^n, R^n). Supporting
    lemma for new:grass_compact. *)
Lemma hom_inner_continuous (T : Hom Rn Rn) :
  continuous (fun S : HE => (hom_inner hBn hBn hbn S T : R^o)).
Proof.
have h := @inner_coordinate_continuous R _ _ hH T.
have he : (fun S : HE => (hom_inner hBn hBn hbn S T : R^o)) =
    (fun S : HE => inner_coordinate hH T S).
  by apply/funext=> S; rewrite inner_coordinateE.
by rewrite he.
Qed.

(** Source for [evaluation_hom_inner]: Allard 2.3(4), p. 422: S(x) • y =
    S • (ω · y) with ω = [v ↦ v • x]. Supporting lemma for
    new:grass_compact. *)
Lemma evaluation_hom_inner (S : Hom Rn Rn) x y :
  Bn (S x) y = hom_inner hBn hBn hbn S
    (rank_one_map (hom_of_linear (inner_coordinate hBn x)) y).
Proof.
rewrite (inner_symmetric hH) rank_one_map_hom_inner hom_of_linearE inner_coordinateE.
rewrite [RHS](inner_symmetric hBn).
exact: esym (inner_adjointP hBn hBn hbn (hom_as_linear S) x y).
Qed.

(** Source for [trace_hom_inner]: Allard 2.3(3), p. 422: trace S =
    1_{R^n} • S. Supporting lemma. *)
Lemma trace_hom_inner (S : Hom Rn Rn) : tr S = hom_inner hBn hBn hbn S ident.
Proof.
have [e [he ho]] := orthonormal_basis_exists_finite hBn hbn.
rewrite (trace_orthonormal hBn hbn he ho) (hom_inner_orthonormal_sum hBn hBn hbn he ho).
by apply: eq_bigr=> i _; rewrite hom_of_linearE.
Qed.

(** Source for [orthogonal_projectors_closed]: blueprint new:grass_compact:
    "the maps [S ↦ S ∘ S - S], [S ↦ S^* - S] and trace are continuous,
    hence G(n, k) is closed". Supporting lemma. *)
Lemma orthogonal_projectors_closed : closed orthogonal_projectors.
Proof.
pose T (x y : Rn) : Hom Rn Rn := rank_one_map (hom_of_linear (inner_coordinate hBn x)) y.
have -> : orthogonal_projectors =
    [set S : HE | (hom_comp S S : HE) = S] `&`
    (\bigcap_(x in [set: Rn]) \bigcap_(y in [set: Rn])
      [set S : HE | hom_inner hBn hBn hbn S (T x y) = hom_inner hBn hBn hbn S (T y x)]) `&`
    [set S : HE | hom_inner hBn hBn hbn S ident = k%:R].
  apply/seteqP; split=> S.
  - move=> [h1 h2 h3]; split; [split|].
    + exact: h1.
    + move=> x _ y _ /=; rewrite -!evaluation_hom_inner (adjoint_symmetric h2).
      by rewrite [LHS](inner_symmetric hBn).
    + rewrite /= -trace_hom_inner; exact: h3.
  - move=> [[h1 h2] h3]; split.
    + exact: h1.
    + apply: symmetric_adjoint=> x y.
      have := h2 x I y I; rewrite /= -!evaluation_hom_inner=> ->.
      by rewrite [LHS](inner_symmetric hBn).
    + by rewrite trace_hom_inner.
apply: closedI; first apply: closedI.
- apply: (@closed_equalizer HE HE (fun S : HE => (hom_comp S S : HE)) (fun S : HE => S)).
  + exact: hom_space_hausdorff.
  + exact: hom_comp_diagonal_continuous.
  + by move=> S; exact: cvg_id.
- apply: closed_bigI=> x _; apply: closed_bigI=> y _.
  apply: (@closed_equalizer HE R^o (fun S : HE => (hom_inner hBn hBn hbn S (T x y) : R^o))
    (fun S : HE => (hom_inner hBn hBn hbn S (T y x) : R^o))).
  + exact: Rhausdorff.
  + exact: hom_inner_continuous.
  + exact: hom_inner_continuous.
- apply: (@closed_equalizer HE R^o (fun S : HE => (hom_inner hBn hBn hbn S ident : R^o))
    (fun _ : HE => (k%:R : R^o))).
  + exact: Rhausdorff.
  + exact: hom_inner_continuous.
  + exact: cst_continuous.
Qed.

(** Source for [orthogonal_projectors_bounded]: blueprint new:grass_compact:
    "it is bounded since |S|^2 = k by 2.3(3)". Supporting lemma. *)
Lemma orthogonal_projectors_bounded :
  orthogonal_projectors `<=` [set S : HE | `|S - 0| <= Num.sqrt k%:R].
Proof.
move=> S hS; rewrite /= subr0 inner_norm_topologyE.
have [_ h2] := allard_2_3_3 hS.
rewrite -(ler_sqr (inner_norm_nonnegative hH S) (sqrtr_ge0 _)) sqr_sqrtr ?ler0n //.
by have -> : inner_norm hH S ^+ 2 = k%:R := h2.
Qed.

(** Source for [orthogonal_projectors_compact]: blueprint
    new:grass_compact: G(n, k) is a compact subset of Hom(R^n, R^n),
    by the Heine–Borel theorem (Federer 1.7.1, 2.7.16). Direct
    formalisation. *)
Theorem orthogonal_projectors_compact : compact orthogonal_projectors.
Proof.
apply: (subclosed_compact orthogonal_projectors_closed _ orthogonal_projectors_bounded).
exact: (@hom_space_closed_ball_compact R Rn Rn Bn Bn hBn hBn n _ hbn n _ hbn 0 (Num.sqrt k%:R)).
Qed.

(** Source for [projection_grassmann_compact]: blueprint new:grass_compact:
    the metric space G(n, k) is compact. Direct formalisation. *)
Theorem projection_grassmann_compact : compact [set: projection_grassmann].
Proof. exact: set_type_compact_whole orthogonal_projectors_compact. Qed.

(** Source for [projection_grassmann_hausdorff]: G(n, k) is a Hausdorff
    space, as a subspace of the metric space Hom(R^n, R^n). Supporting
    lemma for Allard 2.6 and 3.1. *)
Lemma projection_grassmann_hausdorff : hausdorff_space projection_grassmann.
Proof. exact: set_type_hausdorff (@hom_space_hausdorff R Rn Rn Bn Bn hBn hBn n _ hbn). Qed.

(** Source for [projection_grassmann_locally_compact]: G(n, k) is
    locally compact, being compact (blueprint new:grass_compact).
    Supporting lemma for Allard 2.6 and 3.1. *)
Lemma projection_grassmann_locally_compact : locally_compact [set: projection_grassmann].
Proof. exact: compact_space_locally_compact projection_grassmann_compact. Qed.

(** Source for [projection_grassmann_complete]: G(n, k) is a complete
    metric space, being compact. Supporting lemma for Allard 2.6. *)
Theorem projection_grassmann_complete : is_complete_metric_space projection_grassmann.
Proof. exact: compact_metric_space_complete projection_grassmann_compact. Qed.

(** Source for [projection_grassmann_separable]: G(n, k) is separable,
    as a subset of the finite dimensional space Hom(R^n, R^n). Supporting
    lemma for Allard 2.6. *)
Theorem projection_grassmann_separable :
  exists D : set projection_grassmann, countable D /\ dense D.
Proof.
have [U hU] := inner_space_countable_open_base hH (hom_rank_one_baseP hbn hbn).
have hsep := @countable_open_base_dense_set HE 0 U hU.
exact (@metric_subset_separable R HE orthogonal_projectors hsep).
Qed.

(** Source for [grassmann_bundle]: Allard 3.1: G_k(R^n) = R^n × G(n, k),
    the space on which k dimensional varifolds in R^n are Radon measures,
    with the maximum of the distances of the two factors. Definition. *)
Definition grassmann_bundle : metricType R :=
  [the metricType R of metric_product (inner_metric_space hBn) projection_grassmann].

(** Source for [grassmann_bundle_distanceE]: the distance of
    (x, S), (y, T) ∈ G_k(R^n) is max{|x - y|, |S - T|}. Supporting
    lemma. *)
Lemma grassmann_bundle_distanceE (p q : grassmann_bundle) :
  mdist p q = Order.max (mdist p.1 q.1) (mdist p.2 q.2).
Proof. by []. Qed.

(** Source for [grassmann_bundle_locally_compact]: G_k(R^n) = R^n × G(n, k)
    is locally compact, as required of the space on which varifolds are
    Radon measures, Allard 2.6 and 3.1. Supporting lemma. *)
Lemma grassmann_bundle_locally_compact : locally_compact [set: grassmann_bundle].
Proof.
apply: (@product_locally_compact (inner_metric_space hBn) projection_grassmann).
- exact: (@inner_space_locally_compact R Rn Bn hBn n _ hbn).
- exact: projection_grassmann_locally_compact.
Qed.

(** Source for [grassmann_bundle_separable]: G_k(R^n) = R^n × G(n, k)
    is separable, Allard 2.6 and 3.1. Supporting lemma. *)
Lemma grassmann_bundle_separable :
  exists D : set grassmann_bundle, countable D /\ dense D.
Proof.
apply: separable_metric_product.
- exact: (finite_inner_metric_separable hBn hbn).
- exact: projection_grassmann_separable.
Qed.
End Euclidean.

Arguments orthogonal_projectors R n k : clear implicits.
Arguments projection_grassmann R n k : clear implicits.
Arguments grassmann_bundle R n k : clear implicits.
