(** Allard (1972), 2.3, printed p. 421: "We will make no distinction
    between a k dimensional subspace S of R^n and the orthogonal
    projection of R^n onto S"; blueprint label al:2.3. This module proves
    that the identification is a bijection between Federer's Grassmann
    manifold G(V, k) of 1.6.2, p. 24 (the k dimensional subspaces,
    GrassmannSubspaces.G), and the orthogonal projectors of rank k of
    AllardOrthogonalProjectors.v. A subspace W is sent to the orthogonal
    projection P_W of Federer 1.7.4, p. 30 (grassmann_projection), and a
    projector S to its image im S. For V = R^n the bijection is a
    homeomorphism between Federer's topological space G(n, k) of 2.7.16,
    p. 139 (euclidean_grassmann_space, with the initial topology of
    W ↦ P_W), and Allard's metric space [projection_grassmann R n k] of
    AllardGrassmann.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals topology subtype_topology.
From Federer Require Import InnerProductUP InnerProductLaws InnerMetric LinearBasis Bilinear
  TensorUP Hom HomInner OrthonormalFamilies OrthonormalProjection FiniteSpans ModuleQuotient
  SubspaceCarrier SubspaceEquality GrassmannAbbreviations GrassmannSubspaces
  GrassmannHomogeneousSpace OrthogonalMaps OrthonormalFrameMap EuclideanInnerProduct
  FiniteCoordinates EuclideanOrthogonalInvariantMeasures MetricSubsetBackground.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Subspaces.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable k : nat.
Local Notation hBk := (@euclidean_inner_productP R k).
Local Notation hbk := (@coordinate_basisP R k).
Local Notation P W := (grassmann_projection hBk hB hbk W).

(** Source for [grassmann_orthonormal_frame]: Federer 1.6.2, p. 24, and
    1.7.1, p. 28: every W ∈ G(V, k) is the span of an orthonormal family
    u_1, …, u_k. Supporting lemma for Allard 2.3, p. 421. *)
Lemma grassmann_orthonormal_frame (W : G V k) :
  exists u : 'I_k -> V, orthonormal_family B u /\
    forall y, grassmann_val W y <-> in_finite_span u y.
Proof.
have [j [hj himj]] := grassmann_orthogonal_frame hBk hB hbk W.
exists (fun l => j (@coordinate_basis R k l)); split.
  exact: (orthogonal_map_orthonormal hj (@coordinate_basis_orthonormal R k)).
move=> y; have h1 := orthogonal_injection_image_span hbk j y.
have h2 := himj y.
by split=> hy; [exact: (h1.1 (h2.1 hy)) | exact: (h2.2 (h1.2 hy))].
Qed.

(** Source for [frame_projector_grassmann]: Federer 1.7.4, p. 30: if W is
    the span of an orthonormal family u, then [x ↦ Σ_i (x • u_i) u_i]
    satisfies the laws of the orthogonal projection onto W. Supporting
    lemma for Allard 2.3, p. 421. *)
Lemma frame_projector_grassmann (W : G V k) (u : 'I_k -> V) :
  orthonormal_family B u -> (forall y, grassmann_val W y <-> in_finite_span u y) ->
  is_grassmann_projection B W (frame_projector hB u).
Proof.
move=> hu hspan; split.
- move=> x; apply/hspan; rewrite frame_projectorE.
  by exists (fun i => B x (u i)).
- move=> x w /hspan [c ->].
  rewrite (inner_sumr hB) big1 // => i _; rewrite (inner_scaler hB).
  have -> : B (x - frame_projector hB u x) (u i) = 0.
    exact: (@orthonormal_residual_orthogonal R V B hB (Finite.clone 'I_k _) u hu x i).
  exact: mulr0.
Qed.

(** Source for [grassmann_projection_orthogonal_projector]: Allard 2.3,
    p. 421: the orthogonal projection P_W of V onto W ∈ G(V, k) (Federer
    1.7.4, p. 30) satisfies P_W ∘ P_W = P_W, P_W^* = P_W and
    trace P_W = k. Direct formalisation. *)
Theorem grassmann_projection_orthogonal_projector (W : G V k) :
  is_orthogonal_projector hB hb k (P W).
Proof.
have [u [hu hspan]] := grassmann_orthonormal_frame W.
have -> : P W = frame_projector hB u.
  apply: (grassmann_projection_unique hB (grassmann_projectionP hBk hB hbk W)).
  exact: frame_projector_grassmann hu hspan.
exact: (frame_projector_orthogonal_projector hB hb hu).
Qed.

(** Source for [orthogonal_projector_image_pred]: Allard 2.3, p. 421:
    the image of an orthogonal projector S of rank k is k dimensional,
    Federer 1.6.2, p. 24. Supporting lemma. *)
Lemma orthogonal_projector_image_pred (S : Hom V V) :
  is_orthogonal_projector hB hb k S -> grassmann_pred k (linear_image_subspace (hom_as_linear S)).
Proof.
move=> hS; have [u [hu hSu]] := (orthogonal_projector_frame hB hb k S).1 hS.
have [j [hj hju]] := orthonormal_frame_map_exists hB hu.
have hjinj : injective j := orthogonal_map_injective hBk hB hj.
have -> : linear_image_subspace (hom_as_linear S) = linear_image_subspace j.
  apply: subspace_ext=> y.
  have h1 := orthogonal_injection_image_span hbk j y.
  have hu' : (fun i => j (@coordinate_basis R k i)) = u by apply/funext=> i; exact: hju.
  rewrite hu' in h1.
  have h2 : (exists x, frame_projector hB u x = y) <-> in_finite_span u y :=
    frame_projector_image hB y hu.
  split=> hy.
  - apply/(linear_image_subspaceE j y)/h1/h2.
    have [x hx] := (linear_image_subspaceE (hom_as_linear S) y).1 hy.
    by exists x; rewrite -hSu.
  - apply/(linear_image_subspaceE (hom_as_linear S) y).
    have [x hx] := h2.2 (h1.1 ((linear_image_subspaceE j y).1 hy)).
    by exists x; rewrite /= hSu.
exact: (linear_image_grassmann_pred hbk hjinj).
Qed.

(** Source for [orthogonal_projector_image]: Allard 2.3, p. 421, "image
    S = S": the image of an orthogonal projector S of rank k as a member
    of G(V, k), Federer 1.6.2, p. 24. Definition. *)
Definition orthogonal_projector_image (S : Hom V V) (hS : is_orthogonal_projector hB hb k S) :
  G V k := GrassmannSubspace (orthogonal_projector_image_pred hS).

(** Source for [orthogonal_projector_imageE]: the members of im S are
    the vectors S(x). Supporting lemma. *)
Lemma orthogonal_projector_imageE (S : Hom V V) (hS : is_orthogonal_projector hB hb k S) y :
  grassmann_val (orthogonal_projector_image hS) y <-> exists x, S x = y.
Proof. exact: linear_image_subspaceE. Qed.

(** Source for [orthogonal_projector_image_projection]: Allard 2.3,
    p. 421: im P_W = W for W ∈ G(V, k). Direct formalisation of one half
    of the identification. *)
Theorem orthogonal_projector_image_projection (W : G V k) :
  orthogonal_projector_image (grassmann_projection_orthogonal_projector W) = W.
Proof.
apply: grassmann_ext=> y; rewrite orthogonal_projector_imageE; split.
- by move=> [x <-]; exact: (grassmann_projectionP hBk hB hbk W).1.
- by move=> hy; exists y; exact: grassmann_projection_fixed.
Qed.

(** Source for [grassmann_projection_image]: Allard 2.3, p. 421: an
    orthogonal projector S of rank k is the orthogonal projection onto
    its image, P_{im S} = S. Direct formalisation of the other half of
    the identification. *)
Theorem grassmann_projection_image (S : Hom V V) (hS : is_orthogonal_projector hB hb k S) :
  P (orthogonal_projector_image hS) = S.
Proof.
have hsym := orthogonal_projector_symmetric hS.
have hidem := orthogonal_projector_idempotent hS.
apply: (grassmann_projection_unique hB (grassmann_projectionP hBk hB hbk _)); split.
- by move=> x; apply/orthogonal_projector_imageE; exists x.
- move=> x w /orthogonal_projector_imageE [v <-].
  rewrite -hsym.
  have -> : S (x - S x) = 0 by rewrite linearB /= hidem subrr.
  exact: (bil0l (inner_bilinear hB)).
Qed.
End Subspaces.

Section Euclidean.
Variable R : realType.
Variables n k : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation hBk := (@euclidean_inner_productP R k).
Local Notation hbk := (@coordinate_basisP R k).
Local Notation HE := (inner_metric_space (hom_inner_productP hBn hBn hbn)).
Local Notation GF := (euclidean_grassmann_space R n k).
Local Notation GA := (projection_grassmann R n k).

(** Source for [subspace_projector]: Allard 2.3, p. 421: a k dimensional
    subspace W of R^n regarded as the orthogonal projection P_W ∈ G(n, k);
    here W ranges over Federer's G(n, k) of 1.6.2, p. 24, and 2.7.16,
    p. 139. Definition. *)
Definition subspace_projector (W : GF) : GA :=
  projection_grassmann_of (grassmann_projection_orthogonal_projector hBn hbn W).

(** Source for [subspace_projectorE]: the underlying map of
    [subspace_projector W] is P_W, Federer 1.7.4, p. 30. Supporting
    lemma. *)
Lemma subspace_projectorE (W : GF) :
  (set_val (subspace_projector W) : Hom Rn Rn) = grassmann_projection hBk hBn hbk W.
Proof. by []. Qed.

(** Source for [projector_subspace]: Allard 2.3, p. 421: S ∈ G(n, k)
    regarded as the k dimensional subspace im S, a member of Federer's
    G(n, k) of 1.6.2, p. 24. Definition. *)
Definition projector_subspace (S : GA) : GF :=
  orthogonal_projector_image (projection_grassmannP S).

(** Source for [projector_subspaceE]: the members of
    [projector_subspace S] are the vectors S(x). Supporting lemma. *)
Lemma projector_subspaceE (S : GA) y :
  grassmann_val (projector_subspace S) y <-> exists x, (set_val S : Hom Rn Rn) x = y.
Proof. exact: orthogonal_projector_imageE. Qed.

(** Source for [projector_subspaceK]: Allard 2.3, p. 421: im P_W = W.
    Direct formalisation. *)
Theorem projector_subspaceK : cancel subspace_projector projector_subspace.
Proof.
move=> W; apply: grassmann_ext=> y; rewrite projector_subspaceE subspace_projectorE.
have h := congr1 (fun W' : G Rn k => grassmann_val W' y)
  (orthogonal_projector_image_projection hBn hbn W).
by rewrite -h; exact: (orthogonal_projector_imageE (grassmann_projection_orthogonal_projector hBn hbn W) y).
Qed.

(** Source for [subspace_projectorK]: Allard 2.3, p. 421: S is the
    orthogonal projection onto im S. Direct formalisation. *)
Theorem subspace_projectorK : cancel projector_subspace subspace_projector.
Proof.
move=> S; apply: projection_grassmann_ext; rewrite subspace_projectorE.
exact: grassmann_projection_image.
Qed.

(** Source for [subspace_projector_continuous]: W ↦ P_W is continuous
    from Federer's G(n, k) of 2.7.16, p. 139, to Allard's G(n, k), by the
    definition of Federer's topology. Supporting lemma. *)
Lemma subspace_projector_continuous : continuous subspace_projector.
Proof.
apply: (@continuous_comp_initial _ _ _ (@set_val HE (orthogonal_projectors R n k))).
exact: (@grassmann_space_projection_continuous R (R_n R k) Rn _ _ hBk hBn k _ n _ hbk hbn).
Qed.

(** Source for [projector_subspace_continuous]: S ↦ im S is continuous
    from Allard's G(n, k) to Federer's G(n, k) of 2.7.16, p. 139: its
    composition with W ↦ P_W is the inclusion of G(n, k) into
    Hom(R^n, R^n). Supporting lemma. *)
Lemma projector_subspace_continuous : continuous projector_subspace.
Proof.
apply: (@continuous_comp_initial _ _ _
  (fun W : grassmann_carrier Rn k => (grassmann_projection hBk hBn hbk W : HE))).
have -> : (fun W : grassmann_carrier Rn k => (grassmann_projection hBk hBn hbk W : HE))
    \o projector_subspace = (fun S : GA => (set_val S : HE)).
  apply/funext=> S /=; have := subspace_projectorK S.
  by move/(congr1 (@set_val HE (orthogonal_projectors R n k))).
exact: metric_subset_inclusion_continuous.
Qed.

(** Source for [allard_2_3_identification]: Allard 2.3, p. 421: "We will
    make no distinction between a k dimensional subspace S of R^n and the
    orthogonal projection of R^n onto S". The map W ↦ P_W is a
    homeomorphism of Federer's G(n, k) (1.6.2, p. 24, and 2.7.16, p. 139)
    onto Allard's G(n, k). Direct formalisation. *)
Theorem allard_2_3_identification :
  [/\ cancel subspace_projector projector_subspace,
      cancel projector_subspace subspace_projector,
      continuous subspace_projector & continuous projector_subspace].
Proof.
split; [exact: projector_subspaceK | exact: subspace_projectorK |
  exact: subspace_projector_continuous | exact: projector_subspace_continuous].
Qed.
End Euclidean.

Arguments subspace_projector R n k : clear implicits.
Arguments projector_subspace R n k : clear implicits.
