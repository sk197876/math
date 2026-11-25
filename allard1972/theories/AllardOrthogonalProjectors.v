(** Allard (1972), 2.3 and 2.3(1)–(5), printed pp. 421–422; blueprint labels
    al:2.3, al:2.3(1) and new:grass_compact (first assertion). Allard
    identifies a k dimensional subspace S of R^n with the orthogonal
    projection of R^n onto S, "characterized by the conditions S ∘ S = S,
    S^* = S and image S = S". Following the blueprint we work with the
    projections: for a finite dimensional inner product space V we call
    S ∈ Hom(V, V) an orthogonal projector of rank k if S ∘ S = S, S^* = S
    and trace S = k. The principal results of this module are

    - [orthogonal_projector_frame]: S is an orthogonal projector of rank k
      if and only if S(x) = Σ_{i<k} (x • u_i) u_i for x ∈ V and some
      orthonormal family u_1, …, u_k; in particular dim im S = k, see
      AllardGrassmannSubspaces.v for the comparison with Federer's G(n,k);
    - [allard_2_3_1] – [allard_2_3_5]: Allard's elementary observations;
    - [frame_projector_hom_inner]: f • S = Σ_{i<k} f(u_i) • u_i.

    Everything is stated for an arbitrary finite dimensional inner product
    space V with a basis b; Allard's G(n,k) is the case V = R^n, see
    AllardGrassmann.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm LinearBasis Bilinear TensorUP
  Hom HomInner HomInnerCoordinates AdjointUP AdjointLaws Adjoint OrthonormalFamilies
  OrthonormalParseval OrthonormalProjection FiniteSpans ModuleQuotient SubspaceCarrier
  GrassmannAbbreviations GrassmannSubspaces GrassmannHomogeneousSpace
  FiniteSubspaceBasisExistence OrthogonalMaps EuclideanInnerProduct FiniteCoordinates
  CoordinateProjection TraceDefinition GammaIntrinsic TraceCyclic.
From Allard Require Import AllardHomInnerProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [coordinate_basis_orthonormal]: Federer 1.7.1, p. 28: the
    standard basis of R^k is orthonormal for the inner product x • y =
    Σ_i x_i y_i of Allard 2.1, p. 420. Supporting lemma. *)
Lemma coordinate_basis_orthonormal (R : realType) k :
  orthonormal_family (@euclidean_inner_product R k) (@coordinate_basis R k).
Proof.
move=> i j; rewrite euclidean_inner_basis /coordinate_basis ffunE.
by rewrite eq_sym.
Qed.

Section Projectors.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation adj f := (hom_of_linear (inner_adjoint hB hB hb (hom_as_linear f))).
Local Notation tr := (@trace_Hom R (real_two_nonzero R) V (Finite.clone 'I_n _) b hb).
Local Notation ident := (hom_of_linear (linear_id V)).

(** Source for [is_orthogonal_projector]: Allard 2.3, p. 421: "S ∈
    Hom(R^n, R^n) is characterized by the conditions S ∘ S = S, S^* = S and
    image S = S"; blueprint al:2.3 and new:grass_compact, where the
    condition on the image is replaced by trace S = k. Definition. *)
Definition is_orthogonal_projector k (S : Hom V V) : Prop :=
  [/\ hom_comp S S = S, adj S = S & tr S = k%:R].

(** Source for [frame_projector]: the orthogonal projection
    [x ↦ Σ_{i<k} (x • u_i) u_i] onto the span of an orthonormal family
    u_1, …, u_k, Federer 1.7.1, p. 28, and 1.7.4, p. 30; blueprint al:2.3.
    Definition. *)
Definition frame_projector k (u : 'I_k -> V) : Hom V V :=
  hom_of_linear (GRing.Linear.clone _ _ _ _
    (@orthonormal_projection R V B hB (Finite.clone 'I_k _) u) _).

(** Source for [frame_projectorE]: the formula of [frame_projector],
    Federer 1.7.1, p. 28. Supporting lemma. *)
Lemma frame_projectorE k (u : 'I_k -> V) x :
  frame_projector u x = \sum_i B x (u i) *: u i.
Proof. by apply: eq_bigr=> i _; rewrite inner_coordinateE. Qed.

(** Source for [symmetric_adjoint]: Federer 1.7.4, p. 30: if S(x) • y =
    x • S(y) for x, y ∈ V, then S^* = S. Supporting lemma. *)
Lemma symmetric_adjoint (S : Hom V V) :
  (forall x y, B (S x) y = B x (S y)) -> adj S = S.
Proof.
move=> hs; apply: hom_ext=> y; rewrite hom_of_linearE.
apply: (adjoint_unique hB (inner_adjointP hB hB hb (hom_as_linear S))).
by move=> x z; rewrite hs.
Qed.

(** Source for [adjoint_symmetric]: Federer 1.7.4, p. 30: if S^* = S,
    then S(x) • y = x • S(y) for x, y ∈ V. Supporting lemma. *)
Lemma adjoint_symmetric (S : Hom V V) :
  adj S = S -> forall x y, B (S x) y = B x (S y).
Proof.
move=> hs x y; rewrite -(inner_adjointP hB hB hb (hom_as_linear S) x y).
by rewrite -[in RHS]hs hom_of_linearE.
Qed.

(** Source for [frame_projector_symmetric]: Federer 1.7.4, p. 30: the
    map [x ↦ Σ_i (x • u_i) u_i] is symmetric. Supporting lemma. *)
Lemma frame_projector_symmetric k (u : 'I_k -> V) x y :
  B (frame_projector u x) y = B x (frame_projector u y).
Proof.
rewrite !frame_projectorE (inner_suml hB) (inner_sumr hB); apply: eq_bigr=> i _.
rewrite (inner_scalel hB) (inner_scaler hB) (inner_symmetric hB (u i) y).
exact: mulrC.
Qed.

(** Source for [frame_projector_hom_inner]: Federer 1.7.9, p. 35: for an
    orthonormal family u_1, …, u_k and f ∈ Hom(V, V), f • S =
    Σ_i f(u_i) • u_i, where S is the orthogonal projection onto the span
    of u. Supporting lemma for Allard 2.4(1), p. 422. *)
Theorem frame_projector_hom_inner k (u : 'I_k -> V) (f : Hom V V) :
  hom_inner hB hB hb f (frame_projector u) = \sum_i B (f (u i)) (u i).
Proof.
have [e [he ho]] := orthonormal_basis_exists_finite hB hb.
rewrite (hom_inner_orthonormal_sum hB hB hb he ho).
have hs i : B (f (e i)) (frame_projector u (e i)) =
    \sum_l B (e i) (u l) * B (f (e i)) (u l).
  rewrite frame_projectorE (inner_sumr hB); apply: eq_bigr=> l _.
  exact: (inner_scaler hB).
under eq_bigr do rewrite hs.
rewrite exchange_big /=; apply: eq_bigr=> l _.
have hfu : f (u l) = \sum_i B (e i) (u l) *: f (e i).
  rewrite {1}(orthonormal_expansion hB he ho (u l)) linear_sum.
  by apply: eq_bigr=> i _; rewrite linearZ (inner_symmetric hB (u l)).
rewrite hfu (inner_suml hB); apply: eq_bigr=> i _.
by rewrite (inner_scalel hB).
Qed.

(** Source for [frame_projector_trace]: Federer 1.4.5, p. 21, and 1.7.1,
    p. 28: the orthogonal projection onto the span of an orthonormal family
    of k vectors has trace k; blueprint, proof of al:2.3(1). Supporting
    lemma. *)
Theorem frame_projector_trace k (u : 'I_k -> V) :
  orthonormal_family B u -> tr (frame_projector u) = k%:R.
Proof.
move=> hu.
have [e [he ho]] := orthonormal_basis_exists_finite hB hb.
rewrite (trace_orthonormal hB hb he ho).
have hs i : B (frame_projector u (e i)) (e i) = \sum_l B (u l) (e i) ^+ 2.
  rewrite frame_projectorE (inner_suml hB); apply: eq_bigr=> l _.
  by rewrite (inner_scalel hB) (inner_symmetric hB (e i)) expr2.
under eq_bigr do rewrite hs.
rewrite exchange_big /=.
have -> : \sum_l \sum_i B (u l) (e i) ^+ 2 = \sum_(l < k) (1 : R).
  apply: eq_bigr=> l _; rewrite -(orthonormal_parseval hB ho he) hu eqxx.
  by [].
by rewrite sumr_const card_ord.
Qed.

(** Source for [frame_projector_idempotent]: Federer 1.7.4, p. 30:
    S ∘ S = S for the orthogonal projection S onto the span of an
    orthonormal family. Supporting lemma. *)
Lemma frame_projector_idempotent k (u : 'I_k -> V) :
  orthonormal_family B u -> hom_comp (frame_projector u) (frame_projector u) = frame_projector u.
Proof.
move=> hu; apply: hom_ext=> x; rewrite hom_compE.
exact: (@orthonormal_projection_idempotent R V B hB (Finite.clone 'I_k _) u hu x).
Qed.

(** Source for [frame_projector_orthogonal_projector]: Allard 2.3, p. 421;
    blueprint al:2.3: the orthogonal projection onto the span of an
    orthonormal family of k vectors is an orthogonal projector of rank k.
    Supporting lemma. *)
Theorem frame_projector_orthogonal_projector k (u : 'I_k -> V) :
  orthonormal_family B u -> is_orthogonal_projector k (frame_projector u).
Proof.
move=> hu; split.
- exact: frame_projector_idempotent.
- apply: symmetric_adjoint; exact: frame_projector_symmetric.
- exact: frame_projector_trace.
Qed.

(** Source for [orthogonal_projector_symmetric]: Allard 2.3, p. 421:
    S(x) • y = x • S(y) whenever S^* = S. Supporting lemma. *)
Lemma orthogonal_projector_symmetric k (S : Hom V V) :
  is_orthogonal_projector k S -> forall x y, B (S x) y = B x (S y).
Proof. by move=> [_ hs _]; exact: adjoint_symmetric. Qed.

(** Source for [orthogonal_projector_idempotent]: Allard 2.3, p. 421:
    S(S(x)) = S(x). Supporting lemma. *)
Lemma orthogonal_projector_idempotent k (S : Hom V V) :
  is_orthogonal_projector k S -> forall x, S (S x) = S x.
Proof. by move=> [h _ _] x; have := congr1 (fun T : Hom V V => T x) h; rewrite hom_compE. Qed.

(** Source for [orthogonal_projector_frame]: blueprint al:2.3 and
    new:grass_compact (first assertion): S is an orthogonal projector of
    rank k if and only if there is an orthonormal family u_1, …, u_k with
    S(x) = Σ_i (x • u_i) u_i for x ∈ V. The proof follows the blueprint:
    im S has an orthonormal basis (Federer 1.6.3, 1.7.1), S and the
    projection onto its span are both characterised by the laws of
    Federer 1.7.4, p. 30, and the trace counts the members of the basis. *)
Theorem orthogonal_projector_frame k (S : Hom V V) :
  is_orthogonal_projector k S <->
  exists u : 'I_k -> V, orthonormal_family B u /\ S = frame_projector u.
Proof.
split; last first.
  by move=> [u [hu ->]]; exact: frame_projector_orthogonal_projector.
move=> hS; have [hS2 hSa hStr] := hS.
have hsym := orthogonal_projector_symmetric hS.
have hidem := orthogonal_projector_idempotent hS.
pose W := linear_image_subspace (hom_as_linear S).
have hWE y : subspace_mem W y <-> exists v, S v = y := linear_image_subspaceE _ y.
have [d [a [ha _]]] := finite_subspace_basis_exists hb W.
pose WG : G V d := GrassmannSubspace (ex_intro _ a ha : grassmann_pred d W).
have [j [hj himj]] := grassmann_orthogonal_frame (@euclidean_inner_productP R d) hB
  (@coordinate_basisP R d) WG.
pose u l := j (@coordinate_basis R d l).
have hu : orthonormal_family B u :=
  orthogonal_map_orthonormal hj (@coordinate_basis_orthonormal R d).
have hspan y : subspace_mem W y <-> in_finite_span u y.
  have h1 := orthogonal_injection_image_span (@coordinate_basisP R d) j y.
  have h2 := himj y.
  by split=> hy; [exact: (h1.1 (h2.1 hy)) | exact: (h2.2 (h1.2 hy))].
have hPS : S = frame_projector u.
  apply: (grassmann_projection_unique hB (W:=WG)); split.
  - by move=> x; apply/hWE; exists x.
  - move=> x w /hWE [v <-].
    rewrite -hsym.
    have -> : S (x - S x) = 0 by rewrite linearB /= hidem subrr.
    exact: (bil0l (inner_bilinear hB)).
  - move=> x; apply/hspan; rewrite frame_projectorE.
    by exists (fun i => B x (u i)).
  - move=> x w /hspan [c ->].
    rewrite (inner_sumr hB) big1 // => i _; rewrite (inner_scaler hB).
    have -> : B (x - frame_projector u x) (u i) = 0.
      exact: (@orthonormal_residual_orthogonal R V B hB (Finite.clone 'I_d _) u hu x i).
    exact: mulr0.
have hdk : d = k.
  apply/eqP; rewrite -(@eqr_nat R) -hStr hPS (frame_projector_trace hu).
  exact: eqxx.
subst d; by exists u.
Qed.

(** Source for [frame_projector_image]: Allard 2.3, p. 421: "image
    S = S": if S(x) = Σ_i (x • u_i) u_i for an orthonormal family u, then
    the image of S is the span of u. Supporting lemma. *)
Lemma frame_projector_image k (u : 'I_k -> V) y :
  orthonormal_family B u -> (exists x, frame_projector u x = y) <-> in_finite_span u y.
Proof.
move=> hu; split.
- move=> [x <-]; rewrite frame_projectorE; by exists (fun i => B x (u i)).
- move=> hy; exists y.
  exact: (@orthonormal_projection_fixed R V B hB k u hu y hy).
Qed.

Section Observations.
Variable k : nat.
Variable S : Hom V V.
Hypothesis hS : is_orthogonal_projector k S.

(** Source for [allard_2_3_1]: Allard 2.3(1), p. 422: "S(x) • S(y) =
    S(x) • y for x, y ∈ R^n". Direct formalisation for an orthogonal
    projector S of a finite dimensional inner product space. *)
Theorem allard_2_3_1 x y : B (S x) (S y) = B (S x) y.
Proof.
by rewrite -(orthogonal_projector_symmetric hS) (orthogonal_projector_idempotent hS).
Qed.

(** Source for [allard_2_3_2]: Allard 2.3(2), p. 422: "|S(x)|^2 = S(x) • x
    for x ∈ R^n". Direct formalisation. *)
Theorem allard_2_3_2 x : inner_norm hB (S x) ^+ 2 = B (S x) x.
Proof. by rewrite inner_norm_sqr allard_2_3_1. Qed.

(** Source for [allard_2_3_3]: Allard 2.3(3), p. 422: "1_{R^n} • S = k";
    blueprint al:2.3(1)(3): 1 • S = trace S = k = |S|^2. The equation
    trace S = k is part of [is_orthogonal_projector]. Direct
    formalisation. *)
Theorem allard_2_3_3 :
  hom_inner hB hB hb ident S = k%:R /\ hom_norm hB hB hb S ^+ 2 = k%:R.
Proof.
have [_ _ htr] := hS.
have [e [he ho]] := orthonormal_basis_exists_finite hB hb.
have ht := trace_orthonormal hB hb he ho S; rewrite htr in ht.
split.
- rewrite (hom_inner_orthonormal_sum hB hB hb he ho) ht; apply: eq_bigr=> i _.
  by rewrite hom_of_linearE (inner_symmetric hB).
- rewrite inner_norm_sqr (hom_inner_orthonormal_sum hB hB hb he ho) ht.
  by apply: eq_bigr=> i _; rewrite allard_2_3_1.
Qed.

(** Source for [allard_2_3_4]: Allard 2.3(4), p. 422: "(ω · v) • S =
    <S(v), ω> for ω ∈ Hom(R^n, R) and v ∈ R^n", with the rank-one map
    ω · v = [x ↦ ω(x) v] of AllardHomInnerProduct.v. Direct
    formalisation. *)
Theorem allard_2_3_4 (omega : Hom V R^o) v :
  hom_inner hB hB hb (rank_one_map omega v) S = omega (S v).
Proof.
have [_ hSa _] := hS.
rewrite rank_one_map_hom_inner; congr (hom_fun omega _).
by rewrite -[in RHS]hSa.
Qed.

(** Source for [allard_2_3_5]: Allard 2.3(5), p. 422: "f • S = f^* • S for
    f ∈ Hom(R^n, R^n)"; blueprint al:2.3(1)(5) adds the common value
    trace(f ∘ S). Direct formalisation. *)
Theorem allard_2_3_5 (f : Hom V V) :
  hom_inner hB hB hb f S = hom_inner hB hB hb (adj f) S /\
  hom_inner hB hB hb f S = tr (hom_comp f S).
Proof.
have hsym := orthogonal_projector_symmetric hS.
have [e [he ho]] := orthonormal_basis_exists_finite hB hb.
have h1 : hom_inner hB hB hb f S = tr (hom_comp S f).
  rewrite (hom_inner_orthonormal_sum hB hB hb he ho) (trace_orthonormal hB hb he ho).
  by apply: eq_bigr=> i _; rewrite hom_compE (inner_symmetric hB) hsym (inner_symmetric hB).
have h2 : hom_inner hB hB hb (adj f) S = tr (hom_comp f S).
  rewrite (hom_inner_orthonormal_sum hB hB hb he ho) (trace_orthonormal hB hb he ho).
  apply: eq_bigr=> i _; rewrite hom_compE hom_of_linearE (inner_symmetric hB).
  exact: (inner_adjointP hB hB hb (hom_as_linear f) (S (e i)) (e i)).
have h3 : tr (hom_comp S f) = tr (hom_comp f S) := trace_cyclic _ _ S f.
by rewrite h1 h2 h3.
Qed.
End Observations.
End Projectors.
