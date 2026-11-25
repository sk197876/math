(** Allard (1972), 2.2, printed p. 421, and the rank-one maps of 2.3(4),
    printed p. 422. Suppose V and W are finite dimensional inner product
    spaces. The space Hom(V,W) carries the inner product
    f • g = trace(f* ∘ g), the norm |f| = (f • f)^{1/2} and the operator
    norm ||f|| = sup{|f(v)| : v ∈ V, |v| ≤ 1}, with
    ||f|| ≤ |f| ≤ (dim V)^{1/2} ||f||. These are Federer's hom_inner,
    hom_norm and hom_operator_norm (Federer 1.7.6, 1.7.9); this module
    records the formulas in Allard's form, adds the orthonormal expansions
    used later, and introduces the rank-one map ω · b of Allard 2.3(4)
    (Allard [All72, 2.3(4)]) with the identity (ω · b) • A = ω(A*(b)). *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm LinearBasis Bilinear TensorUP Hom HomInner
  HomInnerTrace HomInnerCoordinates HomOperatorNorm HomSpaceTopology AdjointUP Adjoint
  GramSchmidt OrthonormalisationUP OrthonormalFamilies OrthonormalParseval
  OrthonormalBilinearCoordinates TraceDefinition GammaIntrinsic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_two_nonzero]: the hypothesis 1 + 1 ≠ 0 of the
    exterior algebra and trace of Federer 1.3–1.4, for the real field
    of Allard 2.1, p. 420. Supporting lemma. *)
Lemma real_two_nonzero (R : realType) : (1 + 1 : R) != 0.
Proof. by rewrite paddr_eq0 ?ler01 // oner_eq0. Qed.

Section OrthonormalBases.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.

(** Source for [inner_suml]: bilinearity of the inner product, Federer
    1.7.1, p. 27: (Σ_i x_i) • y = Σ_i x_i • y. Supporting lemma. *)
Lemma inner_suml (I : Type) (r : seq I) (P : pred I) (F : I -> V) y :
  B (\sum_(i <- r | P i) F i) y = \sum_(i <- r | P i) B (F i) y.
Proof.
exact: (big_morph (B ^~ y) (fun x x' => bilDl (inner_bilinear hB) x x' y)
  (bil0l (inner_bilinear hB) y)).
Qed.

(** Source for [inner_sumr]: bilinearity of the inner product, Federer
    1.7.1, p. 27: x • Σ_i y_i = Σ_i x • y_i. Supporting lemma. *)
Lemma inner_sumr (I : Type) (r : seq I) (P : pred I) (F : I -> V) x :
  B x (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) B x (F i).
Proof.
exact: (big_morph (B x) (bilDr (inner_bilinear hB) x) (bil0r (inner_bilinear hB) x)).
Qed.

(** Source for [inner_scalel]: Federer 1.7.1, p. 27: (a x) • y = a (x • y).
    Supporting lemma. *)
Lemma inner_scalel a x y : B (a *: x) y = a * B x y.
Proof. exact: (bilZl (inner_bilinear hB)). Qed.

(** Source for [inner_scaler]: Federer 1.7.1, p. 27: x • (a y) = a (x • y).
    Supporting lemma. *)
Lemma inner_scaler a x y : B x (a *: y) = a * B x y.
Proof. exact: (bilZr (inner_bilinear hB)). Qed.

Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.

(** Source for [orthonormal_basis_exists_finite]: the orthonormal bases of
    Federer 1.7.1, p. 28, used throughout Allard 2.2–2.4: every finite
    dimensional inner product space has an orthonormal basis with as many
    members as a given basis. Supporting lemma. *)
Lemma orthonormal_basis_exists_finite :
  exists e : 'I_n -> V, is_basis e /\ orthonormal_family B e.
Proof.
have [e [he ho]] := orthonormal_basis_exists hB hb.
by exists e; split=> //; exact: orthonormalisation_orthonormal ho.
Qed.

Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Hypothesis ho : orthonormal_family B e.

(** Source for [orthonormal_expansion]: Federer 1.7.1, p. 28: for an
    orthonormal basis e of V, x = Σ_i (x • e_i) e_i. Supporting lemma for
    Allard 2.2–2.4. *)
Lemma orthonormal_expansion x : x = \sum_i B x (e i) *: e i.
Proof.
rewrite {1}(orthonormal_basis_vector_expansion he x); apply: eq_bigr=> i _.
by rewrite (orthonormal_basis_inner_coordinate hB ho he).
Qed.

(** Source for [trace_orthonormal]: Federer 1.4.5, p. 21, and 1.7.1,
    p. 28: trace f = Σ_i f(e_i) • e_i for an orthonormal basis e of V,
    the trace being taken with any basis b. Supporting lemma for Allard
    2.2–2.3. *)
Lemma trace_orthonormal (f : Hom V V) :
  @trace_Hom R (real_two_nonzero R) V (Finite.clone 'I_n _) b hb f =
  \sum_i B (f (e i)) (e i).
Proof.
rewrite (@trace_basis_independent R (real_two_nonzero R) V (Finite.clone 'I_n _)
  (Finite.clone 'I_n _) b e hb he f) trace_HomE.
apply: eq_bigr=> i _; exact: (orthonormal_basis_inner_coordinate hB ho he).
Qed.
End OrthonormalBases.

Section HomInnerProduct.
Variable R : realType.
Variables V W : lmodType R.
Variables (B : V -> V -> R) (C : W -> W -> R).
Hypotheses (hB : is_inner_product B) (hC : is_inner_product C).
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation adj f := (inner_adjoint hB hC hb (hom_as_linear f)).
Local Notation tr := (@trace_Hom R (real_two_nonzero R) V (Finite.clone 'I_n _) b hb).

(** Source for [allard_2_2_hom_inner]: Allard 2.2, p. 421: "One defines an
    inner product on Hom(V, W) by setting f • g = trace f* ∘ g"; this is
    Federer's hom_inner, Federer 1.7.9, p. 35. Direct formalisation. *)
Theorem allard_2_2_hom_inner (f g : Hom V W) :
  hom_inner hB hC hb f g = tr (hom_of_linear (linear_comp (adj f) (hom_as_linear g))).
Proof. exact: hom_inner_trace. Qed.

(** Source for [allard_2_2_hom_norm]: Allard 2.2, p. 421: |f| = (f • f)^{1/2}
    for f ∈ Hom(V, W), Federer 1.7.9, p. 35. Direct formalisation. *)
Theorem allard_2_2_hom_norm (f : Hom V W) :
  hom_norm hB hC hb f = Num.sqrt (hom_inner hB hC hb f f).
Proof.
apply: inner_norm_value; first exact: sqrtr_ge0.
by rewrite sqr_sqrtr // (inner_nonnegative (hom_inner_productP hB hC hb)).
Qed.

(** Source for [allard_2_2_norm_comparison]: Allard 2.2, p. 421:
    "||f|| = sup{|f(v)| : v ∈ V and |v| ≤ 1} ... and take note of the
    inequalities ||f|| ≤ |f| ≤ ||f|| m^{1/2}", m = dim V; Federer 1.7.9,
    p. 35. Direct formalisation. *)
Theorem allard_2_2_norm_comparison (f : Hom V W) :
  hom_operator_norm hB hC hb f <= hom_norm hB hC hb f /\
  hom_norm hB hC hb f <= Num.sqrt n%:R * hom_operator_norm hB hC hb f.
Proof. exact: hom_operator_norm_comparison. Qed.

(** Source for [rank_one_map_fun]: Allard 2.3(4), p. 422, and the
    convention of Allard [All72, 2.3(4)]: for ω ∈ Hom(V, R) and y ∈ W,
    ω · y = [x ↦ ω(x) y]. Definition of the underlying function. *)
Definition rank_one_map_fun (omega : Hom V R^o) (y : W) (x : V) : W := (omega x : R) *: y.

(** Source for [rank_one_map_linear]: Allard 2.3(4), p. 422: ω · y is
    linear. Supporting lemma. *)
Lemma rank_one_map_linear (omega : Hom V R^o) (y : W) : linear (rank_one_map_fun omega y).
Proof.
move=> a x x'; rewrite /rank_one_map_fun.
have -> : (omega (a *: x + x') : R) = a * omega x + omega x' by rewrite (hom_linear omega).
by rewrite scalerDl scalerA.
Qed.

(** Source for [rank_one_map]: Allard 2.3(4), p. 422: the rank-one map
    ω · y ∈ Hom(V, W), (ω · y)(x) = ω(x) y. Definition. *)
Definition rank_one_map (omega : Hom V R^o) (y : W) : Hom V W :=
  HomMap (asboolT (@rank_one_map_linear omega y)).

(** Source for [rank_one_mapE]: Allard 2.3(4), p. 422: (ω · y)(x) =
    ω(x) y. Supporting lemma. *)
Lemma rank_one_mapE (omega : Hom V R^o) (y : W) x :
  rank_one_map omega y x = (omega x : R) *: y.
Proof. by []. Qed.

(** Source for [rank_one_map_hom_inner]: Allard 2.3(4), p. 422, and
    Allard [All72, 2.3(4)]: (ω · y) • A = ω(A*(y)) for ω ∈ Hom(V, R),
    y ∈ W and A ∈ Hom(V, W). Supporting lemma; 2.3(4) is its case
    A = S. *)
Theorem rank_one_map_hom_inner (omega : Hom V R^o) (y : W) (A : Hom V W) :
  hom_inner hB hC hb (rank_one_map omega y) A = omega (adj A y).
Proof.
have [e [he ho]] := orthonormal_basis_exists_finite hB hb.
rewrite (hom_inner_orthonormal_sum hB hC hb he ho).
rewrite [in RHS](orthonormal_expansion hB he ho (adj A y)) linear_sum.
apply: eq_bigr=> i _; rewrite rank_one_mapE linearZ (bilZl (inner_bilinear hC)).
rewrite (inner_symmetric hC).
have -> : C (A (e i)) y = B (e i) (adj A y).
  exact: esym (inner_adjointP hB hC hb (hom_as_linear A) (e i) y).
rewrite (inner_symmetric hB); exact: mulrC.
Qed.
End HomInnerProduct.
