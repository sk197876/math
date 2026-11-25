(** Blueprint label new:projection_formula (supporting Allard (1972), 3.2,
    printed p. 427, and DDG Lemma A.1). Suppose L ∈ Hom(R^n, R^p) and
    S ∈ Hom(R^n, R^n) satisfies S ∘ S = S and S^* = S. Set

        A = S ∘ L^* ∘ L ∘ S + 1_{R^n} - S,    P = L ∘ S ∘ A^{-1} ∘ L^*.

    If L | im S is injective, then A is invertible, A ∘ S = S ∘ A and P is
    the orthogonal projection of R^p onto L[im S]; if moreover S ∈ G(n, k),
    then P ∈ G(p, k), and L | im S is injective if and only if
    ||∧_k(L ∘ S)|| > 0. The continuity of [(L, S) ↦ P] is proved in
    AllardProjectionContinuity.v.

    The inverse A^{-1} is the inversion of Federer's linear group of R^n
    (Federer 2.7.16, p. 134; LinearGroupSealed.v), so no new chosen object
    is introduced; P therefore depends on a proof that A is injective.
    The adjoint of L is Federer's euclidean_rectangular_adjoint (1.7.4). *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  topology subtype_topology normedtype.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerMetric InnerNormedTopology
  LinearBasis Bilinear TensorUP Hom HomInner HomInnerCoordinates AdjointUP AdjointLaws Adjoint
  AdjointCriteria OrthonormalFamilies OrthonormalParseval OrthogonalMaps OrthonormalFrameMap
  GrassmannAbbreviations GrassmannSubspaces GrassmannHomogeneousSpace EuclideanInnerProduct
  FiniteCoordinates EuclideanRectangularAdjoint EuclideanLinearMaps EuclideanLinearJacobian
  LinearGroupTopology LinearGroupSealed OrthogonalInjectionSpaces TopologicalProductMaps
  NormMetricScaleContinuity MetricSubsetBackground ModuleQuotient SubspaceCarrier.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann
  AllardGrassmannSubspaces AllardJacobians.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Algebra.
Variable R : realType.
Variables n p : nat.
Local Notation Rn := (R_n R n).
Local Notation Rp := (R_n R p).
Local Notation Bn := (@euclidean_inner_product R n).
Local Notation Bp := (@euclidean_inner_product R p).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hBp := (@euclidean_inner_productP R p).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation adjL L := (euclidean_rectangular_adjoint L).
Local Notation idn := (hom_of_linear (linear_id Rn)).

(** Source for [projection_formula_operator]: blueprint
    new:projection_formula: A = S ∘ L^* ∘ L ∘ S + 1_{R^n} - S for
    L ∈ Hom(R^n, R^p) and S ∈ Hom(R^n, R^n). Definition. *)
Definition projection_formula_operator (L : Hom Rn Rp) (S : Hom Rn Rn) : Hom Rn Rn :=
  hom_comp S (hom_comp (adjL L) (hom_comp L S)) + idn - S.

(** Source for [projection_formula_operatorE]: A(x) = S(L^*(L(S(x)))) + x
    - S(x). Supporting lemma. *)
Lemma projection_formula_operatorE (L : Hom Rn Rp) (S : Hom Rn Rn) x :
  projection_formula_operator L S x = S (adjL L (L (S x))) + x - S x.
Proof. by []. Qed.

Section Symmetric.
Variable L : Hom Rn Rp.
Variable S : Hom Rn Rn.
Hypothesis hidem : forall x, S (S x) = S x.
Hypothesis hsym : forall x y, Bn (S x) y = Bn x (S y).
Local Notation A := (projection_formula_operator L S).

(** Source for [projection_formula_operator_S]: blueprint
    new:projection_formula: A ∘ S = S ∘ L^* ∘ L ∘ S. Supporting lemma. *)
Lemma projection_formula_operator_S x : A (S x) = S (adjL L (L (S x))).
Proof. by rewrite projection_formula_operatorE !hidem addrK. Qed.

(** Source for [projection_formula_operator_commute]: blueprint
    new:projection_formula: "Both A ∘ S and S ∘ A equal
    S ∘ L^* ∘ L ∘ S, hence A ∘ S = S ∘ A". Direct formalisation. *)
Lemma projection_formula_operator_commute x : A (S x) = S (A x).
Proof.
rewrite projection_formula_operator_S projection_formula_operatorE linearB linearD /=.
by rewrite !hidem addrK.
Qed.

(** Source for [projection_formula_operator_symmetric]: blueprint
    new:projection_formula: A^* = A. Supporting lemma. *)
Lemma projection_formula_operator_symmetric x y : Bn (A x) y = Bn x (A y).
Proof.
rewrite !projection_formula_operatorE.
rewrite (bilBl (inner_bilinear hBn)) (bilDl (inner_bilinear hBn)).
rewrite (bilBr (inner_bilinear hBn)) (bilDr (inner_bilinear hBn)).
have h1 : Bn (S (adjL L (L (S x)))) y = Bp (L (S x)) (L (S y)).
  rewrite hsym (inner_symmetric hBn) euclidean_rectangular_adjoint_pairing.
  by rewrite [LHS](inner_symmetric hBp).
have h2 : Bn x (S (adjL L (L (S y)))) = Bp (L (S x)) (L (S y)).
  by rewrite -hsym euclidean_rectangular_adjoint_pairing.
by rewrite h1 h2 hsym.
Qed.

(** Source for [projection_formula_operator_kernel]: blueprint
    new:projection_formula: "Suppose A(x) = 0. Then ... x = S(x) and
    0 = |L(x)|^2". Supporting lemma. *)
Lemma projection_formula_operator_kernel x : A x = 0 -> S x = x /\ L x = 0.
Proof.
move=> h0.
have h1 : S (adjL L (L (S x))) = 0.
  by rewrite -projection_formula_operator_S projection_formula_operator_commute h0 linear0.
have hSx : S x = x.
  move: h0; rewrite projection_formula_operatorE h1 add0r=> /eqP.
  by rewrite subr_eq0=> /eqP h; exact: esym h.
split=> //.
have : Bp (L (S x)) (L (S x)) = 0.
  rewrite -euclidean_rectangular_adjoint_pairing hsym h1.
  exact: (bil0r (inner_bilinear hBn)).
by move/eqP; rewrite (inner_self_eq0 hBp) hSx=> /eqP.
Qed.

(** Source for [projection_formula_operator_injective]: blueprint
    new:projection_formula: A is invertible if and only if L | im S is
    injective. Direct formalisation (the blueprint proves the direction
    needed; the converse is immediate). *)
Theorem projection_formula_operator_injective :
  injective A <-> (forall x, S x = x -> L x = 0 -> x = 0).
Proof.
split.
- move=> hA x hSx hLx; apply: hA.
  by rewrite linear0 projection_formula_operatorE hSx hLx !linear0 add0r subrr.
- move=> h x y hxy.
  have : A (x - y) = 0.
    have -> : A (x - y) = A x - A y := linearB (hom_as_linear A) x y.
    by rewrite hxy subrr.
  move/projection_formula_operator_kernel=> [hS hL].
  by apply/eqP; rewrite -subr_eq0; apply/eqP; exact: h hS hL.
Qed.
End Symmetric.

Section Inverse.
Variable L : Hom Rn Rp.
Variable S : Hom Rn Rn.
Hypothesis hA : injective (projection_formula_operator L S).
Local Notation A := (projection_formula_operator L S).

(** Source for [projection_formula_operator_group]: blueprint
    new:projection_formula: A as a member of the linear group of R^n,
    Federer 2.7.16, p. 134. Definition. *)
Definition projection_formula_operator_group : set_type (linear_group hBn hbn) :=
  @exist (inner_metric_space (hom_inner_productP hBn hBn hbn))
    (fun f => f \in linear_group hBn hbn) A (mem_set hA).

(** Source for [projection_formula_inverse]: blueprint
    new:projection_formula: A^{-1}, the inverse of A in the linear group
    of R^n, Federer 2.7.16, p. 134 (LinearGroupSealed.v). Definition. *)
Definition projection_formula_inverse : Hom Rn Rn :=
  set_val (linear_group_inv hBn hbn projection_formula_operator_group).

(** Source for [projection_formula_map]: blueprint new:projection_formula:
    P = L ∘ S ∘ A^{-1} ∘ L^*. Definition. *)
Definition projection_formula_map : Hom Rp Rp :=
  hom_comp L (hom_comp S (hom_comp projection_formula_inverse (adjL L))).

(** Source for [projection_formula_mapE]: P(y) = L(S(A^{-1}(L^*(y)))).
    Supporting lemma. *)
Lemma projection_formula_mapE y :
  projection_formula_map y = L (S (projection_formula_inverse (adjL L y))).
Proof. by []. Qed.

(** Source for [projection_formula_inverseK]: A^{-1} ∘ A = 1_{R^n},
    Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma projection_formula_inverseK x : projection_formula_inverse (A x) = x.
Proof.
have h := linear_group_invE (linear_group_operations hBn hbn) projection_formula_operator_group.
have := congr1 (fun T : Hom Rn Rn => T x) h.
by rewrite hom_compE hom_identityE.
Qed.

(** Source for [projection_formula_inverseKV]: A ∘ A^{-1} = 1_{R^n},
    Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma projection_formula_inverseKV y : A (projection_formula_inverse y) = y.
Proof.
have h := linear_group_invE_right (linear_group_operations hBn hbn)
  projection_formula_operator_group.
have := congr1 (fun T : Hom Rn Rn => T y) h.
by rewrite hom_compE hom_identityE.
Qed.

Hypothesis hidem : forall x, S (S x) = S x.
Hypothesis hsym : forall x y, Bn (S x) y = Bn x (S y).
Local Notation Ainv := projection_formula_inverse.
Local Notation P := projection_formula_map.

(** Source for [projection_formula_inverse_commute]: blueprint
    new:projection_formula: A^{-1} ∘ S = S ∘ A^{-1}. Supporting lemma. *)
Lemma projection_formula_inverse_commute x : Ainv (S x) = S (Ainv x).
Proof.
rewrite -{1}(projection_formula_inverseKV x) -projection_formula_operator_commute //.
exact: projection_formula_inverseK.
Qed.

(** Source for [projection_formula_inverse_symmetric]: blueprint
    new:projection_formula: A^{-1} is symmetric, because A is.
    Supporting lemma. *)
Lemma projection_formula_inverse_symmetric x y : Bn (Ainv x) y = Bn x (Ainv y).
Proof.
rewrite -{1}(projection_formula_inverseKV y) -projection_formula_operator_symmetric //.
by rewrite projection_formula_inverseKV.
Qed.

(** Source for [projection_formula_map_symmetric]: blueprint
    new:projection_formula: "P^* = L ∘ A^{-1} ∘ S ∘ L^* = P". Direct
    formalisation. *)
Theorem projection_formula_map_symmetric x y : Bp (P x) y = Bp x (P y).
Proof.
rewrite !projection_formula_mapE -euclidean_rectangular_adjoint_pairing hsym.
rewrite projection_formula_inverse_symmetric projection_formula_inverse_commute.
rewrite (inner_symmetric hBn) euclidean_rectangular_adjoint_pairing.
by rewrite [LHS](inner_symmetric hBp).
Qed.

(** Source for [projection_formula_map_fixed]: blueprint
    new:projection_formula: "P ∘ L ∘ S = L ∘ S ∘ A^{-1} ∘ A ∘ S = L ∘ S".
    Direct formalisation. *)
Theorem projection_formula_map_fixed x : P (L (S x)) = L (S x).
Proof.
rewrite projection_formula_mapE -projection_formula_inverse_commute.
by rewrite -projection_formula_operator_S // projection_formula_inverseK.
Qed.

(** Source for [projection_formula_map_idempotent]: blueprint
    new:projection_formula: P ∘ P = P. Direct formalisation. *)
Theorem projection_formula_map_idempotent y : P (P y) = P y.
Proof. exact: projection_formula_map_fixed (Ainv (adjL L y)). Qed.

(** Source for [projection_formula_map_image]: blueprint
    new:projection_formula: im P = L[im S]. Direct formalisation. *)
Theorem projection_formula_map_image y : (exists z, P z = y) <-> (exists x, L (S x) = y).
Proof.
split.
- by move=> [z <-]; exists (Ainv (adjL L z)).
- by move=> [x <-]; exists (L (S x)); exact: projection_formula_map_fixed.
Qed.
End Inverse.
End Algebra.

Section Rank.
Variable R : realType.
Variables n p k : nat.
Local Notation Rn := (R_n R n).
Local Notation Rp := (R_n R p).
Local Notation Rk := (R_n R k).
Local Notation Bn := (@euclidean_inner_product R n).
Local Notation Bp := (@euclidean_inner_product R p).
Local Notation Bk := (@euclidean_inner_product R k).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hBp := (@euclidean_inner_productP R p).
Local Notation hBk := (@euclidean_inner_productP R k).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation hbp := (@coordinate_basisP R p).
Local Notation hbk := (@coordinate_basisP R k).

(** Source for [orthogonal_projector_frame_map]: Allard 2.4, p. 422;
    blueprint al:2.4: an orthogonal projector S of rank k factors as
    S = j ∘ j^* with an orthogonal injection j of R^k into R^n, and
    S ∘ j = j. Supporting lemma. *)
Lemma orthogonal_projector_frame_map (S : Hom Rn Rn) :
  is_orthogonal_projector hBn hbn k S ->
  exists u : 'I_k -> Rn, exists j : {linear Rk -> Rn},
    [/\ orthonormal_family Bn u, S = frame_projector hBn u, is_orthogonal_map Bk Bn j,
        forall l, j (@coordinate_basis R k l) = u l &
        (forall x, S x = j (inner_adjoint hBk hBn hbk j x)) /\ (forall a, S (j a) = j a)].
Proof.
move=> hS; have [u [hu hSu]] := (orthogonal_projector_frame hBn hbn k S).1 hS.
have [j [hj hju]] := orthonormal_frame_map_exists hBn hu.
have hSj x : S x = j (inner_adjoint hBk hBn hbk j x).
  by rewrite hSu; exact: frame_projector_factor hju x.
have hk := proj1 (orthogonal_iff_adjoint_left_inverse hBk (inner_adjointP hBk hBn hbk j)) hj.
exists u, j; split=> //; split=> // a.
by rewrite hSj; congr (j _); exact: hk a.
Qed.

(** Source for [projection_formula_jacobian]: blueprint
    new:projection_formula: "if dim im S = k, then L | im S is injective
    if and only if ∧_k(L ∘ S) ≠ 0", stated with the norm
    ||∧_k(L ∘ S)|| of Federer 3.2.1. Direct formalisation. *)
Theorem projection_formula_jacobian (L : Hom Rn Rp) (S : Hom Rn Rn) :
  is_orthogonal_projector hBn hbn k S ->
  0 < euclidean_linear_jacobian k (hom_comp L S) <-> (forall x, S x = x -> L x = 0 -> x = 0).
Proof.
move=> hS; have [u [j [hu hSu hj hju [hSj hjS]]]] := orthogonal_projector_frame_map hS.
have hjinj : injective j := orthogonal_map_injective hBk hBn hj.
rewrite {1}hSu (jacobian_frame_projector_factor L hj hju) euclidean_linear_jacobian_top_positive.
split.
- move=> hinj x hx hLx.
  have hx' : x = j (inner_adjoint hBk hBn hbk j x) by rewrite -{1}hx hSj.
  have h0 : inner_adjoint hBk hBn hbk j x = 0.
    have e1 : hom_comp L (hom_of_linear j) (inner_adjoint hBk hBn hbk j x) = L x.
      by rewrite hom_compE hom_of_linearE -hx'.
    by apply: hinj; rewrite e1 hLx linear0.
  by rewrite hx' h0 linear0.
- move=> h a b hab.
  have hz : j (a - b) = 0.
    apply: h; first exact: hjS.
    rewrite !linearB /=; apply/eqP; rewrite subr_eq0; apply/eqP.
    by move: hab; rewrite !hom_compE !hom_of_linearE.
  by apply/eqP; rewrite -subr_eq0; apply/eqP; apply: hjinj; rewrite hz linear0.
Qed.

(** Source for [projection_formula_operator_injective_jacobian]: blueprint
    new:projection_formula: for S ∈ G(n, k), A is invertible if and only
    if ||∧_k(L ∘ S)|| > 0. Supporting lemma. *)
Lemma projection_formula_operator_injective_jacobian (L : Hom Rn Rp) (S : Hom Rn Rn) :
  is_orthogonal_projector hBn hbn k S ->
  injective (projection_formula_operator L S) <-> 0 < euclidean_linear_jacobian k (hom_comp L S).
Proof.
move=> hS; rewrite (projection_formula_jacobian L hS).
exact: (projection_formula_operator_injective L (orthogonal_projector_idempotent hS)
  (orthogonal_projector_symmetric hS)).
Qed.

(** Source for [projection_formula_orthogonal_projector]: blueprint
    new:projection_formula: if S ∈ G(n, k) and L | im S is injective,
    then P is the orthogonal projection of R^p onto the k dimensional
    subspace L[im S], hence P ∈ G(p, k). Direct formalisation. *)
Theorem projection_formula_orthogonal_projector (L : Hom Rn Rp) (S : Hom Rn Rn)
    (hS : is_orthogonal_projector hBn hbn k S)
    (hA : injective (projection_formula_operator L S)) :
  is_orthogonal_projector hBp hbp k (projection_formula_map hA).
Proof.
have hidem := orthogonal_projector_idempotent hS.
have hsym := orthogonal_projector_symmetric hS.
have [u [j [hu hSu hj hju [hSj hjS]]]] := orthogonal_projector_frame_map hS.
have hinjS := (projection_formula_operator_injective L hidem hsym).1 hA.
pose Lj := GRing.Linear.clone _ _ _ _ (linear_comp (hom_as_linear L) j) _.
have hLj : injective Lj.
  move=> a b hab.
  have hz : j (a - b) = 0.
    apply: hinjS; first exact: hjS.
    rewrite !linearB /=; apply/eqP; rewrite subr_eq0; apply/eqP; exact: hab.
  apply/eqP; rewrite -subr_eq0; apply/eqP.
  by apply: (orthogonal_map_injective hBk hBn hj); rewrite hz linear0.
pose W : G Rp k := linear_image_grassmann hbk hLj.
have hW y : grassmann_val W y <-> exists a, L (j a) = y := linear_image_grassmannE hbk hLj y.
pose P := projection_formula_map hA.
have hPW : is_grassmann_projection Bp W P.
  split.
  - move=> y; apply/hW.
    exists (inner_adjoint hBk hBn hbk j (projection_formula_inverse hA
      (euclidean_rectangular_adjoint L y))).
    by rewrite -hSj.
  - move=> y w /hW [a <-].
    have hfix : P (L (j a)) = L (j a).
      by rewrite -{1 2}(hjS a); exact: projection_formula_map_fixed.
    rewrite -hfix -(projection_formula_map_symmetric hA hidem hsym).
    have -> : P (y - P y) = P y - P (P y) := linearB (hom_as_linear P) y (P y).
    by rewrite (projection_formula_map_idempotent hA hidem) subrr (bil0l (inner_bilinear hBp)).
suff -> : projection_formula_map hA = grassmann_projection hBk hBp hbk W.
  exact: grassmann_projection_orthogonal_projector.
exact: esym (grassmann_projection_unique hBp (grassmann_projectionP hBk hBp hbk W) hPW).
Qed.
End Rank.
