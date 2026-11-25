(** Allard (1972), 2.4 and 2.4(1), printed p. 422; blueprint labels al:2.4
    and al:2.4(1). For f ∈ Hom(R^n, R^p) and S ∈ G(n, k) with an
    orthonormal basis u_1, …, u_k of im S, the k dimensional Jacobian
    ||∧_k(f ∘ S)|| of Federer 3.2.1 (euclidean_linear_jacobian) equals
    |f(u_1) ∧ ⋯ ∧ f(u_k)| ([allard_2_4]), and its square is the Gram
    determinant Σ_σ sign(σ) Π_i f(u_σ(i)) • f(u_i) ([allard_2_4_gram]).
    From this we derive Allard 2.4(1),

        d/dt ||∧_k((1_{R^n} + t f) ∘ S)|| at t = 0 equals f • S,

    for f ∈ Hom(R^n, R^n) ([allard_2_4_1]). The derivative is the actual
    two-sided derivative of Federer 2.9.19 (has_real_curve_derivative). *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm boolp reals ring.
From mathcomp Require Import classical_sets functions topology.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm LinearBasis Bilinear TensorUP
  Hom HomInner AdjointUP Adjoint OrthonormalFamilies OrthogonalMaps OrthonormalFrameMap
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates EuclideanLinearMaps
  ExteriorGrading ExteriorMaps ExteriorMapScaling ExteriorOperatorEstimate InnerExterior
  InnerExteriorPositivity ExteriorNorm ExteriorOperatorNorm OperatorNormUP OperatorNormLaws
  TopExteriorNorm FiniteExteriorPowers ExteriorProjectionNorm EuclideanLinearJacobian
  EuclideanFrameJacobian InnerExteriorProducts ExteriorFrameUnitNorm InversionCount
  PermutationDeterminant RealCurveDerivativeUP RealCurveDerivativeLaws
  RealCurveDerivativeAlgebra RealCurvePolynomialDerivatives SignedSquareRootDerivative
  PuncturedRealLinearLimits.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section CurveDerivatives.
Variable R : realType.
Local Notation D := (@has_real_curve_derivative R).

(** Source for [real_curve_derivative_constant]: Federer 2.9.19, p. 163:
    a constant function has derivative 0. Supporting lemma for Allard
    2.4(1). *)
Lemma real_curve_derivative_constant (c x : R) : D (fun=> c) x 0.
Proof.
apply: (punctured_real_limit_congr _ (punctured_real_constant_limit (0 : R)))=> h _.
by rewrite subrr mul0r.
Qed.

(** Source for [real_curve_derivative_add]: Federer 2.9.19, p. 163: the
    derivative of a sum is the sum of the derivatives. Supporting lemma
    for Allard 2.4(1). *)
Lemma real_curve_derivative_add (f g : R -> R) (x a b : R) :
  D f x a -> D g x b -> D (fun t => f t + g t) x (a + b).
Proof.
move=> hf hg; apply: (punctured_real_limit_congr _ (punctured_real_limit_add hf hg))=> h _.
rewrite -mulrDl; congr (_ * _); ring.
Qed.

(** Source for [real_curve_derivative_sum]: Federer 2.9.19, p. 163: the
    derivative of a finite sum is the sum of the derivatives. Supporting
    lemma for Allard 2.4(1). *)
Lemma real_curve_derivative_sum (I : Type) (r : seq I) (F : I -> R -> R) (v : I -> R) (x : R) :
  (forall i, D (F i) x (v i)) -> D (fun t => \sum_(i <- r) F i t) x (\sum_(i <- r) v i).
Proof.
move=> hF; elim: r=> [|i r IH].
  have -> : (fun t => \sum_(i <- [::]) F i t) = (fun=> 0) by apply/funext=> t; rewrite big_nil.
  by rewrite big_nil; exact: real_curve_derivative_constant.
have -> : (fun t => \sum_(j <- i :: r) F j t) = (fun t => F i t + \sum_(j <- r) F j t).
  by apply/funext=> t; rewrite big_cons.
by rewrite big_cons; exact: real_curve_derivative_add.
Qed.

(** Source for [real_curve_derivative_prod_exists]: Federer 2.9.19,
    p. 163: a finite product of differentiable functions is
    differentiable. Supporting lemma for Allard 2.4(1). *)
Lemma real_curve_derivative_prod_exists (I : Type) (r : seq I) (P : pred I) (F : I -> R -> R)
    (x : R) :
  (forall i, exists v, D (F i) x v) -> exists v, D (fun t => \prod_(i <- r | P i) F i t) x v.
Proof.
move=> hF; elim: r=> [|i r [w hw]].
  exists 0.
  have -> : (fun t => \prod_(i <- [::] | P i) F i t) = (fun=> 1) by apply/funext=> t; rewrite big_nil.
  exact: real_curve_derivative_constant.
case hi : (P i).
- have [v hv] := hF i.
  have -> : (fun t => \prod_(j <- i :: r | P j) F j t) = (fun t => F i t * \prod_(j <- r | P j) F j t).
    by apply/funext=> t; rewrite big_cons hi.
  by eexists; exact: real_curve_derivative_product hv hw.
- have -> : (fun t => \prod_(j <- i :: r | P j) F j t) = (fun t => \prod_(j <- r | P j) F j t).
    by apply/funext=> t; rewrite big_cons hi.
  by exists w.
Qed.

(** Source for [real_curve_derivative_prod_one]: Federer 2.9.19, p. 163,
    and the product rule: if F_i(x) = 1 for every i, the derivative of
    Π_i F_i at x is Σ_i F_i'(x). Supporting lemma for Allard 2.4(1). *)
Lemma real_curve_derivative_prod_one (I : Type) (r : seq I) (F : I -> R -> R) (v : I -> R)
    (x : R) :
  (forall i, F i x = 1) -> (forall i, D (F i) x (v i)) ->
  D (fun t => \prod_(i <- r) F i t) x (\sum_(i <- r) v i).
Proof.
move=> h1 hF; elim: r=> [|i r IH].
  have -> : (fun t => \prod_(i <- [::]) F i t) = (fun=> 1) by apply/funext=> t; rewrite big_nil.
  by rewrite big_nil; exact: real_curve_derivative_constant.
have -> : (fun t => \prod_(j <- i :: r) F j t) = (fun t => F i t * \prod_(j <- r) F j t).
  by apply/funext=> t; rewrite big_cons.
have hP := real_curve_derivative_product (hF i) IH.
cbv beta in hP.
rewrite h1 big1 ?mulr1 ?mul1r in hP; last by move=> j _; exact: h1.
by rewrite big_cons.
Qed.

(** Source for [real_curve_derivative_prod_two_zero]: Federer 2.9.19,
    p. 163, and the product rule: if two distinct factors vanish at x,
    the derivative of the product at x is 0. Supporting lemma for Allard
    2.4(1). *)
Lemma real_curve_derivative_prod_two_zero (I : eqType) (r : seq I) (F : I -> R -> R) (x : R)
    (i0 i1 : I) :
  uniq r -> i0 \in r -> i1 \in r -> i0 != i1 -> F i0 x = 0 -> F i1 x = 0 ->
  (forall i, exists v, D (F i) x v) -> D (fun t => \prod_(i <- r) F i t) x 0.
Proof.
move=> hu h0r h1r hne h0 h1 hF.
pose r' := [seq i <- r | i != i0].
have h1r' : i1 \in r' by rewrite mem_filter eq_sym hne h1r.
have hu' : uniq r' := filter_uniq _ hu.
have -> : (fun t => \prod_(i <- r) F i t) =
    (fun t => F i0 t * (F i1 t * \prod_(i <- r' | i != i1) F i t)).
  by apply/funext=> t; rewrite (bigD1_seq i0) // -big_filter (bigD1_seq i1).
have [w hw] := real_curve_derivative_prod_exists r' (fun i => i != i1) hF.
have [v0 hv0] := hF i0; have [v1 hv1] := hF i1.
have hP := real_curve_derivative_product hv0 (real_curve_derivative_product hv1 hw).
cbv beta in hP.
by rewrite h0 h1 !mul0r mulr0 addr0 in hP.
Qed.

(** Source for [real_curve_derivative_quadratic]: Federer 2.9.19, p. 163:
    the derivative of [t ↦ a + t b + t^2 c] at 0 is b. Supporting lemma
    for Allard 2.4(1). *)
Lemma real_curve_derivative_quadratic (a b c : R) :
  D (fun t => a + t * b + t ^+ 2 * c) 0 b.
Proof.
have hid : punctured_real_limit (fun h : R => h) 0.
  by move=> e he; exists e; split=> // h /andP [_ hh]; rewrite subr0.
have hL := punctured_real_limit_add (punctured_real_constant_limit b)
  (punctured_real_limit_scale c hid).
rewrite mulr0 addr0 in hL.
apply: (punctured_real_limit_congr _ hL)=> h hh /=.
by field.
Qed.
End CurveDerivatives.

Section Jacobians.
Variable R : realType.
Variables n p k : nat.
Local Notation h2 := (euclidean_two_nonzero R).
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
Local Notation hbk := (@coordinate_basisP R k).

(** Source for [frame_projector_factor]: Allard 2.4, p. 422; blueprint
    al:2.4: if j ∈ Hom(R^k, R^n) maps the standard basis to u_1, …, u_k,
    then Σ_i (x • u_i) u_i = j(j^*(x)), that is S = j ∘ j^*. Supporting
    lemma. *)
Lemma frame_projector_factor (u : 'I_k -> Rn) (j : {linear Rk -> Rn}) :
  (forall l, j (@coordinate_basis R k l) = u l) ->
  forall x, frame_projector hBn u x = j (inner_adjoint hBk hBn hbk j x).
Proof.
move=> hju x; rewrite frame_projectorE.
set a := inner_adjoint hBk hBn hbk j x.
rewrite (orthonormal_expansion hBk hbk (@coordinate_basis_orthonormal R k) a) linear_sum.
apply: eq_bigr=> l _; rewrite linearZ /= hju; congr (_ *: _).
rewrite (inner_symmetric hBk) /a (inner_adjointP hBk hBn hbk j) hju.
by rewrite [LHS](inner_symmetric hBn).
Qed.

(** Source for [jacobian_frame_projector_factor]: Allard 2.4, p. 422;
    blueprint al:2.4: if j ∈ Hom(R^k, R^n) is an orthogonal injection with
    j(e_l) = u_l for l = 1, …, k and S = Σ_l (· • u_l) u_l = j ∘ j^*, then
    ||∧_k(f ∘ S)|| = ||∧_k(f ∘ j)||, since ∧_k(j^* ) contracts lengths
    and ∧_k(j^* ) ∘ ∧_k j = 1, Federer 1.7.6–1.7.7, pp. 33–34.
    Supporting lemma. *)
Lemma jacobian_frame_projector_factor (L : Hom Rn Rp) (u : 'I_k -> Rn) (j : {linear Rk -> Rn}) :
  is_orthogonal_map Bk Bn j -> (forall l, j (@coordinate_basis R k l) = u l) ->
  euclidean_linear_jacobian k (hom_comp L (frame_projector hBn u)) =
  euclidean_linear_jacobian k (hom_comp L (hom_of_linear j)).
Proof.
move=> hj hju.
pose a := inner_adjoint hBk hBn hbk j.
have ha : is_adjoint Bk Bn j a := inner_adjointP hBk hBn hbk j.
have hp : is_orthogonal_projection Bn Bk a by exists j; split.
pose T := hom_comp L (hom_of_linear j).
pose xi0 := e_lambda (@coordinate_basis R k) (ord_tuple k).
have hxi0 : exterior_norm h2 hBk xi0 = 1 := euclidean_top_product_unit_norm h2 k.
have hTval : euclidean_linear_jacobian k T =
    exterior_norm h2 hBp (exterior_power_map (hom_as_linear T) k xi0).
  exact: (top_exterior_operator_unit_value hBp hbk (hom_as_linear T) hxi0).
have hfac y : exterior_power_map (hom_as_linear (hom_comp L (frame_projector hBn u))) k y =
    exterior_power_map (hom_as_linear T) k (exterior_power_map a k y).
  rewrite exterior_power_map_composition; apply: exterior_power_map_ext=> x.
  transitivity (L (frame_projector hBn u x)); first exact: hom_compE.
  rewrite (frame_projector_factor hju).
  exact: (esym (hom_compE L (hom_of_linear j) (a x))).
apply: (operator_norm_unique (exterior_operator_normP h2 hBn hBp hbn _ k)); split.
- move=> y hy; rewrite hfac.
  apply: (le_trans (operator_norm_vector_bound
    (exterior_operator_normP h2 hBk hBp hbk (hom_as_linear T) k) _)).
  rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l.
    exact: euclidean_linear_jacobian_nonnegative.
  exact: (le_trans (exterior_projection_norm_bound h2 hBn hBk hp y) hy).
- exists (exterior_power_map j k xi0); split.
  + have -> : inner_norm (exterior_inner_productP h2 hBn k) (exterior_power_map j k xi0) = 1.
      exact: (eq_trans (exterior_orthogonal_norm h2 hBk hBn hj xi0) hxi0).
    exact: lexx.
  + rewrite hfac (exterior_adjoint_retraction hBk ha hj); exact: esym hTval.
Qed.

(** Source for [allard_2_4]: Allard 2.4, p. 422; blueprint al:2.4: for
    f ∈ Hom(R^n, R^p) and an orthonormal family u_1, …, u_k spanning
    im S, S = Σ_i (· • u_i) u_i, one has ||∧_k(f ∘ S)|| =
    |f(u_1) ∧ ⋯ ∧ f(u_k)|. Direct formalisation of the second equality
    of Allard 2.4; see docs/divergences.md for the other two. *)
Theorem allard_2_4 (L : Hom Rn Rp) (u : 'I_k -> Rn) :
  orthonormal_family Bn u ->
  euclidean_linear_jacobian k (hom_comp L (frame_projector hBn u)) =
  exterior_norm h2 hBp (e_lambda (fun i => L (u i)) (ord_tuple k)).
Proof.
move=> hu.
have [j [hj hju]] := orthonormal_frame_map_exists hBn hu.
rewrite (jacobian_frame_projector_factor L hj hju).
rewrite euclidean_frame_jacobian !exterior_map_indexed_product.
congr (exterior_norm _ _ (e_lambda _ _)); apply/funext=> i; by rewrite /= hju.
Qed.

(** Source for [allard_2_4_gram]: Allard 2.4, p. 422; blueprint al:2.4:
    ||∧_k(f ∘ S)||^2 = Σ_σ sign(σ) Π_i f(u_σ(i)) • f(u_i), the Leibniz
    expansion of det((f ∘ j)^* ∘ f ∘ j), Federer 1.7.5, p. 32. Direct
    formalisation of the last equality of Allard 2.4 in Leibniz form. *)
Theorem allard_2_4_gram (L : Hom Rn Rp) (u : 'I_k -> Rn) :
  orthonormal_family Bn u ->
  euclidean_linear_jacobian k (hom_comp L (frame_projector hBn u)) ^+ 2 =
  \sum_(s : 'S_k) FedererPermutation.index R s * \prod_(i <- enum 'I_k) Bp (L (u (s i))) (L (u i)).
Proof.
move=> hu; rewrite allard_2_4 // exterior_norm_square exterior_inner_product_permutations.
apply: eq_bigr=> s _; congr (_ * _).
by rewrite foldrE big_map.
Qed.


End Jacobians.

Section Derivative.
Variable R : realType.
Variables n k : nat.
Local Notation h2 := (euclidean_two_nonzero R).
Local Notation Rn := (R_n R n).
Local Notation Bn := (@euclidean_inner_product R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).

(** Source for [euclidean_inner_curve]: Allard 2.4(1), p. 422: for
    x, y, z, w ∈ R^n, (x + t y) • (z + t w) = x • z + t (y • z + x • w)
    + t^2 (y • w). Supporting lemma. *)
Lemma euclidean_inner_curve (x y z w : Rn) (t : R) :
  Bn (x + t *: y) (z + t *: w) = Bn x z + t * (Bn y z + Bn x w) + t ^+ 2 * Bn y w.
Proof.
rewrite (bilDl (inner_bilinear hBn)) !(bilDr (inner_bilinear hBn)).
rewrite !(inner_scalel hBn) !(inner_scaler hBn).
ring.
Qed.

(** Source for [allard_2_4_1]: Allard 2.4(1), p. 422: "d/dt
    ||∧_k((1_{R^n} + t f) ∘ S)|| at t = 0 equals f • S whenever
    f ∈ Hom(R^n, R^n) and S ∈ G(n, k)". Direct formalisation, with the
    two-sided derivative of Federer 2.9.19, p. 163. *)
Theorem allard_2_4_1 (f : Hom Rn Rn) (S : projection_grassmann R n k) :
  has_real_curve_derivative
    (fun t => euclidean_linear_jacobian k
      (hom_comp (hom_of_linear (linear_id Rn) + t *: f) (set_val S : Hom Rn Rn))) 0
    (hom_inner hBn hBn hbn f (set_val S)).
Proof.
have [u [hu hSu]] := projection_grassmann_frame S.
rewrite hSu (frame_projector_hom_inner hBn hbn).
pose v (t : R) (i : 'I_k) : Rn := u i + t *: f (u i).
pose g (t : R) := \sum_(s : 'S_k) FedererPermutation.index R s *
  \prod_(i <- enum 'I_k) Bn (v t (s i)) (v t i).
have hv t : (fun i => (hom_of_linear (linear_id Rn) + t *: f) (u i)) = v t.
  by apply/funext=> i; rewrite hom_addE hom_scaleE hom_of_linearE.
have hgJ t : g t = euclidean_linear_jacobian k
    (hom_comp (hom_of_linear (linear_id Rn) + t *: f) (frame_projector hBn u)) ^+ 2.
  by rewrite (@allard_2_4_gram R n n k _ u hu) /g; apply: eq_bigr=> s _; congr (_ * _).
have hphi t : euclidean_linear_jacobian k
    (hom_comp (hom_of_linear (linear_id Rn) + t *: f) (frame_projector hBn u)) = Num.sqrt (g t).
  rewrite hgJ sqrtr_sqr ger0_norm //.
  exact: euclidean_linear_jacobian_nonnegative.
rewrite (_ : (fun t => _) = (fun t => Num.sqrt (g t))); last by apply/funext=> t; exact: hphi.
have hg0 : g 0 = 1.
  rewrite hgJ (@allard_2_4 R n n k _ u hu) hv.
  have -> : v 0 = u by apply/funext=> i; rewrite /v scale0r addr0.
  by rewrite (orthonormal_product_unit_norm h2 hBn hu) expr1n.
pose c (i : 'I_k) := Bn (f (u i)) (u i) + Bn (u i) (f (u i)).
have hfac a b : has_real_curve_derivative (fun t => Bn (v t a) (v t b)) 0
    (Bn (f (u a)) (u b) + Bn (u a) (f (u b))).
  rewrite (_ : (fun t => _) = (fun t => Bn (u a) (u b) + t * (Bn (f (u a)) (u b) +
      Bn (u a) (f (u b))) + t ^+ 2 * Bn (f (u a)) (f (u b)))).
    exact: real_curve_derivative_quadratic.
  by apply/funext=> t; rewrite /v euclidean_inner_curve.
have hval a b : Bn (v 0 a) (v 0 b) = if a == b then 1 else 0.
  by rewrite /v !scale0r !addr0; exact: hu.
have hterm (s : 'S_k) : has_real_curve_derivative
    (fun t => \prod_(i <- enum 'I_k) Bn (v t (s i)) (v t i)) 0
    (if s == 1%g then \sum_(i <- enum 'I_k) c i else 0).
  case: eqP=> [->|hs].
    apply: real_curve_derivative_prod_one=> i; first by rewrite perm1 hval eqxx.
    by rewrite perm1; exact: hfac.
  have [i0 hi0] : exists i0, s i0 != i0.
    apply/existsP; apply: contra_notT hs; rewrite negb_exists=> /forallP h.
    by apply/permP=> i; rewrite perm1; apply/eqP; exact: negbNE (h i).
  apply: (real_curve_derivative_prod_two_zero (i0 := i0) (i1 := s i0)).
  - exact: enum_uniq.
  - exact: mem_enum.
  - exact: mem_enum.
  - by rewrite eq_sym.
  - by rewrite hval (negbTE hi0).
  - rewrite hval; case: eqP=> // h.
    by move: hi0; rewrite (perm_inj h) eqxx.
  - by move=> i; eexists; exact: hfac.
have hg : has_real_curve_derivative g 0 (\sum_(i <- enum 'I_k) c i).
  have hsum := @real_curve_derivative_sum R {perm 'I_k} (index_enum {perm 'I_k})
    (fun s t => FedererPermutation.index R s * \prod_(i <- enum 'I_k) Bn (v t (s i)) (v t i))
    (fun s => FedererPermutation.index R s * (if s == 1%g then \sum_(i <- enum 'I_k) c i else 0))
    0 (fun s => real_curve_derivative_scale (FedererPermutation.index R s) (hterm s)).
  have h0 : \sum_(s : 'S_k | s != 1%g) FedererPermutation.index R s *
      (if s == 1%g then \sum_(i <- enum 'I_k) c i else 0) = 0.
    by apply: big1=> s hs; rewrite (negbTE hs) mulr0.
  by rewrite (bigD1 1%g) //= h0 addr0 eqxx (index_one h2) mul1r in hsum.
have hsq : has_real_curve_derivative Num.sqrt (g 0) (2 * Num.sqrt (g 0))^-1.
  by apply: positive_square_root_real_derivative; rewrite hg0 ltr01.
have hc := real_curve_derivative_compose hg hsq.
have e1 : \sum_(i <- enum 'I_k) c i = \sum_i c i by rewrite big_enum.
have hC : \sum_(i <- enum 'I_k) c i = (\sum_i Bn (f (u i)) (u i)) *+ 2.
  rewrite e1 -sumrMnl; apply: eq_bigr=> i _.
  by rewrite /c (inner_symmetric hBn (u i)) mulr2n.
have h2' : (2 : R) != 0 by rewrite pnatr_eq0.
rewrite hg0 sqrtr1 mulr1 hC in hc.
by rewrite -(mulr_natl (\sum_i Bn (f (u i)) (u i)) 2) mulrAC (divff h2') mul1r in hc.
Qed.
End Derivative.
