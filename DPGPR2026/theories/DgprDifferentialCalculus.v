(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    section 3, proof of lem:ibp (DPGPR (3.17)): supporting rules of the
    differential calculus of Federer 3.1.1, pp. 209-210, and 3.1.11,
    pp. 220-222, for maps on R^n whose differentials are given by their
    values: sums, products with real functions, continuous linear
    postcomposition, coordinates, and the rule
    D[x ↦ A(x)(u(x))](a)(v) = DA(a)(v)(u(a)) + A(a)(Du(a)(v)). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm HilbertFormCompactness FiniteCoordinates LinearBasis
  FiniteDualDimension EuclideanCoordinateMetric EuclideanTraceContinuity
  NormDifferentialUP NormDifferentialLocal NormDifferentialLinear NormDifferentialArithmetic
  NormDifferentialScalarProduct NormDifferentialFiniteCalculus NormHigherCurveDerivativeUP
  ProductInnerDifferential NormClassOneUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Calculus.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NR := (fun t : R^o => `|t|).
Local Notation hNR := (@scalar_absolute_value_norm R).
Local Notation eps := (@coordinate_basis R n).

(** Source for [dgpr_coordinate_expansion]: Federer 1.1.2, p. 10: each
    vector of R^n is the sum of its coordinates times the standard basis
    vectors. *)
Lemma dgpr_coordinate_expansion (y : X) : y = \sum_i y i *: eps i.
Proof.
apply/ffunP=> j; rewrite sum_ffunE (bigD1 j) //= big1 => [|i hij].
- by rewrite !ffunE eqxx addr0; change (y j = y j * 1); rewrite mulr1.
- by rewrite !ffunE eq_sym (negbTE hij) scaler0.
Qed.

(** Source for [dgpr_coordinate_sum]: Federer 1.1.2, p. 10: for a linear
    map L on R^n, sum_i y_i L(eps_i) = L(y). *)
Lemma dgpr_coordinate_sum (Z : lmodType R) (L : Hom X Z) (y : X) :
  \sum_i y i *: L (eps i) = L y.
Proof.
by rewrite [in RHS](dgpr_coordinate_expansion y) linear_sum; apply: eq_bigr=> i _; rewrite linearZ.
Qed.

Variables (Z : lmodType R) (NZ : Z -> R).
Hypothesis hNZ : is_real_norm NZ.

(** Source for [dgpr_differential_values]: Federer 3.1.1, p. 209: f is
    differentiable at a and its differential Df(a) satisfies
    Df(a)(v) = l(v) for v in R^n. *)
Definition dgpr_differential_values (f : X -> Z) (a : X) (l : X -> Z) :=
  exists L : Hom X Z, has_norm_differential NX NZ setT f a L /\ forall v, L v = l v.

(** Source for [dgpr_values_ext]: Federer 3.1.1, p. 209: the
    differential depends only on the function and on its values. *)
Lemma dgpr_values_ext (f g : X -> Z) (a : X) (l l' : X -> Z) :
  (forall x, f x = g x) -> (forall v, l v = l' v) ->
  dgpr_differential_values f a l -> dgpr_differential_values g a l'.
Proof.
move=> hfg hl [L [hL hv]]; exists L; split; last by move=> v; rewrite hv hl.
by have -> : g = f by apply: funext=> x; rewrite hfg.
Qed.

(** Source for [dgpr_values_linear]: Federer 3.1.1, p. 209: the
    differential is linear, so sum_i y_i l(eps_i) = l(y). *)
Lemma dgpr_values_linear (f : X -> Z) (a : X) (l : X -> Z) (y : X) :
  dgpr_differential_values f a l -> \sum_i y i *: l (eps i) = l y.
Proof.
move=> [L [_ hv]]; rewrite -hv -(dgpr_coordinate_sum L y).
by apply: eq_bigr=> i _; rewrite hv.
Qed.

(** Source for [dgpr_values_add]: Federer 3.1.1(5), p. 210: the
    differential of a sum. *)
Lemma dgpr_values_add (f g : X -> Z) (a : X) (l1 l2 : X -> Z) :
  dgpr_differential_values f a l1 -> dgpr_differential_values g a l2 ->
  dgpr_differential_values (fun x => f x + g x) a (fun v => l1 v + l2 v).
Proof.
move=> [L [hL h1]] [M [hM h2]]; exists (L + M); split.
- by have hh := norm_differential_add hNZ hL hM; exact hh.
- by move=> v; rewrite hom_addE h1 h2.
Qed.

(** Source for [dgpr_values_sum]: Federer 3.1.1(5), p. 210: the
    differential of a finite sum. *)
Lemma dgpr_values_sum (I : finType) (F : I -> X -> Z) (a : X) (l : I -> X -> Z) :
  (forall i, dgpr_differential_values (F i) a (l i)) ->
  dgpr_differential_values (fun x => \sum_i F i x) a (fun v => \sum_i l i v).
Proof.
move=> hF; have [L hL] := choice hF.
have hD i : true -> has_norm_differential NX NZ setT (F i) a (L i) by move=> _; have [] := hL i.
have hi : norm_domain_interior NX setT a by exists 1; split.
have h := @norm_differential_finite_sum R X Z NX NZ hNX hNZ setT a I xpredT F L hi hD.
exists (\sum_i L i); split.
- apply: (norm_differential_domain_agreement hNX _ h)=> x _.
  by elim/big_rec2: _=> [|i c g _ <-].
- move=> v; have -> : (\sum_i L i) v = \sum_i L i v.
    by elim/big_rec2: _=> [|i c g _ <-]; rewrite ?hom_addE ?hom_zeroE.
  by apply: eq_bigr=> i _; have [_ ->] := hL i.
Qed.

(** Source for [dgpr_values_constant]: Federer 3.1.1, p. 209: constant
    maps have differential 0. *)
Lemma dgpr_values_constant (c : Z) (a : X) :
  dgpr_differential_values (fun _ => c) a (fun _ => 0).
Proof.
exists 0; split; last by move=> v; rewrite hom_zeroE.
have hi : norm_domain_interior NX setT a by exists 1; split.
by have hh := @norm_differential_constant R X Z NX NZ hNX hNZ setT a c hi; exact hh.
Qed.

End Calculus.

Arguments dgpr_differential_values {R n Z} NZ f a l.

Section CalculusMixed.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NR := (fun t : R^o => `|t|).
Local Notation hNR := (@scalar_absolute_value_norm R).
Variables (Z : lmodType R) (NZ : Z -> R).
Hypothesis hNZ : is_real_norm NZ.

(** Source for [dgpr_values_scalar_product]: the product rule of
    Federer 3.1.11, pp. 220-222, for a real function times a vector
    valued function. *)
Lemma dgpr_values_scalar_product (f : X -> R) (g : X -> Z) (a : X) (l1 : X -> R) (l2 : X -> Z) :
  @dgpr_differential_values R n R^o NR f a l1 -> dgpr_differential_values NZ g a l2 ->
  dgpr_differential_values NZ (fun x => f x *: g x) a (fun v => l1 v *: g a + f a *: l2 v).
Proof.
move=> [L [hL h1]] [M [hM h2]].
exists (scalar_vector_product_linear_term (f a) (g a) L M); split.
- by have hh := norm_differential_scalar_product hNX hNZ hL hM; exact hh.
- move=> v; rewrite /scalar_vector_product_linear_term hom_addE hom_compE hom_scaleE.
  by rewrite -h1 -h2.
Qed.

(** Source for [dgpr_values_postcompose]: Federer 3.1.1(3), p. 210,
    chain rule with a continuous linear map. *)
Lemma dgpr_values_postcompose (W : lmodType R) (NW : W -> R) (hNW : is_real_norm NW)
    (M : Hom Z W) (g : X -> Z) (a : X) (l : X -> Z) :
  norm_bounded_linear NZ NW M -> dgpr_differential_values NZ g a l ->
  dgpr_differential_values NW (fun x => M (g x)) a (fun v => M (l v)).
Proof.
move=> hM [L [hL hv]]; exists (hom_comp M L); split.
- by have hh := norm_differential_postcompose_linear hNX hNZ hNW hM hL; exact hh.
- by move=> v; rewrite hom_compE hv.
Qed.

End CalculusMixed.

Section CalculusEvaluation.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NR := (fun t : R^o => `|t|).
Local Notation hNR := (@scalar_absolute_value_norm R).

(** Source for [dgpr_coordinate_bounded]: Federer 1.7.1, p. 28: the
    coordinate functionals of R^n are bounded by the Euclidean norm. *)
Lemma dgpr_coordinate_bounded (i : 'I_n) :
  norm_bounded_linear NX NR (dual_basis (@coordinate_basisP R n) i).
Proof.
exists 1; split=> // y; rewrite euclidean_coordinate_dual_basis mul1r.
exact: euclidean_coordinate_norm_bound.
Qed.

(** Source for [dgpr_values_coordinate]: Federer 3.1.1(3), p. 210: the
    coordinates of a differentiable map into R^n are differentiable. *)
Lemma dgpr_values_coordinate (u : X -> X) (a : X) (l : X -> X) (i : 'I_n) :
  dgpr_differential_values NX u a l ->
  @dgpr_differential_values R n R^o NR (fun y => u y i) a (fun v => l v i).
Proof.
move=> hu.
have h := dgpr_values_postcompose hNX hNR (dgpr_coordinate_bounded i) hu.
apply: (dgpr_values_ext _ _ h)=> [y|v]; exact: euclidean_coordinate_dual_basis.
Qed.

Variables (Z : lmodType R) (NZ : Z -> R).
Hypothesis hNZ : is_real_norm NZ.

(** Source for [dgpr_values_evaluation]: Federer 3.1.11, pp. 220-222:
    if y ↦ A(y)(w) has differential [v ↦ A2(v)(w)] at a for every w, and
    u has differential l at a, then [y ↦ A(y)(u(y))] has differential
    [v ↦ A2(v)(u(a)) + A(a)(l(v))] at a. *)
Lemma dgpr_values_evaluation (A : X -> Hom X Z) (A2 : X -> Hom X Z) (u : X -> X) (a : X)
    (l : X -> X) :
  (forall w, dgpr_differential_values NZ (fun y => A y w) a (fun v => A2 v w)) ->
  dgpr_differential_values NX u a l ->
  dgpr_differential_values NZ (fun y => A y (u y)) a (fun v => A2 v (u a) + A a (l v)).
Proof.
move=> hA hu.
have hi i := dgpr_values_scalar_product hNZ (dgpr_values_coordinate i hu) (hA (@coordinate_basis R n i)).
have h := dgpr_values_sum hNZ hi.
apply: (dgpr_values_ext _ _ h)=> [y|v].
- exact: dgpr_coordinate_sum.
- rewrite big_split /= addrC; congr (_ + _); exact: dgpr_coordinate_sum.
Qed.
End CalculusEvaluation.
