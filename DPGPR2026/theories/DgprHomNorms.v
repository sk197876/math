(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    mr:notation: the inner product A . B = trace(A* o B) on Hom(V,Z) and
    its norm |A| (Federer 1.7.9, [hom_inner], [hom_norm],
    [hom_inner_trace]), the operator norm ||A|| (Federer 1.7.6,
    [linear_operator_norm]), the comparison ||A|| <= |A| <= (dim V)^(1/2) ||A||
    (Federer 1.7.9, [hom_operator_norm_comparison]), the estimates
    |B o A| <= ||B|| |A|, |A*| = |A| and |A o C| <= |A| ||C||, and the
    rank one map omega . b of Allard 2.3(4), which is Federer's
    [hom_with_coefficient] (1.4.4). Only the estimates and the rank one
    identity are new; the remaining notions are Federer's declarations,
    used directly. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP Bilinear InnerProductUP InnerNorm InnerProductLaws
  LinearBasis Hom HomInner HomInnerCoordinates OperatorNorm OperatorNormIdentities
  Adjoint AdjointUP OrthonormalFamilies CoefficientCoordinates.
From DPGPR Require Import DgprOrthonormalCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [dgpr_sqr_le]: supporting comparison of nonnegative
    numbers through their squares, used for the norm estimates of
    blueprint mr:notation and lem:spectral. *)
Lemma dgpr_sqr_le (R : realType) (x y : R) : 0 <= y -> x ^+ 2 <= y ^+ 2 -> x <= y.
Proof.
move=> hy h; have [hx|hx] := lerP x 0; first exact: le_trans hx hy.
by rewrite -(ler_pXn2r (n := 2)) ?nnegrE // ltW.
Qed.

(** Source for [dgpr_hom_sum_apply]: supporting evaluation of a finite
    sum of linear maps (Federer 1.4.1: operations on Hom are pointwise). *)
Lemma dgpr_hom_sum_apply (R : realType) (V W : lmodType R) (I : finType)
    (F : I -> Hom V W) v : (\sum_i F i) v = \sum_i F i v.
Proof.
apply: (big_rec2 (fun (G : Hom V W) w => G v = w)) => [|i G w _ h]; first exact: hom_zeroE.
by rewrite hom_addE h.
Qed.

Section HomNorm.
Variable R : realType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Variable C : W -> W -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.

(** Source for [dgpr_hom_norm_sqr]: Federer 1.7.9, p. 35, first
    displayed computation: |F|^2 = sum_j |F(u_j)|^2 for an orthonormal
    basis u of V. *)
Lemma dgpr_hom_norm_sqr (F : Hom V W) k (u : 'I_k -> V) :
  is_basis u -> orthonormal_family B u ->
  hom_norm hB hC he F ^+ 2 = \sum_j C (F (u j)) (F (u j)).
Proof.
move=> hu ho; rewrite (inner_norm_sqr (hom_inner_productP hB hC he)).
exact: (hom_inner_orthonormal_sum hB hC he hu ho).
Qed.

(** Source for [dgpr_rank_one]: blueprint mr:notation and Allard
    2.3(4): for omega in Hom(V,R) and b in W, omega . b in Hom(V,W) is
    [v |-> omega(v) b]; it is Federer's [hom_with_coefficient] of 1.4.4. *)
Definition dgpr_rank_one (omega : Hom V R^o) (b : W) : Hom V W := hom_with_coefficient b omega.

(** Source for [dgpr_rank_oneE]: blueprint mr:notation,
    (omega . b)(v) = omega(v) b. *)
Lemma dgpr_rank_oneE omega b v : dgpr_rank_one omega b v = (omega v : R) *: b.
Proof. exact: hom_with_coefficientE. Qed.

(** Source for [dgpr_rank_one_inner]: blueprint mr:notation and Allard
    2.3(4): (omega . b) . A = omega(A*(b)) for A in Hom(V,W), where A*
    is the adjoint of Federer 1.7.4. *)
Lemma dgpr_rank_one_inner (omega : Hom V R^o) (b : W) (A : Hom V W) :
  hom_inner hB hC he (dgpr_rank_one omega b) A =
  omega (inner_adjoint hB hC he (hom_as_linear A) b).
Proof.
have [u [hu ho]] := dgpr_orthonormal_basis_exists hB he.
pose As := inner_adjoint hB hC he (hom_as_linear A).
have hA : is_adjoint B C (hom_as_linear A) As := inner_adjointP hB hC he (hom_as_linear A).
rewrite (hom_inner_orthonormal_sum hB hC he hu ho).
rewrite [in RHS](dgpr_orthonormal_expansion hB hu ho (As b)) linear_sum.
apply: eq_bigr => j _; rewrite dgpr_rank_oneE linearZ_LR.
have h1 : C ((omega (u j) : R) *: b) (A (u j)) = omega (u j) * C b (A (u j)).
  by rewrite (inner_symmetric hC) dgpr_innerZr // (inner_symmetric hC).
rewrite h1 (inner_symmetric hC) -hA (inner_symmetric hB).
by rewrite [RHS]mulrC.
Qed.
(** Source for [dgpr_adjoint_square_sum]: Federer 1.7.9, p. 35, with
    the adjoint of 1.7.4: if x . F*(y) = F(x) . y for x in V and y in W,
    and u, w are orthonormal bases of V and W, then
    sum_j |F(u_j)|^2 = sum_k |F*(w_k)|^2, both sides being
    sum_(j,k) (F(u_j) . w_k)^2. *)
Lemma dgpr_adjoint_square_sum (F : V -> W) (Fs : W -> V) k (u : 'I_k -> V) l (w : 'I_l -> W) :
  (forall x y, B x (Fs y) = C (F x) y) ->
  is_basis u -> orthonormal_family B u -> is_basis w -> orthonormal_family C w ->
  \sum_j C (F (u j)) (F (u j)) = \sum_i B (Fs (w i)) (Fs (w i)).
Proof.
move=> hF hu ho hw how.
have hL j : C (F (u j)) (F (u j)) = \sum_i (B (Fs (w i)) (u j)) ^+ 2.
  rewrite (dgpr_orthonormal_parseval hC hw how); apply: eq_bigr => i _.
  by rewrite -hF (inner_symmetric hB).
rewrite (eq_bigr _ (fun j _ => hL j)) exchange_big; apply: eq_bigr => i _.
by rewrite (dgpr_orthonormal_parseval hB hu ho).
Qed.

End HomNorm.

Section Composition.
Variable R : realType.
Variables V' V W Z : lmodType R.
Variable B' : V' -> V' -> R.
Variable B : V -> V -> R.
Variable C : W -> W -> R.
Variable D : Z -> Z -> R.
Hypothesis hB' : is_inner_product B'.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Hypothesis hD : is_inner_product D.
Variables p n m : nat.
Variable e' : 'I_p -> V'.
Variable e : 'I_n -> V.
Variable f : 'I_m -> W.
Hypothesis he' : is_basis e'.
Hypothesis he : is_basis e.
Hypothesis hf : is_basis f.

(** Source for [dgpr_hom_norm_adjoint]: blueprint mr:notation, with
    Federer 1.7.4 and 1.7.9: |A*| = |A| for A in Hom(V,W). *)
Theorem dgpr_hom_norm_adjoint (A : Hom V W) :
  hom_norm hC hB hf (hom_of_linear (inner_adjoint hB hC he (hom_as_linear A))) =
    hom_norm hB hC he A.
Proof.
have [u [hu ho]] := dgpr_orthonormal_basis_exists hB he.
have [w [hw how]] := dgpr_orthonormal_basis_exists hC hf.
have hA := inner_adjointP hB hC he (hom_as_linear A).
apply: (@pexpIrn R 2) => //; rewrite ?nnegrE ?inner_norm_nonnegative //.
rewrite (dgpr_hom_norm_sqr hC hB hf _ hw how) (dgpr_hom_norm_sqr hB hC he _ hu ho).
have hA' x y : B x (inner_adjoint hB hC he (hom_as_linear A) y) = C (A x) y.
  by rewrite hA hom_as_linearE.
rewrite (dgpr_adjoint_square_sum hB hC hA' hu ho hw how).
by apply: eq_bigr => i _; rewrite hom_of_linearE.
Qed.

(** Source for [dgpr_hom_norm_comp_left]: blueprint mr:notation,
    |L o A| <= ||L|| |A| for A in Hom(V,W) and L in Hom(W,Z), with the
    norms of Federer 1.7.6 and 1.7.9. *)
Theorem dgpr_hom_norm_comp_left (A : Hom V W) (L : Hom W Z) :
  hom_norm hB hD he (hom_comp L A) <=
    linear_operator_norm hC hD hf (hom_as_linear L) * hom_norm hB hC he A.
Proof.
have [u [hu ho]] := dgpr_orthonormal_basis_exists hB he.
pose M := linear_operator_norm hC hD hf (hom_as_linear L).
have hM : 0 <= M := linear_operator_norm_nonnegative hC hD hf (hom_as_linear L).
apply: dgpr_sqr_le; first by rewrite mulr_ge0 ?inner_norm_nonnegative.
rewrite exprMn (dgpr_hom_norm_sqr hB hD he _ hu ho) (dgpr_hom_norm_sqr hB hC he _ hu ho).
rewrite mulr_sumr; apply: ler_sum => j _.
rewrite hom_compE -(inner_norm_sqr hD) -(inner_norm_sqr hC) -exprMn.
apply: lerXn2r; rewrite ?nnegrE ?mulr_ge0 ?inner_norm_nonnegative //.
by have := linear_operator_norm_bound hC hD hf (hom_as_linear L) (A (u j)); rewrite hom_as_linearE.
Qed.

(** Source for [dgpr_hom_norm_comp_right]: blueprint mr:notation,
    |A o L| <= |A| ||L|| for A in Hom(V,W) and L in Hom(V',V), with the
    norms of Federer 1.7.6 and 1.7.9; the proof passes to adjoints and
    uses ||L*|| = ||L|| of Federer 1.7.6. *)
Theorem dgpr_hom_norm_comp_right (A : Hom V W) (L : Hom V' V) :
  hom_norm hB' hC he' (hom_comp A L) <=
    hom_norm hB hC he A * linear_operator_norm hB' hB he' (hom_as_linear L).
Proof.
have [u' [hu' ho']] := dgpr_orthonormal_basis_exists hB' he'.
have [u [hu ho]] := dgpr_orthonormal_basis_exists hB he.
have [w [hw how]] := dgpr_orthonormal_basis_exists hC hf.
pose As := inner_adjoint hB hC he (hom_as_linear A).
pose Ls := inner_adjoint hB' hB he' (hom_as_linear L).
have hA : is_adjoint B C (hom_as_linear A) As := inner_adjointP hB hC he (hom_as_linear A).
have hL : is_adjoint B' B (hom_as_linear L) Ls := inner_adjointP hB' hB he' (hom_as_linear L).
pose M := linear_operator_norm hB' hB he' (hom_as_linear L).
have hMs : linear_operator_norm hB hB' he Ls = M.
  by rewrite /M (linear_operator_adjoint_norm_equal hB' hB he' he).
have hM : 0 <= M := linear_operator_norm_nonnegative hB' hB he' (hom_as_linear L).
apply: dgpr_sqr_le; first by rewrite mulr_ge0 ?inner_norm_nonnegative.
have hcomp x y : B' x (Ls (As y)) = C (hom_comp A L x) y.
  by rewrite hL hom_as_linearE hA hom_as_linearE hom_compE.
have hA' x y : B x (As y) = C (A x) y by rewrite hA hom_as_linearE.
rewrite exprMn (dgpr_hom_norm_sqr hB' hC he' _ hu' ho') (dgpr_hom_norm_sqr hB hC he _ hu ho).
rewrite (dgpr_adjoint_square_sum hB' hC hcomp hu' ho' hw how).
rewrite (dgpr_adjoint_square_sum hB hC hA' hu ho hw how).
rewrite mulr_suml; apply: ler_sum => i _.
rewrite -(inner_norm_sqr hB') -(inner_norm_sqr hB) -exprMn [_ * M]mulrC.
apply: lerXn2r; rewrite ?nnegrE ?mulr_ge0 ?inner_norm_nonnegative //.
by rewrite -hMs; exact: linear_operator_norm_bound.
Qed.
End Composition.
