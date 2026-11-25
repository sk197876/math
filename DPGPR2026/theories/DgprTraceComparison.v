(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    lem:trace: if g is a bilinear form on a finite dimensional inner
    product space V with g(v,v) >= 0 for v in V, Q is a symmetric
    endomorphism of V with ||Q|| <= 1, and eps is an orthonormal basis of
    V, then sum_j g(Q(eps_j),Q(eps_j)) <= sum_j g(eps_j,eps_j). The proof
    expresses both sums through an orthonormal basis of eigenvectors of Q
    (Federer 1.7.3, 1.7.10). *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import TensorUP Bilinear InnerProductUP InnerNorm InnerProductLaws
  LinearBasis Hom OrthonormalFamilies SymmetricEndomorphisms EigenbasisUP
  SymmetricEigenbasis OperatorNorm.
From DPGPR Require Import DgprOrthonormalCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Trace.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.

(** Source for [dgpr_trace_eigen]: blueprint proof of lem:trace, with
    Federer 1.7.10, p. 35: if u is an orthonormal basis of V and
    F(x) . u_a = q_a (x . u_a) for x in V, then
    sum_j g(F(eps_j),F(eps_j)) = sum_a q_a^2 g(u_a,u_a) for every
    orthonormal basis eps of V. *)
Lemma dgpr_trace_eigen (g : V -> V -> R) (hg : @bilinear R V V R^o g) (F : V -> V)
    m (u : 'I_m -> V) (q : 'I_m -> R) k (eps : 'I_k -> V) :
  is_basis u -> orthonormal_family B u -> is_basis eps -> orthonormal_family B eps ->
  (forall x a, B (F x) (u a) = q a * B x (u a)) ->
  \sum_j g (F (eps j)) (F (eps j)) = \sum_a q a ^+ 2 * g (u a) (u a).
Proof.
move=> hu ho heps hoe hF.
have h1 j : g (F (eps j)) (F (eps j)) =
    \sum_a \sum_b (q a * q b * g (u a) (u b)) * (B (u a) (eps j) * B (u b) (eps j)).
  rewrite (dgpr_orthonormal_bilinear hB hu ho hg); apply: eq_bigr => a _.
  apply: eq_bigr => b _; rewrite !hF (inner_symmetric hB (eps j) (u a)).
  by rewrite (inner_symmetric hB (eps j) (u b)); ring.
rewrite (eq_bigr _ (fun j _ => h1 j)) exchange_big; apply: eq_bigr => a _.
rewrite exchange_big (bigD1 a) //= [X in _ + X]big1 => [|b hb].
  rewrite addr0 -mulr_sumr -(dgpr_orthonormal_inner hB heps hoe) ho eqxx mulr1.
  by rewrite expr2.
rewrite -mulr_sumr -(dgpr_orthonormal_inner hB heps hoe) ho.
by rewrite eq_sym (negbTE hb) mulr0.
Qed.

Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.

(** Source for [dgpr_trace_comparison]: blueprint lem:trace. The form
    g need not be symmetric; the basis e only expresses that V is finite
    dimensional, and eps is any orthonormal basis of V. *)
Theorem dgpr_trace_comparison (g : V -> V -> R) (hg : @bilinear R V V R^o g) (Q : Hom V V)
    k (eps : 'I_k -> V) :
  (forall v, 0 <= g v v) -> is_symmetric_endomorphism B (hom_as_linear Q) ->
  linear_operator_norm hB hB he (hom_as_linear Q) <= 1 ->
  is_basis eps -> orthonormal_family B eps ->
  \sum_j g (Q (eps j)) (Q (eps j)) <= \sum_j g (eps j) (eps j).
Proof.
move=> hg0 hQ hQ1 heps hoe.
have [u [q hu]] := symmetric_orthonormal_eigenbasis hB hQ he.
have hub := eigenbasis_basis hu; have huo := eigenbasis_orthonormal hu.
have hue : forall a, hom_as_linear Q (u a) = q a *: u a := eigenbasis_eigenvalue hu.
have hQc x a : B (Q x) (u a) = q a * B x (u a).
  by rewrite -hom_as_linearE (dgpr_eigen_coefficient hB hub huo hue).
have hIc x a : B ((fun y : V => y) x) (u a) = 1 * B x (u a) by rewrite mul1r.
rewrite (dgpr_trace_eigen hg hub huo heps hoe hQc).
rewrite (dgpr_trace_eigen (F := fun y : V => y) hg hub huo heps hoe hIc).
apply: ler_sum => a _; rewrite expr1n mul1r.
have hq : q a ^+ 2 <= 1.
  have hn : inner_norm hB (hom_as_linear Q (u a)) <= 1.
    apply: le_trans (linear_operator_norm_bound hB hB he (hom_as_linear Q) (u a)) _.
    have hua : inner_norm hB (u a) = 1.
      apply: (@pexpIrn R 2) => //; rewrite ?nnegrE ?inner_norm_nonnegative //.
      by rewrite (inner_norm_sqr hB) huo eqxx expr1n.
    by rewrite hua mulr1.
  have hqa : inner_norm hB (hom_as_linear Q (u a)) ^+ 2 = q a ^+ 2.
    rewrite (inner_norm_sqr hB) hue dgpr_innerZl // dgpr_innerZr // huo eqxx mulr1.
    by rewrite expr2.
  rewrite -hqa -(expr1n R 2); apply: lerXn2r; rewrite ?nnegrE ?inner_norm_nonnegative //.
by rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r; [exact: hg0|exact: hq].
Qed.
End Trace.
