(** Federer (1969), 1.8.2, p. 40: the coefficient of a
    paired block is the value of the two-form on that orthonormal
    pair. These supporting identities also connect pair indexing
    with the two-block coordinate convention. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity OrthonormalFamilies
  SkewNormalFormUP OrthonormalConcatenation ConcatenatedFamilies
  AlternatingForms AlternatingProduct ScalarCoefficients TwoCovectorProduct FormEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Coordinates.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable k : nat.
Variables a b : 'I_k -> V.
Hypothesis ho : orthonormal_family B (paired_family a b).

(** Source for [paired_orthonormal_first]: Federer 1.8.2,
    p. 40, the first members of the pairs form an orthonormal family. *)
Lemma paired_orthonormal_first : orthonormal_family B a.
Proof.
move=> i j; have h := ho (i,false) (j,false).
by rewrite /paired_family /= xpair_eqE /= andbT in h.
Qed.

(** Source for [paired_orthonormal_second]: Federer 1.8.2,
    p. 40, the second members of the pairs form an orthonormal family. *)
Lemma paired_orthonormal_second : orthonormal_family B b.
Proof.
move=> i j; have h := ho (i,true) (j,true).
by rewrite /paired_family /= xpair_eqE /= andbT in h.
Qed.

(** Source for [paired_orthonormal_cross]: Federer 1.8.2,
    p. 40, all first members are orthogonal to all second members. *)
Lemma paired_orthonormal_cross i j : B (a i) (b j) = 0.
Proof.
have h := ho (i,false) (j,true).
by rewrite /paired_family /= xpair_eqE /= andbF in h.
Qed.

(** Source for [paired_orthonormal_concatenated]: Federer 1.8.2,
    p. 40, reordering the orthonormal pairs into two blocks preserves
    orthonormality. *)
Lemma paired_orthonormal_concatenated : orthonormal_family B (concatenate_family a b).
Proof.
exact: (@orthonormal_concatenation R V B hB k k a b
  paired_orthonormal_first paired_orthonormal_second paired_orthonormal_cross).
Qed.

(** Source for [paired_normal_form_coefficient]: Federer 1.8.2,
    p. 40, lambda_j=A(e_(2j-1),e_(2j)) for the orthonormal normal form. *)
Lemma paired_normal_form_coefficient (lambda : 'I_k -> R) i :
  (\sum_j lambda j *: form_wedge h2 (scalar_bilinear R)
    (inner_polarity hB (a j)) (inner_polarity hB (b j))) [tuple a i; b i] = lambda i.
Proof.
change (form_evaluate [tuple a i; b i]
  (\sum_j lambda j *: form_wedge h2 (scalar_bilinear R)
    (inner_polarity hB (a j)) (inner_polarity hB (b j))) = lambda i).
rewrite linear_sum.
under eq_bigr do rewrite linearZ.
change ((\sum_j lambda j * (form_wedge h2 (scalar_bilinear R)
  (inner_polarity hB (a j)) (inner_polarity hB (b j)) [tuple a i; b i])) = lambda i).
have ht j : form_wedge h2 (scalar_bilinear R)
    (inner_polarity hB (a j)) (inner_polarity hB (b j)) [tuple a i; b i] =
    if j == i then 1 else 0.
  rewrite inner_covector_pair_product /skew_pair_form
    paired_orthonormal_first paired_orthonormal_second
    paired_orthonormal_cross mul0r subr0 eq_sym.
  by case: (j == i); rewrite ?mul1r ?mul0r.
under eq_bigr do rewrite ht.
rewrite (bigD1 i) //= eqxx mulr1.
have hz : \sum_(j | j != i) lambda j * (if j == i then 1 else 0) = 0.
  apply: big1 => j hj; by rewrite (negbTE hj) mulr0.
by rewrite hz addr0.
Qed.
End Coordinates.
