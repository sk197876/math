(** Federer (1969), 1.8.2, p. 40: normal-form vectors for
    the imaginary rotation. These supporting consequences of the
    bilinear normal form in 1.7.3, pp. 29-30, recover the vector
    action and show that an orthogonal skew map has unit coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws Bilinear
  InnerNorm OrthogonalMaps OrthonormalFamilies SkewNormalFormUP
  PairedOrthonormalCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Actions.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable f : {linear V -> V}.
Variable k : nat.
Variables a b : 'I_k -> V.
Variable lambda : 'I_k -> R.
Hypothesis ho : orthonormal_family B (paired_family a b).
Hypothesis heq : forall x y, B (f x) y =
  \sum_i lambda i * skew_pair_form B (a i) (b i) x y.
Local Notation hb := (inner_bilinear hB).

(** Source for [skew_normal_vector_expansion]: Federer 1.8.2,
    p. 40, supporting vector form of the paired-block expansion. *)
Lemma skew_normal_vector_expansion x :
  f x = \sum_i lambda i *: (B x (a i) *: b i - B x (b i) *: a i).
Proof.
apply/eqP; rewrite -subr_eq0; apply/eqP.
apply: (inner_left_separates hB) => y.
rewrite (bilBl hb) heq.
have hs : B (\sum_i lambda i *: (B x (a i) *: b i - B x (b i) *: a i)) y =
    \sum_i lambda i * skew_pair_form B (a i) (b i) x y.
  rewrite (big_morph (fun z => B z y) (fun z t => bilDl hb z t y) (bil0l hb y)).
  apply: eq_bigr => i _.
  rewrite (bilZl hb) (bilBl hb) !(bilZl hb).
  change (lambda i * (B x (a i)*B (b i) y-B x (b i)*B (a i) y) =
    lambda i * skew_pair_form B (a i) (b i) x y).
  by rewrite /skew_pair_form (inner_symmetric hB (b i)) (inner_symmetric hB (a i)).
by rewrite hs subrr.
Qed.

(** Source for [skew_normal_first_action]: Federer 1.8.2,
    p. 40, a first vector is mapped to lambda times its paired second vector. *)
Lemma skew_normal_first_action i : f (a i) = lambda i *: b i.
Proof.
rewrite skew_normal_vector_expansion.
under eq_bigr do rewrite (paired_orthonormal_first ho)
  (paired_orthonormal_cross ho) scale0r subr0.
rewrite (bigD1 i) //= eqxx scale1r.
have hz : \sum_(j | j != i) lambda j *: ((if i == j then 1 else 0) *: b j) = 0.
  apply: big1 => j hj; by rewrite eq_sym (negbTE hj) !scale0r scaler0.
by rewrite hz addr0.
Qed.

(** Source for [orthogonal_skew_normal_coefficients_one]: Federer
    1.8.2, p. 40, when the skew map is orthogonal, every nonnegative
    normal-form coefficient equals one. This applies to J(v)=iv. *)
Theorem orthogonal_skew_normal_coefficients_one
    (hf : is_orthogonal_map B B f) (hl : forall i, 0 <= lambda i) i : lambda i = 1.
Proof.
have ha : inner_norm hB (a i) = 1.
  apply: inner_norm_value; first exact: ler01.
  by rewrite expr1n (paired_orthonormal_first ho) eqxx.
have hb' : inner_norm hB (b i) = 1.
  apply: inner_norm_value; first exact: ler01.
  by rewrite expr1n (paired_orthonormal_second ho) eqxx.
have hh := orthogonal_map_norm hB hB hf (a i).
by rewrite skew_normal_first_action inner_normZ hb' mulr1 (ger0_norm (hl i)) ha in hh.
Qed.
End Actions.
