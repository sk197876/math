(** Federer (1969), 1.8.2, p. 40: exterior powers of a
    two-form written as a sum of scalar multiples of paired one-form
    products. In top degree the coefficient is k! times the product
    of the block coefficients; above the number of blocks it vanishes.
    These algebraic statements require no orthonormality. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ExteriorExpansion BoundedHom HomogeneousHom AlgebraUP Bilinear AlgebraPowers
  AlternatingForms AlternatingSum AlternatingProduct AlternatingUnit
  ScalarCoefficients CommutingNilpotentPowers TwoFormBlocks TwoFormPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section NormalPowers.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Local Notation A := (alternating_unital_algebra h2 V (scalar_algebra K)).
Local Notation mul := (alg_mul A).
Local Notation hb := (alg_bilinear A).
Variable k : nat.
Variables alpha beta : 'I_k -> A_m V K^o 1.
Variable lambda : 'I_k -> K.
Local Notation block := (fun j => form_wedge h2 (scalar_bilinear K) (alpha j) (beta j)).
Local Notation term := (fun j => lambda j *: form_include (block j)).

(** Source for [normal_block_sum_include]: Federer 1.8.2,
    p. 40, supporting inclusion of the normal-form sum into the
    full unital alternating algebra. *)
Lemma normal_block_sum_include :
  form_include (\sum_j lambda j *: block j) =
    \sum_(x <- [seq term j | j <- enum 'I_k]) x.
Proof.
rewrite linear_sum big_map product_index_enum.
apply: eq_bigr => j _; exact: linearZ.
Qed.

(** Source for [normal_blocks_square_zero]: Federer 1.8.2,
    p. 40, every scaled paired block in the normal form squares to zero. *)
Lemma normal_blocks_square_zero x :
  x \in [seq term j | j <- enum 'I_k] -> mul x x = 0.
Proof. move=> /mapP [j _ ->]; exact: scaled_two_form_block_square. Qed.

(** Source for [normal_blocks_commute]: Federer 1.8.2,
    p. 40, the scaled paired blocks commute with each other. *)
Lemma normal_blocks_commute x y :
  x \in [seq term j | j <- enum 'I_k] ->
  y \in [seq term j | j <- enum 'I_k] -> mul x y = mul y x.
Proof.
move=> /mapP [i _ ->] /mapP [j _ ->].
by rewrite !(bilZl hb) !(bilZr hb) !scalerA included_two_forms_commute mulrC.
Qed.

(** Source for [normal_blocks_product_scale]: Federer 1.8.2,
    p. 40, extracting the product of the scalar block coefficients. *)
Lemma normal_blocks_product_scale (s : seq 'I_k) :
  foldr mul (alg_one A) [seq term j | j <- s] =
    (\prod_(j <- s) lambda j) *:
      foldr mul (alg_one A) [seq form_include (block j) | j <- s].
Proof.
elim: s => [|j s ih]; first by rewrite big_nil /= scale1r.
rewrite big_cons.
change (mul (lambda j *: form_include (block j))
  (foldr mul (alg_one A) [seq term i | i <- s]) =
  (lambda j * (\prod_(i <- s) lambda i)) *:
    mul (form_include (block j))
      (foldr mul (alg_one A) [seq form_include (block i) | i <- s])).
by rewrite ih (bilZl hb) (bilZr hb) scalerA.
Qed.

(** Source for [normal_two_form_top_power]: Federer 1.8.2,
    p. 40, the power equals k! lambda_1 ... lambda_k times the
    ordered product of the k paired one-form blocks. *)
Theorem normal_two_form_top_power :
  form_include (two_form_power h2 (\sum_j lambda j *: block j) k) =
    ((k`!%:R : K) * \prod_j lambda j) *:
      foldr mul (alg_one A) [seq form_include (block j) | j <- enum 'I_k].
Proof.
rewrite two_form_power_include normal_block_sum_include.
have hs : size [seq term j | j <- enum 'I_k] = k by rewrite size_map size_enum_ord.
have h := @commuting_square_zero_top_power K A
  [seq term j | j <- enum 'I_k] normal_blocks_square_zero normal_blocks_commute.
rewrite hs normal_blocks_product_scale scalerA in h.
rewrite !product_index_enum in h *.
exact h.
Qed.

(** Source for [normal_two_form_power_above_blocks]: Federer 1.8.2,
    p. 40, supporting vanishing if the power exceeds the number
    of normal-form blocks. *)
Theorem normal_two_form_power_above_blocks m : (k < m)%N ->
  two_form_power h2 (\sum_j lambda j *: block j) m = 0.
Proof.
move=> hm; apply: (can_inj (@form_includeK K V K^o (m+m))).
rewrite two_form_power_include linear0 normal_block_sum_include.
have hs : (size [seq term j | j <- enum 'I_k] < m)%N
  by rewrite size_map size_enum_ord.
exact: (@commuting_square_zero_power_vanishes K A
  [seq term j | j <- enum 'I_k] normal_blocks_square_zero normal_blocks_commute m hs).
Qed.
End NormalPowers.
