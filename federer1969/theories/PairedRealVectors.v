(** Federer (1969), 1.8.2, p. 40: the interleaved top
    vector a_1 wedge b_1 wedge ... wedge a_k wedge b_k of the
    normal-form pairs. The two-block definition below includes the
    permutation sign from 1.6.6, p. 27. *)
From mathcomp Require Import all_boot all_order all_algebra binomial.
From Federer Require Import SimpleVectors SimpleElementary ConcatenatedFamilies
  PairedGradedWords WordEvaluation InnerProductUP ExteriorNorm
  OrthonormalFamilies SkewNormalFormUP PairedOrthonormalCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Vector.
Variable K : fieldType.
Variable V : lmodType K.
Variable k : nat.
Variables a b : 'I_k -> V.

(** Source for [paired_real_vector]: Federer 1.8.2,
    p. 40, the oriented product of the paired normal-form vectors. *)
Definition paired_real_vector : exterior_power V (k+k) :=
  (-1 : K)^+'C(k,2) *: e_lambda (concatenate_family a b) (ord_tuple (k+k)).

(** Source for [paired_real_vector_word]: Federer 1.8.2,
    p. 40, the paired vector is exactly the literal interleaved word. *)
Lemma paired_real_vector_word : component_val paired_real_vector =
  exterior_word (flatten [seq [:: a j; b j] | j <- enum 'I_k]).
Proof.
rewrite /paired_real_vector linearZ.
change ((-1 : K)^+'C(k,2) *: component_val
  (e_lambda (concatenate_family a b) (ord_tuple (k+k))) =
  exterior_word (flatten [seq [:: a j; b j] | j <- enum 'I_k])).
rewrite e_lambdaE.
have h := @paired_word_interleaving_sign K (exterior_algebra V) (exterior_grading V)
  (@wedge_graded K V) (@exterior_unit_homogeneous K V) (@exterior_anticommutative K V)
  (Choice.clone V _) (@exterior_generator K V) (@exterior_generator_homogeneous K V)
  (Choice.clone 'I_k _) a b (enum 'I_k).
have hw (s : seq V) : @word_eval K (Choice.clone V _) (exterior_algebra V)
    (@exterior_generator K V) s = exterior_word s.
  by elim: s => [|x s ih] //=; rewrite exterior_word_cons -ih.
rewrite !hw size_enum_ord in h.
rewrite concatenate_family_sequence -exterior_word_cat.
exact: esym h.
Qed.

(** Source for [paired_real_vector_simple]: Federer 1.8.2,
    p. 40, a paired product is simple; the empty product is the unit. *)
Lemma paired_real_vector_simple : simple paired_real_vector.
Proof.
rewrite /paired_real_vector; case: k a b => [|q] u v.
- rewrite (_ : 'C(0,2)=0%N) // expr0 scale1r; exact: product_simple.
- apply: simple_scale; [by [] | exact: product_simple].
Qed.
End Vector.

(** Source for [paired_orthonormal_vector_unit]: Federer 1.8.2,
    p. 40, the product of the orthonormal pairs has Euclidean norm one. *)
Theorem paired_orthonormal_vector_unit (R : rcfType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    k (a b : 'I_k -> V) (ho : orthonormal_family B (paired_family a b)) :
  exterior_norm h2 hB (paired_real_vector a b) = 1.
Proof.
rewrite /paired_real_vector exterior_norm_scale normrX normrN normr1 expr1n mul1r.
exact: (@orthonormal_product_unit_norm R h2 V B hB (k+k) (concatenate_family a b)
  (@paired_orthonormal_concatenated R V B hB k a b ho)).
Qed.
