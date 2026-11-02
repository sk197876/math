(** Federer (1969), 1.9.3, p. 42: factorisation of monomials and their
    factorial denominators. Supporting identities for the multinomial
    theorem. No characteristic restriction is needed for these identities. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear AlgebraUP SymmetricAlgebra
  SymmetricGrading SymmetricMultiIndices SymmetricMonomials SymmetricDividedMonomials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_multi_factorial_cons]: Federer 1.9.3,
    p. 42, the product definition of alpha! separates into
    the factorial of the first exponent and the tail factorial. *)
Lemma symmetric_multi_factorial_cons n k (a : symmetric_multi_index n) :
  symmetric_multi_factorial (symmetric_multi_cons k a) = (k`! * symmetric_multi_factorial a)%N.
Proof.
rewrite /symmetric_multi_factorial big_ord_recl /symmetric_multi_cons ffunE unlift_none.
congr (_ * _)%N; apply: eq_bigr=> i _; by rewrite ffunE liftK.
Qed.

(** Source for [symmetric_monomial_word_cons]: Federer 1.9.3,
    p. 42, the first exponent gives an initial repeated block,
    followed by the monomial word in the remaining variables. *)
Lemma symmetric_monomial_word_cons (T : Type) n (v : 'I_n.+1 -> T) k
    (a : symmetric_multi_index n) :
  symmetric_monomial_word v (symmetric_multi_cons k a) =
    nseq k (v ord0) ++ symmetric_monomial_word (fun i => v (lift ord0 i)) a.
Proof.
rewrite /symmetric_monomial_word enum_ordSl /= -map_comp
  /symmetric_multi_cons ffunE unlift_none.
congr (_ ++ _); congr 1 (flatten _); apply: eq_map=> i.
by rewrite /= ffunE liftK.
Qed.

(** Source for [symmetric_monomial_cons]: Federer 1.9.3,
    p. 42, the monomial separates as the first vector's power
    times the monomial in the remaining vectors. *)
Lemma symmetric_monomial_cons (K : fieldType) (V : lmodType K)
    n (v : 'I_n.+1 -> V) k (a : symmetric_multi_index n) :
  symmetric_monomial v (symmetric_multi_cons k a) =
    symmetric_product (symmetric_vector_power (v ord0) k)
      (symmetric_monomial (fun i => v (lift ord0 i)) a).
Proof. by rewrite /symmetric_monomial /symmetric_vector_power
  symmetric_monomial_word_cons symmetric_word_cat. Qed.

(** Source for [symmetric_divided_monomial_cons]: Federer
    1.9.3, p. 42, the divided monomial factors into the
    first divided power and the tail divided monomial. *)
Lemma symmetric_divided_monomial_cons (K : fieldType) (V : lmodType K)
    n (v : 'I_n.+1 -> V) k (a : symmetric_multi_index n) :
  symmetric_divided_monomial v (symmetric_multi_cons k a) =
    symmetric_product (symmetric_divided_vector_power (v ord0) k)
      (symmetric_divided_monomial (fun i => v (lift ord0 i)) a).
Proof.
rewrite /symmetric_divided_monomial /symmetric_divided_vector_power
  symmetric_multi_factorial_cons symmetric_monomial_cons natrM invfM
  (bilZl (symmetric_product_bilinear V)) (bilZr (symmetric_product_bilinear V)) scalerA.
by [].
Qed.

(** Source for [symmetric_block_word_scale]: Federer 1.9.3,
    p. 42, supporting scalar extraction from every repeated
    block of a finite monomial word. *)
Lemma symmetric_block_word_scale (K : fieldType) (V : lmodType K) (I : Type)
    (v : I -> V) (t : I -> K) (a : I -> nat) s :
  symmetric_word (flatten [seq nseq (a i) (t i *: v i) | i <- s]) =
    (\prod_(i <- s) (t i)^+(a i)) *:
      symmetric_word (flatten [seq nseq (a i) (v i) | i <- s]).
Proof.
elim: s=> [|i s ih]; first by rewrite /= big_nil scale1r.
rewrite /= big_cons -!symmetric_word_cat ih.
change (symmetric_product (symmetric_vector_power (t i *: v i) (a i))
  ((\prod_(j <- s) (t j)^+(a j)) *:
    symmetric_word (flatten [seq nseq (a j) (v j) | j <- s])) =
  ((t i)^+(a i) * \prod_(j <- s) (t j)^+(a j)) *:
    symmetric_product (symmetric_vector_power (v i) (a i))
      (symmetric_word (flatten [seq nseq (a j) (v j) | j <- s]))).
by rewrite symmetric_vector_power_scale
  (bilZl (symmetric_product_bilinear V)) (bilZr (symmetric_product_bilinear V)) scalerA.
Qed.

(** Source for [symmetric_monomial_scale]: Federer 1.9.3,
    p. 42, (t_1 v_1)^alpha_1 ... (t_k v_k)^alpha_k
    equals t^alpha times v^alpha. *)
Lemma symmetric_monomial_scale (K : fieldType) (V : lmodType K)
    n (v : 'I_n -> V) (t : 'I_n -> K) (a : symmetric_multi_index n) :
  symmetric_monomial (fun i => t i *: v i) a =
    symmetric_scalar_monomial t a *: symmetric_monomial v a.
Proof.
rewrite /symmetric_monomial /symmetric_monomial_word symmetric_block_word_scale.
by rewrite /symmetric_scalar_monomial big_enum.
Qed.

(** Source for [symmetric_divided_monomial_scale]: Federer
    1.9.3, p. 42, the same scalar extraction for the divided
    monomials used in the displayed k-nomial theorem. *)
Lemma symmetric_divided_monomial_scale (K : fieldType) (V : lmodType K)
    n (v : 'I_n -> V) (t : 'I_n -> K) (a : symmetric_multi_index n) :
  symmetric_divided_monomial (fun i => t i *: v i) a =
    symmetric_scalar_monomial t a *: symmetric_divided_monomial v a.
Proof. by rewrite /symmetric_divided_monomial symmetric_monomial_scale !scalerA mulrC. Qed.
