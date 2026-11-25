(** Federer (1969), 1.9.3, pp. 42-43: powers, the scalar monomial t^alpha,
    and the multiindex factorial alpha!. The definitions allow arbitrary
    fields; theorems using inverse factorials require characteristic zero. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear AlgebraUP AlgebraPowers DividedPowers
  GradedAlgebra SymmetricAlgebra SymmetricGrading SymmetricMultiIndices SymmetricMonomials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_multi_factorial]: Federer 1.9.3,
    p. 42, the displayed definition alpha!=product_i(alpha_i!). *)
Definition symmetric_multi_factorial n (a : symmetric_multi_index n) :=
  (\prod_(i < n) (a i)`!)%N.

(** Source for [symmetric_scalar_monomial]: Federer 1.9.3,
    p. 42, the displayed definition t^alpha=product_i(t_i^alpha_i). *)
Definition symmetric_scalar_monomial (K : fieldType) n (t : 'I_n -> K)
    (a : symmetric_multi_index n) := \prod_(i < n) (t i)^+(a i).

(** Source for [symmetric_vector_power]: Federer 1.9.3,
    p. 42, the m-th symmetric power of a vector v, with
    the empty product interpreted as the unit when m=0. *)
Definition symmetric_vector_power (K : fieldType) (V : lmodType K) (v : V) m :=
  symmetric_word (nseq m v).

(** Source for [symmetric_vector_powerE]: Federer 1.9.3,
    p. 42, supporting identification of a repeated symmetric
    word with the ordinary algebra power of its generator. *)
Lemma symmetric_vector_powerE (K : fieldType) (V : lmodType K) (v : V) m :
  symmetric_vector_power v m = @algebra_power K (symmetric_algebra V) (symmetric_generator v) m.
Proof.
rewrite /symmetric_vector_power.
by elim: m=> [|m ih] //=; rewrite symmetric_word_cons ih.
Qed.

(** Source for [symmetric_vector_power_scale]: Federer 1.9.3,
    p. 42, a scalar in every factor contributes its m-th power. *)
Lemma symmetric_vector_power_scale (K : fieldType) (V : lmodType K) (v : V) c m :
  symmetric_vector_power (c *: v) m = c^+m *: symmetric_vector_power v m.
Proof. by rewrite !symmetric_vector_powerE linearZ algebra_power_scale. Qed.

(** Source for [symmetric_vector_power_homogeneous]: Federer
    1.9.3, p. 42, the m-th power belongs to the m-th symmetric component. *)
Lemma symmetric_vector_power_homogeneous (K : fieldType) (V : lmodType K) (v : V) m :
  homogeneous (symmetric_grading V) m (symmetric_vector_power v m).
Proof.
have h := symmetric_word_homogeneous (nseq m v).
by rewrite size_nseq in h.
Qed.

(** Source for [symmetric_divided_vector_power]: Federer
    1.9.3, p. 42, the divided power v^m/m! in the multinomial formula. *)
Definition symmetric_divided_vector_power (K : fieldType) (V : lmodType K) (v : V) m :=
  (m`!%:R : K)^-1 *: symmetric_vector_power v m.

(** Source for [symmetric_divided_monomial]: Federer 1.9.3,
    p. 42, the divided monomial v^alpha/alpha! on the right
    side of the multinomial formula. *)
Definition symmetric_divided_monomial (K : fieldType) (V : lmodType K)
    n (v : 'I_n -> V) (a : symmetric_multi_index n) :=
  ((symmetric_multi_factorial a)%:R : K)^-1 *: symmetric_monomial v a.

(** Source for [symmetric_multi_factorial_nonzero]: Federer
    1.9.3, p. 42, supporting justification of division by
    alpha!: in characteristic zero the finite product of factorials
    is nonzero. The printed formula is over the real field. *)
Lemma symmetric_multi_factorial_nonzero (K : fieldType) (h0 : [pchar K] =i pred0)
    n (a : symmetric_multi_index n) : ((symmetric_multi_factorial a)%:R : K) != 0.
Proof.
rewrite /symmetric_multi_factorial natr_prod; apply/prodf_neq0=> i _.
exact (@characteristic_zero_factorial K h0 (a i)).
Qed.
