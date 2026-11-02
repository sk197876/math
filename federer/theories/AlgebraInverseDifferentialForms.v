(** Federer (1969), 3.1.11, p. 220:
    the symmetric multilinear forms given by the
    printed permutation formula for inversion.
    Their identification with actual differentials is separate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp fingroup perm reals ring.
From Federer Require Import Hom AlgebraUP AlgebraPowers Bilinear WordEvaluation PowerWords
  RealNormUP TensorFamilyUP ContinuousMultilinearUP FiniteArgumentPermutation
  MultilinearPermutationSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section InverseForms.
Variable R : realType.
Variable A : algebra R.

(** Source for [inverse_differential_factor]:
    the factor -T^(-1) S in the
    inverse series and derivative formula,
    Federer 3.1.11, p. 220. *)
Definition inverse_differential_factor (v h : A) := -alg_mul A v h.

(** Source for [inverse_differential_factor_linear]:
    the perturbation enters linearly, supporting
    the inverse differential formula in
    Federer 3.1.11, p. 220. *)
Lemma inverse_differential_factor_linear v :
  linear (inverse_differential_factor v).
Proof.
move=>c x y; rewrite /inverse_differential_factor (alg_bilinear A).2
  opprD -scalerN; by [].
Qed.

(** Source for [inverse_differential_ordered_word]:
    the ordered summand (-1)^k v S_1 v
    ... S_k v in Federer 3.1.11,
    p. 220, written using the
    proved associative word evaluation from Chapter 1. *)
Definition inverse_differential_ordered_word (v : A) (s : seq A) :=
  alg_mul A (word_eval (inverse_differential_factor v) s) v.

(** Source for [inverse_differential_ordered]:
    the ordered k-linear summand in
    the permutation formula of Federer 3.1.11,
    p. 220. In degree zero
    its value is v. *)
Definition inverse_differential_ordered v k (u : {ffun 'I_k->A}) :=
  inverse_differential_ordered_word v (power_seq u).

(** Source for [inverse_differential_form]:
    the sum over every permutation of
    the k arguments, Federer 3.1.11,
    p. 220. This definition does
    not presume that it is a differential. *)
Definition inverse_differential_form v k (u : {ffun 'I_k->A}) :=
  multilinear_permutation_sum (@inverse_differential_ordered v k) u.

(** Source for [inverse_differential_ordered_multilinear]:
    multilinearity of each ordered inverse
    summand, Federer 3.1.11, p. 220. *)
Lemma inverse_differential_ordered_multilinear v k :
  multilinear (@inverse_differential_ordered v k).
Proof.
pose L := @HomMap R A A (inverse_differential_factor v)
  (introT (asboolP _) (inverse_differential_factor_linear v)).
have hw : multilinear_words (inverse_differential_ordered_word v).
  move=>s t c x y.
  have hh := word_eval_multilinear (hom_as_linear L) s t c x y.
  rewrite /inverse_differential_ordered_word hh.
  exact: (alg_bilinear A).1 v c _ _.
exact: multilinear_words_power hw.
Qed.

(** Source for [inverse_differential_form_multilinear]:
    the full permutation expression is
    multilinear, Federer 3.1.11, p. 220. *)
Lemma inverse_differential_form_multilinear v k :
  multilinear (@inverse_differential_form v k).
Proof. exact (multilinear_permutation_sum_multilinear (@inverse_differential_ordered_multilinear v k)). Qed.

(** Source for [inverse_differential_form_symmetric]:
    the inverse expression is symmetric
    in all arguments, Federer 3.1.11,
    p. 220. *)
Lemma inverse_differential_form_symmetric v k (s : 'S_k) u :
  inverse_differential_form v (finite_argument_permutation s u)=
    inverse_differential_form v u.
Proof. exact: multilinear_permutation_sum_symmetric. Qed.

(** Source for [inverse_differential_ordered_diagonal]:
    equal perturbations reduce the ordered
    product to (-v h)^k v,
    Federer 3.1.11, p. 220. *)
Lemma inverse_differential_ordered_diagonal v k h :
  inverse_differential_ordered v [ffun _ : 'I_k=>h]=
    alg_mul A (@AlgebraPowers.algebra_power R A (-alg_mul A v h) k) v.
Proof.
rewrite /inverse_differential_ordered /inverse_differential_ordered_word /power_seq.
have hm : [seq [ffun _ : 'I_k=>h] i | i<-enum 'I_k]=
    [seq h | i<-enum 'I_k].
  by apply: eq_map=>i; rewrite ffunE.
rewrite hm.
have he (r : seq 'I_k) :
    word_eval (inverse_differential_factor v) [seq h | i<-r]=
      @AlgebraPowers.algebra_power R A (-alg_mul A v h) (size r).
  elim:r=>[|i r ih] //=; by rewrite ih.
by rewrite he size_enum_ord.
Qed.

(** Source for [inverse_differential_form_diagonal]:
    the permutation expression evaluated on
    a repeated argument equals k! (-v h)^k v,
    Federer 3.1.11, p. 220. *)
Lemma inverse_differential_form_diagonal v k h :
  inverse_differential_form v [ffun _ : 'I_k=>h]=
    (k`!)%:R*:alg_mul A (@AlgebraPowers.algebra_power R A (-alg_mul A v h) k) v.
Proof.
by rewrite /inverse_differential_form multilinear_permutation_sum_diagonal
  inverse_differential_ordered_diagonal.
Qed.

Variable N : A->R.
Hypothesis hN : is_real_norm N.
Hypothesis hM : forall x y, N (alg_mul A x y)<=N x*N y.

(** Source for [inverse_differential_ordered_word_bound]:
    the ordered product is bounded by
    ||v||^(k+1) times the argument norm
    product, supporting Federer 3.1.11,
    p. 220, including degree zero. *)
Lemma inverse_differential_ordered_word_bound v s :
  N (inverse_differential_ordered_word v s)
    <=(N v)^+(size s).+1*\prod_(h<-s) N h.
Proof.
elim:s=>[|h s ih].
- by rewrite /inverse_differential_ordered_word /= alg_unitl expr1 big_nil mulr1.
- rewrite /inverse_differential_ordered_word /= -alg_assoc big_cons.
  have hf : N (inverse_differential_factor v h)<=N v*N h.
    rewrite /inverse_differential_factor (real_seminorm_negate hN.1); exact: hM.
  have hn0 := real_seminorm_nonnegative hN.1 v.
  have hh0 := real_seminorm_nonnegative hN.1 h.
  apply: le_trans (hM _ _) _.
  apply: le_trans (ler_wpM2l
    (real_seminorm_nonnegative hN.1 (inverse_differential_factor v h)) ih) _.
  have hP0 : 0<=(N v)^+(size s).+1*\prod_(a<-s) N a.
    apply: mulr_ge0; first exact: exprn_ge0 _ hn0.
    apply: prodr_ge0=>a _; exact (real_seminorm_nonnegative hN.1 a).
  have hh := ler_wpM2r hP0 hf.
  have he : (N v*N h)*((N v)^+(size s).+1*\prod_(a<-s) N a)=
      (N v)^+(size s).+2*(N h*\prod_(a<-s) N a).
    by rewrite [(N v)^+(size s).+2]exprS; ring.
  by rewrite he in hh.
Qed.

(** Source for [inverse_differential_form_bound]:
    the permutation expression has operator
    norm at most k! ||v||^(k+1),
    supporting its continuity in Federer
    3.1.11, p. 220. *)
Lemma inverse_differential_form_bound v k u :
  N (@inverse_differential_form v k u)<=
    ((k`!)%:R*(N v)^+k.+1)*\prod_(i<k) N (u i).
Proof.
apply: (multilinear_permutation_sum_bound hN)=>w.
have hh := inverse_differential_ordered_word_bound v (power_seq w).
by rewrite size_power_seq /power_seq big_map big_enum in hh.
Qed.

(** Source for [inverse_differential_form_representable]:
    the displayed symmetric expression belongs
    to the abstract continuous multilinear space
    used in Federer 3.1.11, p. 220.
    Its existence follows from that space's
    universal representation law. *)
Theorem inverse_differential_form_representable v k
    (Z : lmodType R) (ev : {ffun 'I_k->A}->Hom Z A) (ZN : Z->R)
    (hZ : is_continuous_multilinear_space N N ev ZN) :
  exists z, forall u, ev u z=inverse_differential_form v u.
Proof.
apply: (continuous_multilinear_surjective hZ).
split; first exact: inverse_differential_form_multilinear.
exists ((k`!)%:R*(N v)^+k.+1); split.
- exact: mulr_ge0 (ler0n _ _) (exprn_ge0 _ (real_seminorm_nonnegative hN.1 v)).
- exact: inverse_differential_form_bound.
Qed.
End InverseForms.
