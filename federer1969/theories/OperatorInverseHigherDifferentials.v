(** Federer (1969), 3.1.11, p. 220: the kth differential of
    inversion on the continuous endomorphisms of a Banach space.
    The algebraic formula is transported through the public operator
    algebra laws, giving the printed compositions of linear maps. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm
  reals topology.
From Federer Require Import Hom AlgebraUP Bilinear WordEvaluation PowerWords
  RealNormUP NormMetric CompleteMetricUP ContinuousOperatorAlgebraUP
  ContinuousOperatorAlgebraLaws AlgebraInverseUP AlgebraInverse PartialFunctionUP
  ContinuousMultilinearUP FiniteArgumentPermutation MultilinearPermutationSum
  AlgebraInverseDifferentialForms NormHigherDifferentialUP
  NormAlgebraInverseHigherDifferentials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [operator_inverse_ordered_evaluation]: supporting
    transport of the ordered inverse products in Federer 3.1.11,
    p. 220. The product v S_1 v ... S_k v acts by the
    corresponding nested compositions, with the sign (-1)^k. *)
Lemma operator_inverse_ordered_evaluation (R : realType)
    (X : lmodType R) (NX : X->R) (E : algebra R)
    (evaluation : Hom E (Hom X X)) (EN : E->R)
    (hE : is_continuous_operator_algebra NX evaluation EN) v s x :
  evaluation (inverse_differential_ordered_word v s) x=
    (-1 : R)^+(size s)*:
      foldr (fun h y=>evaluation v (evaluation h y)) (evaluation v x) s.
Proof.
elim:s=>[|h s ih].
- by rewrite /inverse_differential_ordered_word /= alg_unitl scale1r.
- have he : inverse_differential_ordered_word v (h::s)=
      alg_mul E (inverse_differential_factor v h)
        (inverse_differential_ordered_word v s).
    by rewrite /inverse_differential_ordered_word /= -alg_assoc.
  rewrite he (operator_algebra_composition hE) hom_compE ih.
  have hn : evaluation (inverse_differential_factor v h)=
      -evaluation (alg_mul E v h).
    rewrite /inverse_differential_factor; exact: linearN.
  rewrite hn (operator_algebra_composition hE).
  change (-evaluation v (evaluation h
    ((-1 : R)^+(size s)*:
      foldr (fun h y=>evaluation v (evaluation h y)) (evaluation v x) s))=
    (-1 : R)^+(size s).+1*:
      evaluation v (evaluation h
        (foldr (fun h y=>evaluation v (evaluation h y)) (evaluation v x) s))).
  by rewrite !linearZ /= exprS mulN1r scaleNr scalerN.
Qed.

(** Source for [operator_inverse_permutation_evaluation]: the sum
    over all permutations in Federer 3.1.11, p. 220, evaluated
    on a vector. This includes the single empty composition at k=0. *)
Lemma operator_inverse_permutation_evaluation (R : realType)
    (X : lmodType R) (NX : X->R) (E : algebra R)
    (evaluation : Hom E (Hom X X)) (EN : E->R)
    (hE : is_continuous_operator_algebra NX evaluation EN) v k u x :
  evaluation (@inverse_differential_form R E v k u) x=
    \sum_(s : 'S_k) (-1 : R)^+k*:
      foldr (fun h y=>evaluation v (evaluation h y)) (evaluation v x)
        (power_seq (finite_argument_permutation s u)).
Proof.
rewrite /inverse_differential_form /multilinear_permutation_sum linear_sum.
have he (f : 'S_k->Hom X X) : (\sum_s f s) x=\sum_s f s x.
  by elim/big_rec2: _=>[|s y g _ <-]; rewrite ?hom_zeroE ?hom_addE.
rewrite he; apply: eq_bigr=>s _.
rewrite /inverse_differential_ordered
  (operator_inverse_ordered_evaluation hE) size_power_seq; by [].
Qed.

(** Source for [norm_operator_inverse_higher_differential_formula]:
    the displayed kth differential of the inversion operator on E,
    Federer 3.1.11, p. 220. Completeness of X supplies completeness
    of its continuous endomorphism algebra. All products are exposed as
    actual operator compositions, and no finite-dimensionality is assumed. *)
Theorem norm_operator_inverse_higher_differential_formula (R : realType)
    (X : lmodType R) (NX : X->R) (hNX : is_real_norm NX)
    (hcomplete : is_complete_metric_space (real_norm_metric_space hNX))
    (E : algebra R) (evaluation : Hom E (Hom X X)) (EN : E->R)
    (hE : is_continuous_operator_algebra NX evaluation EN)
    (Z : nat->lmodType R)
    (ev : forall j, {ffun 'I_j->E}->Hom (Z j) E)
    (ZN : forall j, Z j->R)
    (hZ : forall j, is_continuous_multilinear_space EN EN (@ev j) (@ZN j))
    (F : E->E)
    (hF : forall T, partial_function_domain (algebra_inverse E) T ->
      is_two_sided_algebra_inverse T (F T)) T k (z : Z k) :
  partial_function_domain (algebra_inverse E) T ->
  has_norm_higher_differential EN ev ZN
    (partial_function_domain (algebra_inverse E)) F k T z ->
  forall u x, evaluation (@ev k u z) x=
    \sum_(s : 'S_k) (-1 : R)^+k*:
      foldr (fun S y=>evaluation (F T) (evaluation S y)) (evaluation (F T) x)
        (power_seq (finite_argument_permutation s u)).
Proof.
move=>hT hz u x.
have hn := operator_algebra_norm_is_norm hNX hE.
have hm := operator_algebra_norm_product hE.
have hc := @operator_algebra_complete R X NX hNX E evaluation EN hE hcomplete.
have he := @norm_algebra_inverse_higher_differential_formula R E EN hn hm hc
  Z ev ZN hZ F hF T k z hT hz u.
rewrite he; exact (@operator_inverse_permutation_evaluation R X NX E
  evaluation EN hE (F T) k u x).
Qed.
