(** Allard (1972), 2.2(1) and 2.2(2), printed p. 421: the expansion
    det(1 + t f) = Σ_{i=0}^{m} t^i trace(∧_i f) for f ∈ Hom(V, V),
    m = dim V, and the identity (∧_k f)^* = ∧_k(f^* ) for f ∈ Hom(V, W),
    where ∧_k V carries the inner product of Federer 1.7.5. Both are
    restatements of Federer 1.4.5, p. 21 (determinant_identity_add with
    exterior_traceE), and 1.7.6, p. 33 (exterior_power_adjoint). *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP LinearBasis TensorUP Hom AdjointUP AdjointLaws Adjoint
  ExteriorGrading ExteriorMaps ExteriorDeterminant FiniteExteriorPowers FiniteOrdinalBasis
  InnerExterior InnerExteriorPositivity ExteriorAdjoint CharacteristicPolynomial
  CharacteristicIdentities.
From Allard Require Import AllardHomInnerProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Determinant.
Variable R : realType.
Variable V : lmodType R.
Variable m : nat.
Variable e : 'I_m -> V.
Hypothesis he : is_basis e.
Local Notation h2 := (real_two_nonzero R).

(** Source for [allard_2_2_1]: Allard 2.2(1), p. 421: "det(1 + t f) =
    Σ_{i=0}^{m} t^i trace(∧_i f) whenever t ∈ R and f ∈ Hom(V, V)", where
    m = dim V is the length of the basis e. The determinant is that of
    Federer 1.3.4 and trace(∧_i f) is exterior_trace of Federer 1.4.5, p. 21.
    Direct formalisation. *)
Theorem allard_2_2_1 (f : Hom V V) (t : R) :
  det h2 he (hom_as_linear (hom_of_linear (linear_id V) + t *: f)) =
  \sum_(i < m.+1) t ^+ i * exterior_trace h2 he f i.
Proof.
rewrite (determinant_identity_add h2 (@pchar_num R) he f t).
by apply: eq_bigr=> i _; rewrite exterior_traceE.
Qed.
End Determinant.

Section ExteriorAdjoint.
Variable R : realType.
Variables V W : lmodType R.
Variables (B : V -> V -> R) (C : W -> W -> R).
Hypotheses (hB : is_inner_product B) (hC : is_inner_product C).
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation h2 := (real_two_nonzero R).

(** Source for [allard_2_2_2]: Allard 2.2(2), p. 421: "(∧_k f)^* = ∧_k(f^* )
    for f ∈ Hom(V, W)", the adjoints being taken with respect to the inner
    products of Federer 1.7.5 on ∧_k V and ∧_k W; the adjoint on the left
    is the one of Federer 1.7.4 computed with the basis e_λ of ∧_k V,
    Federer 1.3.2. Direct formalisation, from Federer 1.7.6, p. 33. *)
Theorem allard_2_2_2 (f : {linear V -> W}) k :
  inner_adjoint (exterior_inner_productP h2 hB k) (exterior_inner_productP h2 hC k)
    (finite_ordinal_basis (finite_e_lambda_basis hb h2 k)) (exterior_power_map f k) =1
  exterior_power_map (inner_adjoint hB hC hb f) k.
Proof.
apply: (adjoint_unique (exterior_inner_productP h2 hB k)).
- exact: inner_adjointP.
- exact (@exterior_power_adjoint R h2 V W B C hB hC f _ (inner_adjointP hB hC hb f) k).
Qed.
End ExteriorAdjoint.
