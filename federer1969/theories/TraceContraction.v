(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import DualExterior.
From Federer Require Import TraceAlgebra TraceComponents TraceDefinition
  GammaPower TraceBasisProduct LambdaComplements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5, trace contraction display: Gamma of the identity
    on the j-th exterior power, and its action under trace. *)
(** Source for [algebra_sum_right]: Federer (1969), 1.4.5, pp. 20-21, last
    display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Supporting lemma for this passage; not separately stated in
    the book. The local LaTeX erratum (May 1987), p. 1, entry for book p. 20
    line 32, corrects the identity to the identity on the j-th exterior
    power. *)
Lemma algebra_sum_right (K : fieldType) (B : algebra K) (I : finType) x (f : I -> B) :
  alg_mul B x (\sum_i f i) = \sum_i alg_mul B x (f i).
Proof. exact (linear_sum (algebra_left x) _ _ _). Qed.
Section TraceContraction.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation D := (A h2 V V).
Local Notation omega := (fun i => one_form (dual_basis he i)).
(** Source for [Gamma_identity]: Federer (1969), 1.4.5, pp. 20-21, last
    display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Definition or construction used to formalise this passage.
    The local LaTeX erratum (May 1987), p. 1, entry for book p. 20 line 32,
    corrects the identity to the identity on the j-th exterior power. *)
Definition Gamma_identity j : D := @Gamma_power_A K h2 V V n e he j
  (hom_of_linear (linear_id (exterior_power V j))).
(** Source for [Gamma_identityE]: Federer (1969), 1.4.5, pp. 20-21, last
    display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Supporting lemma for this passage; not separately stated in
    the book. The local LaTeX erratum (May 1987), p. 1, entry for book p. 20
    line 32, corrects the identity to the identity on the j-th exterior
    power. *)
Lemma Gamma_identityE j : Gamma_identity j =
  \sum_(kappa : Lambda n j) A_pure h2 (omega_lambda h2 omega kappa) (e_lambda e (val kappa)).
Proof. exact: Gamma_power_AE. Qed.
(** Source for [trace_right]: Federer (1969), 1.4.5, pp. 20-21, last display
    of p. 20 and its hypotheses at the top of p. 21. In words: Multiplying a
    degree-m diagonal tensor by Gamma of the identity on the j-th exterior
    power multiplies its trace by binomial(n-m,j), for 0<=j<=n-m. Definition
    or construction used to formalise this passage. The local LaTeX erratum
    (May 1987), p. 1, entry for book p. 20 line 32, corrects the identity to
    the identity on the j-th exterior power. *)
Definition trace_right (eta : D) : {linear D -> K^o} :=
  linear_comp (trace h2 V) (algebra_right eta).
(** Source for [trace_rightE]: Federer (1969), 1.4.5, pp. 20-21, last
    display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Supporting lemma for this passage; not separately stated in
    the book. The local LaTeX erratum (May 1987), p. 1, entry for book p. 20
    line 32, corrects the identity to the identity on the j-th exterior
    power. *)
Lemma trace_rightE eta zeta : trace_right eta zeta = trace h2 V (alg_mul D zeta eta).
Proof. by []. Qed.
(** Source for [trace_contraction_basis]: Federer (1969), 1.4.5, pp. 20-21,
    last display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Supporting lemma for this passage; not separately stated in
    the book. The local LaTeX erratum (May 1987), p. 1, entry for book p. 20
    line 32, corrects the identity to the identity on the j-th exterior
    power. *)
Lemma trace_contraction_basis m j (lambda mu : Lambda n m) :
  trace_right (Gamma_identity j)
    (A_pure h2 (omega_lambda h2 omega lambda) (e_lambda e (val mu))) =
  ('C(n-m,j)%:R : K) *:
    trace h2 V (A_pure h2 (omega_lambda h2 omega lambda) (e_lambda e (val mu))).
Proof.
rewrite trace_rightE Gamma_identityE.
rewrite algebra_sum_right linear_sum.
under eq_bigr do rewrite trace_basis_product.
rewrite trace_pure (pairing_e_omega h2 (Gamma_dualE he)).
case hm : (lambda == mu) => /=.
- change ((\sum_(kappa : Lambda n j)
    (if uniq (val lambda ++ val kappa) then 1 else 0 : K)) = ('C(n-m,j)%:R : K)*1).
  by rewrite -big_mkcond sumr_const mulr1 card_Lambda_complement.
- rewrite scaler0; apply: big1 => kappa _; by [].
Qed.
(** Source for [trace_contraction_component]: Federer (1969), 1.4.5, pp.
    20-21, last display of p. 20 and its hypotheses at the top of p. 21. In
    words: Multiplying a degree-m diagonal tensor by Gamma of the identity
    on the j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Formalises the indicated part of the passage under the
    hypotheses in the statement below. The local LaTeX erratum (May 1987),
    p. 1, entry for book p. 20 line 32, corrects the identity to the
    identity on the j-th exterior power. *)
Lemma trace_contraction_component m j (t : tensor_space (A_m V K^o m) (exterior_power V m)) :
  trace_right (Gamma_identity j) (@A_component K h2 V V m t) =
  ('C(n-m,j)%:R : K) *: trace h2 V (@A_component K h2 V V m t).
Proof.
pose L : {linear tensor_space (A_m V K^o m) (exterior_power V m) -> K^o} :=
  linear_comp (trace_right (Gamma_identity j)) (@A_component K h2 V V m).
pose R : {linear tensor_space (A_m V K^o m) (exterior_power V m) -> K^o} :=
  linear_comp (@scalar_map K K^o ('C(n-m,j)%:R))
    (linear_comp (trace h2 V) (@A_component K h2 V V m)).
change (L t = R t).
have hb := tensor_basisP
  (@omega_lambda_basis K h2 V n m e omega he (Gamma_dualE he))
  (finite_e_lambda_basis he h2 m).
apply: (basis_linear_ext hb L R) t => [[lambda mu]].
change (trace_right (Gamma_identity j)
  (@A_component K h2 V V m (tensor_inj (omega_lambda h2 omega lambda) (e_lambda e (val mu)))) =
  ('C(n-m,j)%:R : K) *: trace h2 V
  (@A_component K h2 V V m (tensor_inj (omega_lambda h2 omega lambda) (e_lambda e (val mu))))).
by rewrite A_componentE trace_contraction_basis.
Qed.
(** Source for [trace_contraction]: Federer (1969), 1.4.5, pp. 20-21, last
    display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Formalises the indicated part of the passage under the
    hypotheses in the statement below. The local LaTeX erratum (May 1987),
    p. 1, entry for book p. 20 line 32, corrects the identity to the
    identity on the j-th exterior power. *)
Theorem trace_contraction m j (zeta : D) : homogeneous (A_grading h2 V V) m zeta ->
  trace h2 V (alg_mul D zeta (Gamma_identity j)) = ('C(n-m,j)%:R : K) *: trace h2 V zeta.
Proof.
move=> hz; have [t <-] := (proj1 (@A_component_image K h2 V V m zeta)) hz.
exact: trace_contraction_component.
Qed.
End TraceContraction.

(** Federer 1.4.5: the unit has trace one, including when V is zero. *)
(** Source for [trace_unit]: Federer (1969), 1.4.5, p. 20, definition of
    trace by its value on a homogeneous pure tensor. In words: Trace is the
    linear functional on the diagonal algebra taking a covector tensored
    with an m-vector to their evaluation pairing. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma trace_unit (K : fieldType) (h2 : (1+1 : K) != 0) (V : lmodType K) :
  trace h2 V (alg_one (A h2 V V)) = 1.
Proof.
change (trace_tensor h2 V (tensor_inj (coefficient_form V (1 : K^o)) (exterior_unit V)) = 1).
rewrite trace_tensorE coefficient_formE.
by rewrite exterior_augmentation_unit scale1r.
Qed.
(** Source for [A_unit_nonzero]: Federer (1969), 1.4.5, p. 20, definition of
    trace by its value on a homogeneous pure tensor. In words: Trace is the
    linear functional on the diagonal algebra taking a covector tensored
    with an m-vector to their evaluation pairing. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma A_unit_nonzero (K : fieldType) (h2 : (1+1 : K) != 0) (V : lmodType K) :
  alg_one (A h2 V V) != 0.
Proof.
apply/eqP=> h; have /eqP ht := congr1 (trace h2 V) h.
by rewrite trace_unit linear0 oner_eq0 in ht.
Qed.
