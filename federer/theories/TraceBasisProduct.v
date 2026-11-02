(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import DualExterior.
From Federer Require Import TraceAlgebra TraceDefinition WordPairing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5, trace contraction: multiplication of homogeneous
    pure tensors is followed by the pairing which defines trace. *)
(** Source for [ordinary_tensor_productE]: Federer (1969), 1.4.5, pp. 20-21,
    last display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Supporting lemma for this passage; not separately stated in
    the book. The local LaTeX erratum (May 1987), p. 1, entry for book p. 20
    line 32, corrects the identity to the identity on the j-th exterior
    power. *)
Lemma ordinary_tensor_productE (K : fieldType) (B C : algebra K)
    (a c : B) (b d : C) :
  alg_mul (algebra_tensor B C) (tensor_inj a b) (tensor_inj c d) =
  tensor_inj (alg_mul B a c) (alg_mul C b d).
Proof. exact: tensor_multiplicationE. Qed.
Section TraceProduct.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Local Notation U := (alternating_unital_algebra h2 V (scalar_algebra K)).
Local Notation E := (exterior_algebra V).
Local Notation D := (A h2 V V).
Local Notation include := (@A_include K h2 V V).
(** Source for [trace_pure_product]: Federer (1969), 1.4.5, pp. 20-21, last
    display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Supporting lemma for this passage; not separately stated in
    the book. The local LaTeX erratum (May 1987), p. 1, entry for book p. 20
    line 32, corrects the identity to the identity on the j-th exterior
    power. *)
Lemma trace_pure_product m j (phi : A_m V K^o m) (psi : A_m V K^o j)
    (xi : exterior_power V m) (eta : exterior_power V j) :
  trace h2 V (alg_mul D (A_pure h2 phi xi) (A_pure h2 psi eta)) =
    (alg_mul U (form_include phi) (form_include psi))
      (wedge (component_val xi) (component_val eta)).
Proof.
transitivity (trace_tensor h2 V (alg_mul (algebra_tensor U E)
  (include (A_pure h2 phi xi)) (include (A_pure h2 psi eta)))).
- exact (congr1 (trace_tensor h2 V) (algebra_map_mul include _ _)).
- by rewrite !A_pureE ordinary_tensor_productE trace_tensorE.
Qed.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation omega := (fun i => one_form (dual_basis he i)).
(** Source for [omega_lambda_word]: Federer (1969), 1.4.5, pp. 20-21, last
    display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Supporting lemma for this passage; not separately stated in
    the book. The local LaTeX erratum (May 1987), p. 1, entry for book p. 20
    line 32, corrects the identity to the identity on the j-th exterior
    power. *)
Lemma omega_lambda_word m (lambda : Lambda n m) :
  form_include (omega_lambda h2 omega lambda) = omega_word h2 he (val lambda).
Proof. by rewrite -Omega_e_lambda Omega_m_include e_lambdaE. Qed.
(** Source for [omega_word_product]: Federer (1969), 1.4.5, pp. 20-21, last
    display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Supporting lemma for this passage; not separately stated in
    the book. The local LaTeX erratum (May 1987), p. 1, entry for book p. 20
    line 32, corrects the identity to the identity on the j-th exterior
    power. *)
Lemma omega_word_product (s t : seq 'I_n) :
  alg_mul U (omega_word h2 he s) (omega_word h2 he t) = omega_word h2 he (s++t).
Proof.
rewrite /omega_word -algebra_map_mul.
change (Omega h2 V (wedge (exterior_word [seq dual_basis he i | i <- s])
  (exterior_word [seq dual_basis he i | i <- t])) =
  Omega h2 V (exterior_word [seq dual_basis he i | i <- s++t])).
by rewrite exterior_word_cat map_cat.
Qed.
(** Source for [trace_basis_product]: Federer (1969), 1.4.5, pp. 20-21, last
    display of p. 20 and its hypotheses at the top of p. 21. In words:
    Multiplying a degree-m diagonal tensor by Gamma of the identity on the
    j-th exterior power multiplies its trace by binomial(n-m,j), for
    0<=j<=n-m. Formalises the indicated part of the passage under the
    hypotheses in the statement below. The local LaTeX erratum (May 1987),
    p. 1, entry for book p. 20 line 32, corrects the identity to the
    identity on the j-th exterior power. *)
Theorem trace_basis_product m j (lambda mu : Lambda n m) (kappa : Lambda n j) :
  trace h2 V (alg_mul D
    (A_pure h2 (omega_lambda h2 omega lambda) (e_lambda e (val mu)))
    (A_pure h2 (omega_lambda h2 omega kappa) (e_lambda e (val kappa)))) =
  if (lambda == mu) && uniq (val lambda ++ val kappa) then 1 else 0.
Proof.
rewrite trace_pure_product !omega_lambda_word omega_word_product !e_lambdaE exterior_word_cat -map_cat.
exact: omega_word_shared.
Qed.
End TraceProduct.
