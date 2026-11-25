(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorMultiplication.
From Federer Require Import DualityMaps DualityBasis TopComplements
  InteriorSigns InteriorBasisEvaluation CovectorWords.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.2: the inverse equations for D_p and D^(n-p).
    On complementary basis products their two signs are the same,
    so their product is one. *)
Section Inverse.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Variable omega : 'I_n -> A_m V K^o 1.
Hypothesis he : is_basis e.
Hypothesis hdual : forall i j, omega i [tuple e j] = if i == j then 1 else 0.
Local Notation et := (e_lambda e (val (Lambda_top n))).
Local Notation ot := (omega_lambda h2 omega (Lambda_top n)).
(** Source for [D_upper_inverse]: Federer (1969), 1.5.2, p. 22, inverse and
    basis-dependence assertions in the last paragraph. In words: The duality
    maps in complementary degrees are mutually inverse and depend only on
    the chosen dual top-degree elements. Definition or construction used to
    formalise this passage. *)
Definition D_upper_inverse p (hp : (p <= n)%N) (xi : exterior_power V (n-p)) : A_m V K^o p :=
  form_reindex (subKn hp) (D_p ot (leq_subr p n) xi).
(** Source for [D_upper_inverse_linear]: Federer (1969), 1.5.2, p. 22,
    inverse and basis-dependence assertions in the last paragraph. In words:
    The duality maps in complementary degrees are mutually inverse and
    depend only on the chosen dual top-degree elements. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma D_upper_inverse_linear p hp : linear (@D_upper_inverse p hp).
Proof. by move=> a xi eta; rewrite /D_upper_inverse !linearP. Qed.
HB.instance Definition _ p hp := GRing.isLinear.Build K (exterior_power V (n-p)) (A_m V K^o p)
  *:%R (@D_upper_inverse p hp) (@D_upper_inverse_linear p hp).
(** Source for [D_upper_inverse_basisK]: Federer (1969), 1.5.2, p. 22,
    inverse and basis-dependence assertions in the last paragraph. In words:
    The duality maps in complementary degrees are mutually inverse and
    depend only on the chosen dual top-degree elements. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma D_upper_inverse_basisK p hp (lambda : Lambda n p) :
  @D_upper_inverse p hp (D_upper h2 et hp (omega_lambda h2 omega lambda)) = omega_lambda h2 omega lambda.
Proof.
rewrite (@D_upper_basis K h2 V n e omega he hdual p hp lambda) linearZ.
apply: (@pairing_basis_ext K h2 V n p e he) => mu.
rewrite (bilZr (@pairing_bilinear K V K^o p)).
change ((-1 : K)^+(FedererInteriorSigns.N lambda (top_complement lambda)) *:
  form_homogeneous (D_upper_inverse hp (e_lambda e (val (top_complement lambda))))
    (component_val (e_lambda e (val mu))) = pairing (e_lambda e (val mu)) (omega_lambda h2 omega lambda)).
rewrite /D_upper_inverse form_reindexE D_pE !e_lambdaE exterior_word_cat -map_cat.
have hs : size (val mu ++ val (top_complement lambda)) = n.
  by rewrite size_cat !size_tuple subnKC.
change ((-1 : K)^+(FedererInteriorSigns.N lambda (top_complement lambda)) *:
  form_include ot (exterior_word [seq e i | i <- val mu ++ val (top_complement lambda)]) =
  pairing (e_lambda e (val mu)) (omega_lambda h2 omega lambda)).
rewrite (@basis_word_pairing_seq K h2 V n e omega hdual n
  (val mu ++ val (top_complement lambda)) (Lambda_top n) hs) top_complement_shared_right
  (pairing_e_omega h2 hdual) (eq_sym lambda mu).
case hm: (mu == lambda).
- move/eqP: hm => ->; rewrite -FedererInteriorSigns.N_inversions.
  change ((-1 : K)^+(FedererInteriorSigns.N lambda (top_complement lambda)) *
    (-1 : K)^+(FedererInteriorSigns.N lambda (top_complement lambda)) = 1).
  by rewrite -exprMn mulrNN mul1r expr1n.
- exact: scaler0.
Qed.
(** Source for [D_upperK]: Federer (1969), 1.5.2, p. 22, inverse and
    basis-dependence assertions in the last paragraph. In words: The duality
    maps in complementary degrees are mutually inverse and depend only on
    the chosen dual top-degree elements. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Theorem D_upperK p hp : cancel (D_upper h2 et hp) (@D_upper_inverse p hp).
Proof.
apply: (@basis_linear_ext K (Choice.clone (Lambda n p) _) (A_m V K^o p)
  (@omega_lambda K h2 V n omega p) (@omega_lambda_basis K h2 V n p e omega he hdual) (A_m V K^o p)
  (linear_comp (GRing.Linear.clone _ _ _ _ (@D_upper_inverse p hp) _) (GRing.Linear.clone _ _ _ _ (D_upper h2 et hp) _))
  (linear_id (A_m V K^o p))).
exact: D_upper_inverse_basisK.
Qed.
End Inverse.
