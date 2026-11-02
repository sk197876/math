(** Federer (1969), 1.6.4, p. 25, naturality reduction in the proof. The
    statements below supply the displayed naturality identities for actual
    products of one-forms, including empty products. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import SimpleVectors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [omega_lambda_top_product]: Federer 1.6.4, p. 25,
    product of the complete dual basis. Supporting notation identity:
    the product indexed by the top index is the ordered product of
    all members of the family. *)
Lemma omega_lambda_top_product (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) m (a : 'I_m -> A_m V K^o 1) :
  omega_lambda h2 a (Lambda_top m) = one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) a.
Proof.
rewrite /omega_lambda.
have he : (fun i => a (tnth (val (Lambda_top m)) i)) = a.
  by apply: funext => i; rewrite /Lambda_top tnth_ord_tuple.
by rewrite he.
Qed.

(** Source for [one_forms_wedge_natural]: Federer 1.6.4, p. 25, naturality
    paragraph. Direct supporting identity: pulling back a product of
    one-forms pulls back each factor, also for the empty product. *)
Theorem one_forms_wedge_natural (K : fieldType) (h2 : (1+1 : K) != 0)
  (V W : lmodType K) (f : {linear V -> W}) m (a : 'I_m -> A_m W K^o 1) :
  A_m_dual f (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) a) =
    one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) (fun i => A_m_dual f (a i)).
Proof.
apply: (can_inj (@form_includeK K V K^o m)).
rewrite -A_star_dual_include
  !(one_forms_wedge_include h2 (scalar_bilinear K) (@mulr1 K)) /one_forms_product.
have hprod (s : seq 'I_m) :
    A_star_dual f (foldr (alternating_wedge h2 (scalar_bilinear K))
      (coefficient_form W (1 : K^o)) [seq form_include (a i) | i <- s]) =
    foldr (alternating_wedge h2 (scalar_bilinear K))
      (coefficient_form V (1 : K^o)) [seq form_include (A_m_dual f (a i)) | i <- s].
  elim: s => [|i s ih] /=.
  - exact: (@A_star_dual_coefficient K V W (scalar_algebra K) f 1).
  - by rewrite A_star_dual_multiplicative A_star_dual_include ih.
exact: hprod.
Qed.

(** Source for [exterior_basis_product_natural]: Federer 1.6.4,
    p. 25, naturality reduction to the associated subspace. Supporting
    identity: the induced exterior map carries a basis product to
    the product of the images of its factors. *)
Lemma exterior_basis_product_natural (K : fieldType) (V W : lmodType K)
  (f : {linear V -> W}) m (e : 'I_m -> V) :
  exterior_power_map f m (e_lambda e (ord_tuple m)) =
    e_lambda (fun i => f (e i)) (ord_tuple m).
Proof.
apply: val_inj.
change (exterior_algebra_map f (component_val (e_lambda e (ord_tuple m))) =
  component_val (e_lambda (fun i => f (e i)) (ord_tuple m))).
by rewrite !e_lambdaE exterior_algebra_map_word -map_comp.
Qed.
