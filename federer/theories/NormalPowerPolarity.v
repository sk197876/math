(** Federer (1969), 1.8.2, p. 40: the top power of a
    normal-form two-form is k! times the coefficient product times
    the dual of the interleaved paired volume. This is the displayed
    power computation, expressed through the polarity gamma of 1.7.5. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import AlternatingCoordinates InnerProductUP InnerPolarity
  InnerExterior InnerExteriorProducts PairedRealVectors PairedFormProducts
  TwoFormPowers TwoFormNormalPowers ConcatenatedFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [normal_two_form_power_polarity]: Federer 1.8.2,
    p. 40, A^k=k! lambda_1 ... lambda_k times the dual paired
    volume. Algebraically this holds without orthonormality. *)
Theorem normal_two_form_power_polarity (R : rcfType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    k (a b : 'I_k -> V) (lambda : 'I_k -> R) :
  two_form_power h2 (\sum_j lambda j *: form_wedge h2 (scalar_bilinear R)
    (inner_polarity hB (a j)) (inner_polarity hB (b j))) k =
  ((k`!%:R : R) * \prod_j lambda j) *:
    inner_exterior_form h2 hB (paired_real_vector a b).
Proof.
have hc : concatenate_family (fun j => inner_polarity hB (a j))
    (fun j => inner_polarity hB (b j)) =
    (fun j => inner_polarity hB (concatenate_family a b j)).
  apply: funext => j.
  by rewrite /concatenate_family; case: (split j).
have hp : inner_exterior_form h2 hB (paired_real_vector a b) =
    (-1 : R)^+'C(k,2) *: one_forms_wedge h2 (scalar_bilinear R) (1 : R^o)
      (concatenate_family (fun j => inner_polarity hB (a j))
        (fun j => inner_polarity hB (b j))).
  rewrite /paired_real_vector linearZ.
  change ((-1 : R)^+'C(k,2) *:
    inner_exterior_form h2 hB (e_lambda (concatenate_family a b) (ord_tuple (k+k))) =
    (-1 : R)^+'C(k,2) *: one_forms_wedge h2 (scalar_bilinear R) (1 : R^o)
      (concatenate_family (fun j => inner_polarity hB (a j))
        (fun j => inner_polarity hB (b j)))).
  by rewrite inner_exterior_product_covectors hc.
apply: (can_inj (@form_includeK R V R^o (k+k))).
by rewrite hp !linearZ normal_two_form_top_power paired_form_product_two_blocks.
Qed.
