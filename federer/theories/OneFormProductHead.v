(** Federer (1969), 4.1.6, p. 355: split
    the existing ordered product of one-forms at its
    first factor. The original product of 1.4.3
    is retained; no new product construction is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Alternating AlternatingProduct AlternatingUnit
  OneFormProducts ScalarCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [original_one_forms_wedge_empty]: the
    original empty product is the scalar unit,
    supporting the generator argument of
    Federer 4.1.6, p. 355. *)
Lemma original_one_forms_wedge_empty (K:fieldType) (h2:(1+1:K)!=0)
    (V:lmodType K) (a:'I_0->A_m V K^o 1):
  one_forms_wedge h2 (scalar_bilinear K) 1 a=@zero_form K V K^o 1.
Proof.
apply:(can_inj (@form_includeK K V K^o 0)).
by rewrite (one_forms_wedge_include h2 (scalar_bilinear K) (@mulr1 K))
  /one_forms_product enum_ord0 /=.
Qed.

(** Source for [original_one_forms_wedge_head]: separate
    the first of the original coordinate generators,
    supporting Federer 4.1.6, p. 355,
    including an empty remaining product. *)
Lemma original_one_forms_wedge_head (K:fieldType) (h2:(1+1:K)!=0)
    (V:lmodType K) m (a:'I_m.+1->A_m V K^o 1):
  one_forms_wedge h2 (scalar_bilinear K) 1 a=
    form_wedge h2 (scalar_bilinear K) (a ord0)
      (one_forms_wedge h2 (scalar_bilinear K) 1 (fun i:'I_m=>a (lift ord0 i))).
Proof.
apply:(can_inj (@form_includeK K V K^o m.+1)).
rewrite (@form_wedge_include K h2 V K^o _ (scalar_bilinear K) 1 m (a ord0)
  (one_forms_wedge h2 (scalar_bilinear K) 1 (fun i:'I_m=>a (lift ord0 i))))
  !(one_forms_wedge_include h2 (scalar_bilinear K) (@mulr1 K)).
by rewrite /one_forms_product enum_ordSl /= -!map_comp.
Qed.
