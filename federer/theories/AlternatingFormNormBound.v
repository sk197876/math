(** Federer (1969), 4.1.6, p. 352: every alternating
    form on R^n with normed coefficients has the finite
    multilinear norm of 3.1.11, p. 219. The original
    1.7.5 exterior product bound and the finite-source
    linear bound prove this without completeness or finite
    dimension of the coefficient space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom RealNormUP TensorFamilyUP ExteriorGrading
  AlternatingForms AlternatingIsomorphism AlternatingPairing CovectorProducts
  FiniteExteriorPowers FiniteOrdinalBasis LinearBasis InnerProductUP InnerNorm HilbertFormCompactness
  InnerExteriorPositivity ExteriorNorm ExteriorHadamardBound ExteriorWordMultilinear
  NormDifferentialUP NormFiniteLinearBound ContinuousMultilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [form_ordered_value]: the original multilinear
    evaluation used to norm A^m(R^n,W), Federer
    4.1.6, p. 352, by 3.1.11, p. 219. *)
Definition form_ordered_value (K:fieldType) (V W:lmodType K) m
    (phi:A_m V W m) (u:{ffun 'I_m->V}):W:=
  pairing (e_lambda u (ord_tuple m)) phi.

(** Source for [form_ordered_value_tuple]: finite families
    evaluate to the same actual tuple values, supporting
    the norm and exterior derivative of Federer 4.1.6,
    p. 352. No alternate form carrier is substituted. *)
Lemma form_ordered_value_tuple (K:fieldType) (V W:lmodType K) m
    (phi:A_m V W m) (t:m.-tuple V):
  form_ordered_value phi [ffun i=>tnth t i]=phi t.
Proof.
rewrite /form_ordered_value pairing_e_lambda; congr (phi _).
by apply:eq_from_tnth=>i; rewrite tnth_map tnth_ord_tuple ffunE.
Qed.

(** Source for [form_ordered_value_multilinear]: actual
    alternating-form evaluation is multilinear in the
    original arguments, Federer 4.1.6, p. 352,
    using 1.4.1 and its exterior-power identification. *)
Lemma form_ordered_value_multilinear (K:fieldType) (V W:lmodType K) m
    (phi:A_m V W m):multilinear (form_ordered_value phi).
Proof.
have hWord:=@exterior_ordered_word_multilinear K V m.
move=>u i c v w; rewrite /form_ordered_value /pairing (hWord u i) linearP.
reflexivity.
Qed.

(** Source for [form_ordered_evaluation]: evaluation is
    linear in the original alternating form, supporting
    the induced norm in Federer 4.1.6, p. 352. *)
Definition form_ordered_evaluation (K:fieldType) (V W:lmodType K) m
    (u:{ffun 'I_m->V}):Hom (A_m V W m) W:=
  @HomMap K (A_m V W m) W (fun phi=>form_ordered_value phi u)
    (introT (asboolP _) ((@pairing_bilinear K V W m).2 (e_lambda u (ord_tuple m)))).

(** Source for [finite_source_alternating_form_bounded]: the
    norm on A^m(R^n,W) in Federer 4.1.6,
    p. 352, is finite. The earlier exterior Hadamard
    bound and finite-source linear bound apply to the
    original form_to_hom map. All degrees, including
    degree zero and degrees above the dimension, remain. *)
Theorem finite_source_alternating_form_bounded (R:realType)
    (h2:(1+1:R)!=0) (V W:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n (e:'I_n->V) (he:is_basis e)
    (NW:W->R) (hNW:is_real_norm NW) m (phi:A_m V W m):
  norm_bounded_multilinear (inner_norm hB) NW (form_ordered_value phi).
Proof.
split; first exact:form_ordered_value_multilinear.
have hBasis:=finite_e_lambda_basis he h2 m.
have hOrdinal:=finite_ordinal_basis hBasis.
have hExterior:=inner_norm_real_norm (@exterior_inner_productP R h2 V B hB m).
have[C [hC hBound]]:=norm_finite_linear_bounded hExterior hNW hOrdinal (form_to_hom phi).
exists C; split=>// u.
apply:le_trans (hBound (e_lambda u (ord_tuple m))) _.
exact:(ler_wpM2l hC (@exterior_product_norm_bound R h2 V B hB m u)).
Qed.
