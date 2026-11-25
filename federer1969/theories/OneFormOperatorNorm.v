(** Federer (1969), 4.1.6, pp. 352–355:
    one-form norms are exactly ordinary operator
    norms. Bounded coefficient maps therefore act
    continuously on the actual first-differential
    fields used for the pullback coordinate generators. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP
  NormOperatorNormUP ContinuousOperatorUP ContinuousMultilinearUP
  Alternating OneFormLinear OneFormIdentification CovectorProducts
  AlternatingFormNormUP AlternatingFormNormBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [ordered_one_form_value]: the original
    one-linear identification evaluates its one argument,
    supporting Federer 4.1.6, p. 352. *)
Lemma ordered_one_form_value (K:fieldType) (V W:lmodType K)
    (L:Hom V W) (u:{ffun 'I_1->V}):
  form_ordered_value (one_form L) u=L (u ord0).
Proof.
rewrite /form_ordered_value pairing_e_lambda.
have hTuple:[tuple of map u (ord_tuple 1)]=[tuple u ord0].
  by apply:eq_from_tnth=>i; rewrite (ord1 i) tnth_map tnth_ord_tuple.
by rewrite hTuple one_formE.
Qed.

(** Source for [one_form_operator_norm]: the actual
    induced one-form norm is the original ordinary
    operator norm, Federer 4.1.6, p. 352. *)
Theorem one_form_operator_norm (R:realType) (V W:lmodType R)
    (NV:V->R) (NW:W->R) (P:A_m V W 1->R)
    (hP:is_alternating_form_norm NV NW P) (L:Hom V W):
  is_norm_operator_norm NV NW L (P (one_form L)).
Proof.
constructor.
- exact:multilinear_operator_nonnegative (hP (one_form L)).
- move=>v; have h:=multilinear_operator_bound (hP (one_form L)) [ffun i:'I_1=>v].
  by rewrite ordered_one_form_value big_ord1 !ffunE in h.
- move=>C hC hBound; apply:(multilinear_operator_least (hP (one_form L)) hC)=>u.
  rewrite ordered_one_form_value big_ord1; exact:hBound.
Qed.

(** Source for [one_form_postoperator_exists]: the
    actual first-operator field may be followed by
    a bounded coefficient functional and identified
    with one-forms, supporting the generator proof
    of Federer 4.1.6, p. 355. *)
Theorem one_form_postoperator_exists (R:realType) (V Y W Z:lmodType R)
    (NV:V->R) (NY:Y->R) (NW:W->R) (P:A_m V W 1->R)
    (hP:is_alternating_form_norm NV NW P)
    (J:Hom Z (Hom V Y)) (ZN:Z->R)
    (hZ:is_continuous_operator_space NV NY J ZN) (M:Hom Y W):
  norm_bounded_linear NY NW M->
  exists K:Hom Z (A_m V W 1),
    (forall z v,one_hom (K z) v=M (J z v)) /\norm_bounded_linear ZN P K.
Proof.
move=>[C [hC hBound]].
have hLinear:linear (fun z=>one_form (hom_comp M (J z))).
  move=>c z w; rewrite (linearP J) (hom_postcompose_linear M).
  exact:linearP.
pose K:Hom Z (A_m V W 1):=@HomMap R _ _ _ (introT (asboolP _) hLinear).
exists K; split.
- move=>z v.
  change (one_hom (one_form (hom_comp M (J z))) v=M (J z v)).
  by rewrite one_formK hom_compE.
- exists C; split=>// z.
  apply:(norm_operator_least (one_form_operator_norm hP (hom_comp M (J z)))).
  + exact:mulr_ge0 hC (norm_operator_nonnegative (continuous_operator_norm_laws hZ z)).
  + move=>v; rewrite hom_compE.
    apply:le_trans (hBound (J z v)) _.
    rewrite -mulrA; exact:(ler_wpM2l hC (norm_operator_bound (continuous_operator_norm_laws hZ z) v)).
Qed.
