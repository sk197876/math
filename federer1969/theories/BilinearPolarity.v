(** Federer (1969), 1.7.1, p. 27: the correspondence between bilinear forms
    and linear maps into one-forms. The characteristic equation is specified
    first and both directions are proved using the previously established
    Hom/one-form identification. Source context are recorded in
    InnerProductUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP AlternatingCoordinates OneFormIdentification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Correspondence.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation F := (A_m V K^o 1).

(** Source for [is_bilinear_polar_map]: Federer 1.7.1, p. 27,
    the connecting formula B(x,y)=<x,beta(y)>. This is the
    characteristic condition, independent of any construction. *)
Definition is_bilinear_polar_map (B : V -> V -> K)
  (beta : {linear V -> F}) := forall x y, beta y [tuple x] = B x y.

(** Source for [is_polarity]: Federer 1.7.1, p. 27,
    a linear map into one-forms is a polarity when its associated
    bilinear form is symmetric. *)
Definition is_polarity (beta : {linear V -> F}) :=
  forall x y, beta y [tuple x] = beta x [tuple y].

Variable B : V -> V -> K.
Hypothesis hb : @bilinear K V V K^o B.

(** Source for [bilinear_slice]: Federer 1.7.1, p. 27,
    supporting construction: fix the second argument of B. *)
Definition bilinear_slice y (x : V) : K^o := B x y.

(** Source for [bilinear_slice_linear]: Federer 1.7.1, p. 27,
    linearity of each slice is part of bilinearity. *)
Lemma bilinear_slice_linear y : linear (bilinear_slice y).
Proof. exact: (proj1 hb y). Qed.
HB.instance Definition _ y := GRing.isLinear.Build K V K^o *:%R
  (bilinear_slice y) (bilinear_slice_linear y).

(** Source for [bilinear_polarity]: Federer 1.7.1, p. 27,
    existence witness for the characteristic map beta. Each slice
    is viewed as a one-form using the established identification. *)
Definition bilinear_polarity y : F :=
  one_form (hom_of_linear (GRing.Linear.clone _ _ _ _ (bilinear_slice y) _)).

(** Source for [bilinear_polarityE]: Federer 1.7.1, p. 27,
    the constructed map satisfies the connecting formula exactly. *)
Lemma bilinear_polarityE x y : bilinear_polarity y [tuple x] = B x y.
Proof. by rewrite /bilinear_polarity one_formE hom_of_linearE. Qed.

(** Source for [bilinear_polarity_linear]: Federer 1.7.1,
    p. 27, the connecting map into one-forms is linear. *)
Lemma bilinear_polarity_linear : linear bilinear_polarity.
Proof.
move=> a y z; apply: form_ext => /tupleP [x t]; rewrite (tuple0 t).
by rewrite form_addE form_scaleE !bilinear_polarityE (proj2 hb x).
Qed.
HB.instance Definition _ := GRing.isLinear.Build K V F *:%R
  bilinear_polarity bilinear_polarity_linear.

(** Source for [bilinear_polarity_unique]: Federer 1.7.1,
    p. 27, one-to-one correspondence. The connecting equation
    uniquely determines the map into one-forms. *)
Theorem bilinear_polarity_unique (beta : {linear V -> F}) :
  is_bilinear_polar_map B beta -> beta =1 bilinear_polarity.
Proof.
move=> h y; apply: form_ext => /tupleP [x t]; rewrite (tuple0 t).
by rewrite bilinear_polarityE h.
Qed.

(** Source for [bilinear_polarity_exists]: Federer 1.7.1,
    p. 27, existence of a linear map satisfying the connecting formula. *)
Theorem bilinear_polarity_exists :
  exists beta : {linear V -> F}, is_bilinear_polar_map B beta.
Proof.
exists (GRing.Linear.clone _ _ _ _ bilinear_polarity _).
exact: bilinear_polarityE.
Qed.
End Correspondence.

Section Reverse.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation F := (A_m V K^o 1).
Variable beta : {linear V -> F}.

(** Source for [polarity_bilinear_form]: Federer 1.7.1,
    p. 27, the reverse direction of B(x,y)=<x,beta(y)>. *)
Definition polarity_bilinear_form x y := beta y [tuple x].

(** Source for [polarity_bilinear_formP]: Federer 1.7.1,
    p. 27, the form obtained from a linear map is bilinear. *)
Theorem polarity_bilinear_formP :
  @bilinear K V V K^o polarity_bilinear_form.
Proof.
split.
- move=> y; exact: (one_form_evaluation_linear (beta y)).
- move=> x a y z; by rewrite /polarity_bilinear_form linearP form_addE form_scaleE.
Qed.

(** Source for [polarity_correspondenceK]: Federer 1.7.1,
    p. 27, one-to-one correspondence: reconstructing a map from
    its associated bilinear form recovers the original map. *)
Theorem polarity_correspondenceK :
  bilinear_polarity polarity_bilinear_formP =1 beta.
Proof.
move=> y; apply: form_ext => /tupleP [x t]; rewrite (tuple0 t).
by rewrite bilinear_polarityE.
Qed.

(** Source for [polarity_symmetric_iff]: Federer 1.7.1,
    p. 27, final sentence. The map is a polarity exactly when
    its associated bilinear form is symmetric. *)
Theorem polarity_symmetric_iff :
  is_polarity beta <-> is_symmetric_bilinear polarity_bilinear_form.
Proof.
split; first by move=> h; split; [exact: polarity_bilinear_formP | exact: h].
by move=> [_ h].
Qed.
End Reverse.
