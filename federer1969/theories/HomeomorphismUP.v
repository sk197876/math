(** Federer (1969), 2.7.1, printed p. 121: open maps and homeomorphisms, as
    used in the definition of a homogeneous space ("for each x in X the map
    A^x ... is open with im A^x = X") and in the consequence "for each g in
    G the map A_g ... is a homeomorphism, with (A_g)^{-1} = A_{g^{-1}}".
    These notions belong to the general topology on which Federer's Chapter
    2 relies. A homeomorphism is specified together with its inverse; a
    homeomorphism without a named inverse is a map that has one. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_open_map]: the open maps of Federer 2.7.1,
    p. 121, "for each x in X the map A^x: G -> X ... is open". The
    image of every open set is open. Definition supporting 2.7.1. *)
Definition is_open_map (S T : topologicalType) (f : S -> T) : Prop :=
  forall U : set S, open U -> open (f @` U).

(** Source for [is_homeomorphism_with_inverse]: Federer 2.7.1,
    p. 121, "A_g is a homeomorphism, with (A_g)^{-1} = A_{g^{-1}}".
    The record specifies a homeomorphism f together with its inverse
    h: both maps are continuous and each cancels the other. Definition
    supporting 2.7.1. *)
Record is_homeomorphism_with_inverse (S T : topologicalType) (f : S -> T) (h : T -> S) : Prop := {
  (** Source for [homeomorphism_continuous]: continuity of the
      homeomorphism in Federer 2.7.1, p. 121. *)
  homeomorphism_continuous : continuous f;
  (** Source for [homeomorphism_inverse_continuous]: continuity of
      the inverse in Federer 2.7.1, p. 121. *)
  homeomorphism_inverse_continuous : continuous h;
  (** Source for [homeomorphism_left_inverse]: h o f = 1_S, Federer
      2.7.1, p. 121. *)
  homeomorphism_left_inverse : cancel f h;
  (** Source for [homeomorphism_right_inverse]: f o h = 1_T, Federer
      2.7.1, p. 121. *)
  homeomorphism_right_inverse : cancel h f
}.

(** Source for [is_homeomorphism]: the homeomorphism G/G^x ~ X of
    Federer 2.7.1, p. 122, "A^x induces a homeomorphism", whose
    inverse is not named. Definition supporting 2.7.1: some inverse
    map exists with the laws of [is_homeomorphism_with_inverse]. *)
Definition is_homeomorphism (S T : topologicalType) (f : S -> T) : Prop :=
  exists h : T -> S, is_homeomorphism_with_inverse f h.

Section HomeomorphismLaws.
Variables S T : topologicalType.

(** Source for [homeomorphism_with_inverse_symmetric]: the inverse
    of a homeomorphism is a homeomorphism, supporting Federer 2.7.1,
    p. 121. *)
Lemma homeomorphism_with_inverse_symmetric (f : S -> T) (h : T -> S) :
  is_homeomorphism_with_inverse f h -> is_homeomorphism_with_inverse h f.
Proof. by case=> hf hh hfh hhf; constructor. Qed.

(** Source for [homeomorphism_with_inverse_image]: the image under a
    homeomorphism is the inverse image under its inverse, supporting
    Federer 2.7.1, p. 121. *)
Lemma homeomorphism_with_inverse_image (f : S -> T) (h : T -> S) (U : set S) :
  is_homeomorphism_with_inverse f h -> f @` U = h @^-1` U.
Proof.
case=> _ _ hfh hhf; apply/seteqP; split=> y.
- by case=> x hx <-; rewrite /= hfh.
- by move=> hy; exists (h y)=> //; rewrite hhf.
Qed.

(** Source for [homeomorphism_with_inverse_open_map]: a
    homeomorphism is an open map, supporting Federer 2.7.1, p. 121. *)
Lemma homeomorphism_with_inverse_open_map (f : S -> T) (h : T -> S) :
  is_homeomorphism_with_inverse f h -> is_open_map f.
Proof.
move=> hfh U hU; rewrite (homeomorphism_with_inverse_image U hfh).
by move/continuousP: (homeomorphism_inverse_continuous hfh); apply.
Qed.

(** Source for [homeomorphism_with_inverse_homeomorphism]: a
    homeomorphism with a named inverse is a homeomorphism, Federer
    2.7.1, p. 121. *)
Lemma homeomorphism_with_inverse_homeomorphism (f : S -> T) (h : T -> S) :
  is_homeomorphism_with_inverse f h -> is_homeomorphism f.
Proof. by move=> hfh; exists h. Qed.

(** Source for [open_continuous_bijection_homeomorphism]: supporting
    the homeomorphism G/G^x ~ X of Federer 2.7.1, p. 122. A
    continuous open bijection is a homeomorphism; its inverse is
    chosen pointwise from surjectivity, and the inverse image of an
    open set under the inverse is the image of that set. *)
Lemma open_continuous_bijection_homeomorphism (f : S -> T) :
  continuous f -> is_open_map f -> injective f -> (forall y, exists x, f x = y) ->
  is_homeomorphism f.
Proof.
move=> hc ho hi hs.
pose h (y : T) : S := projT1 (cid (hs y)).
have hhf : cancel h f by move=> y; rewrite /h; case: (cid (hs y)).
have hfh : cancel f h by move=> x; apply: hi; rewrite hhf.
exists h; constructor=> //.
apply/continuousP=> U hU.
have -> : h @^-1` U = f @` U.
  apply/seteqP; split=> y.
  - by move=> hy; exists (h y)=> //; rewrite hhf.
  - by case=> x hx <-; rewrite /= hfh.
exact: ho.
Qed.

(** Source for [homeomorphism_surjective]: supporting surjectivity in
    Federer 2.7.1, p. 122: a homeomorphism maps onto its target. *)
Lemma homeomorphism_surjective (f : S -> T) : is_homeomorphism f -> forall y, exists x, f x = y.
Proof. by case=> h hfh y; exists (h y); exact: homeomorphism_right_inverse hfh y. Qed.

(** Source for [homeomorphism_injective]: supporting injectivity in
    Federer 2.7.1, p. 122: a homeomorphism is injective. *)
Lemma homeomorphism_injective (f : S -> T) : is_homeomorphism f -> injective f.
Proof. by case=> h hfh; exact: can_inj (homeomorphism_left_inverse hfh). Qed.

End HomeomorphismLaws.
