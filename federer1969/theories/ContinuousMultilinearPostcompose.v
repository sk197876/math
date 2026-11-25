(** Federer (1969), 3.1.11, pp. 219–220:
    a bounded linear map on the target acts
    on every space of continuous multilinear maps.
    Existence and bounds follow from the abstract
    representation and least-norm laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continuous_multilinear_postcompose_exists]:
    target-linear composition on continuous k-linear
    maps, supporting the higher chain rule of
    Federer 3.1.11, p. 220.
    The lift is characterized by evaluation and
    has a proved finite operator bound. *)
Theorem continuous_multilinear_postcompose_exists (R : realType) k
    (X U V P Q : lmodType R)
    (NX : X->R) (NU : U->R) (NV : V->R)
    (ep : {ffun 'I_k->X}->Hom P U) (PN : P->R)
    (eq : {ffun 'I_k->X}->Hom Q V) (QN : Q->R)
    (hP : is_continuous_multilinear_space NX NU ep PN)
    (hQ : is_continuous_multilinear_space NX NV eq QN)
    (M : Hom U V) :
  norm_bounded_linear NU NV M ->
  exists K : Hom P Q,
    (forall z u, eq u (K z)=M (ep u z)) /\
    norm_bounded_linear PN QN K.
Proof.
move=> [C [hC hM]].
have hf z : norm_bounded_multilinear NX NV (fun u=>M (ep u z)).
  split.
  - move=> u i c x y.
    by rewrite (continuous_multilinear_evaluation hP z) (hom_linear M).
  - exists (C*PN z); split.
    + exact: mulr_ge0 hC
        (multilinear_operator_nonnegative (continuous_multilinear_norm_laws hP z)).
    + move=> u; apply: le_trans (hM (ep u z)) _.
      rewrite -mulrA; apply: (ler_wpM2l hC).
      exact (multilinear_operator_bound (continuous_multilinear_norm_laws hP z) u).
have hex z := continuous_multilinear_surjective hQ (hf z).
have [kmap hk] := choice hex.
have hlin : linear kmap.
  move=> c z w; apply: (continuous_multilinear_extensional hQ)=>u.
  by rewrite hk (hom_linear (eq u)) !hk (hom_linear (ep u)) (hom_linear M).
pose K := @HomMap R P Q kmap (introT (asboolP _) hlin).
exists K; split; first exact hk.
exists C; split=> // z.
apply: (multilinear_operator_least (continuous_multilinear_norm_laws hQ (K z))).
- exact: mulr_ge0 hC
    (multilinear_operator_nonnegative (continuous_multilinear_norm_laws hP z)).
- move=> u; rewrite /K /= hk.
  apply: le_trans (hM (ep u z)) _; rewrite -mulrA.
  apply: (ler_wpM2l hC).
  exact (multilinear_operator_bound (continuous_multilinear_norm_laws hP z) u).
Qed.

(** Source for [continuous_multilinear_postcompose_family_exists]:
    compatible target-linear lifts in all degrees,
    supporting the recursive higher differential in
    Federer 3.1.11, pp. 219–220.
    Compatibility is exactly the common evaluation formula. *)
Theorem continuous_multilinear_postcompose_family_exists (R : realType)
    (X U V : lmodType R) (NX : X->R) (NU : U->R) (NV : V->R)
    (P Q : nat->lmodType R)
    (ep : forall k, {ffun 'I_k->X}->Hom (P k) U) (PN : forall k, P k->R)
    (eq : forall k, {ffun 'I_k->X}->Hom (Q k) V) (QN : forall k, Q k->R)
    (hP : forall k, is_continuous_multilinear_space NX NU (@ep k) (@PN k))
    (hQ : forall k, is_continuous_multilinear_space NX NV (@eq k) (@QN k))
    (M : Hom U V) :
  norm_bounded_linear NU NV M ->
  exists K : forall k, Hom (P k) (Q k),
    (forall k z u, @eq k u (K k z)=M (@ep k u z)) /\
    forall k, norm_bounded_linear (@PN k) (@QN k) (K k).
Proof.
move=> hM.
have hex k := @continuous_multilinear_postcompose_exists R k X U V (P k) (Q k)
  NX NU NV (@ep k) (@PN k) (@eq k) (@QN k) (@hP k) (@hQ k) M hM.
pose K k := sval (constructive_indefinite_description (hex k)).
have hK k := svalP (constructive_indefinite_description (hex k)).
exists K; split.
- by move=> k; exact: (hK k).1.
- by move=> k; exact: (hK k).2.
Qed.
