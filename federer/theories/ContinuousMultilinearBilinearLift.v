(** Federer (1969), 3.1.11, p. 220:
    bilinear operations lift to continuous multilinear
    maps by fixing the other factor. These abstract
    lifts support the induction on differentiability class. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import Hom TensorUP Bilinear RealNormUP
  ContinuousMultilinearUP NormBoundedBilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_bounded_bilinear_flip]:
    reversing the two factors of a continuous
    bilinear operation preserves its bound,
    supporting Federer 3.1.11, p. 220. *)
Lemma norm_bounded_bilinear_flip (R : realType)
    (U V W : lmodType R) (NU : U->R) (NV : V->R) (NW : W->R)
    (B : U->V->W) :
  norm_bounded_bilinear NU NV NW B ->
  norm_bounded_bilinear NV NU NW (fun v u=>B u v).
Proof.
move=> [hb [C [hC hbound]]]; split; first by split; [exact: hb.2|exact: hb.1].
exists C; split=> // v u; rewrite [NV v*NU u]mulrC; exact: hbound.
Qed.

(** Source for [continuous_multilinear_bilinear_first_lift]:
    the map (L,v) to the multilinear
    form u to B(L(u),v), supporting
    higher bilinear calculus in Federer 3.1.11,
    p. 220. The lift is itself bounded
    bilinear, with existence derived from the
    abstract representation of continuous multilinear maps. *)
Theorem continuous_multilinear_bilinear_first_lift (R : realType) k
    (X U V W P Q : lmodType R)
    (NX : X->R) (NU : U->R) (NV : V->R) (NW : W->R)
    (hNV : is_real_norm NV)
    (ep : {ffun 'I_k->X}->Hom P U) (PN : P->R)
    (eq : {ffun 'I_k->X}->Hom Q W) (QN : Q->R)
    (hP : is_continuous_multilinear_space NX NU ep PN)
    (hQ : is_continuous_multilinear_space NX NW eq QN)
    (B : U->V->W) :
  norm_bounded_bilinear NU NV NW B ->
  exists C : P->V->Q,
    norm_bounded_bilinear PN NV QN C /\
    forall p v u, eq u (C p v)=B (ep u p) v.
Proof.
move=> [hbil [b [hb hbound]]].
have hf p v : norm_bounded_multilinear NX NW (fun u=>B (ep u p) v).
  have hv := real_seminorm_nonnegative hNV.1 v.
  have hp := multilinear_operator_nonnegative (continuous_multilinear_norm_laws hP p).
  split.
  - move=> u i c x y; rewrite (continuous_multilinear_evaluation hP p).
    exact: hbil.1 v c _ _.
  - exists (b*(PN p*NV v)); split; first exact: mulr_ge0 hb (mulr_ge0 hp hv).
    move=> u; apply: le_trans (hbound _ _) _.
    have h := ler_wpM2l hb
      (ler_wpM2r hv (multilinear_operator_bound (continuous_multilinear_norm_laws hP p) u)).
    have he : b*((PN p*(\prod_(i<k) NX (u i)))*NV v)=
        (b*(PN p*NV v))*(\prod_(i<k) NX (u i)) by ring.
    by rewrite he in h.
have hex (pv : P*V) := continuous_multilinear_surjective hQ (hf pv.1 pv.2).
have [c hc] := choice hex.
pose C p v := c (p,v).
have hC p v u : eq u (C p v)=B (ep u p) v := hc (p,v) u.
exists C; split; last exact hC.
split.
- split.
  + move=> v a p q; apply: (continuous_multilinear_extensional hQ)=>u.
    by rewrite (hom_linear (eq u)) !hC (hom_linear (ep u)) (hbil.1 v).
  + move=> p a v w; apply: (continuous_multilinear_extensional hQ)=>u.
    by rewrite (hom_linear (eq u)) !hC (hbil.2 (ep u p)).
- exists b; split=> // p v.
  apply: (multilinear_operator_least (continuous_multilinear_norm_laws hQ (C p v))).
  + exact: mulr_ge0 hb (mulr_ge0
      (multilinear_operator_nonnegative (continuous_multilinear_norm_laws hP p))
      (real_seminorm_nonnegative hNV.1 v)).
  + move=> u; rewrite hC; apply: le_trans (hbound _ _) _.
    have h := ler_wpM2l hb
      (ler_wpM2r (real_seminorm_nonnegative hNV.1 v)
        (multilinear_operator_bound (continuous_multilinear_norm_laws hP p) u)).
    have he : b*((PN p*(\prod_(i<k) NX (u i)))*NV v)=
        (b*(PN p*NV v))*(\prod_(i<k) NX (u i)) by ring.
    by rewrite he in h.
Qed.

(** Source for [continuous_multilinear_bilinear_second_lift]:
    the companion map (u,L) to the
    multilinear form v to B(u,L(v)),
    supporting the two terms of the bilinear
    differential in Federer 3.1.11, p. 220. *)
Theorem continuous_multilinear_bilinear_second_lift (R : realType) k
    (X U V W P Q : lmodType R)
    (NX : X->R) (NU : U->R) (NV : V->R) (NW : W->R)
    (hNU : is_real_norm NU)
    (ep : {ffun 'I_k->X}->Hom P V) (PN : P->R)
    (eq : {ffun 'I_k->X}->Hom Q W) (QN : Q->R)
    (hP : is_continuous_multilinear_space NX NV ep PN)
    (hQ : is_continuous_multilinear_space NX NW eq QN)
    (B : U->V->W) :
  norm_bounded_bilinear NU NV NW B ->
  exists C : U->P->Q,
    norm_bounded_bilinear NU PN QN C /\
    forall u p v, eq v (C u p)=B u (ep v p).
Proof.
move=> hB.
have [C [hC hCe]] := continuous_multilinear_bilinear_first_lift
  hNU hP hQ (norm_bounded_bilinear_flip hB).
exists (fun u p=>C p u); split.
- exact: norm_bounded_bilinear_flip hC.
- move=> u p v; exact: hCe p u v.
Qed.
