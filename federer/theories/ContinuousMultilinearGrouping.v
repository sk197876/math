(** Federer (1969), 3.1.11, p. 219:
    the isometric linear identification between
    (p+q)-linear maps and q-linear maps
    into the p-linear space. Only the abstract
    evaluation and norm specifications are used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP
  ContinuousMultilinearBlockCurrying MultilinearArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continuous_multilinear_grouping_exists]:
    grouping arguments gives an onto linear isometry,
    as used in the D^q D^p identity
    of Federer 3.1.11, p. 219.
    The evaluation identity characterizes the identification;
    no chosen implementation of any multilinear space
    is exposed or used. *)
Theorem continuous_multilinear_grouping_exists (R : realType) p q
    (X Y P T W : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX)
    (ep : {ffun 'I_p->X}->Hom P Y) (PN : P->R)
    (et : {ffun 'I_(p+q)->X}->Hom T Y) (TN : T->R)
    (ew : {ffun 'I_q->X}->Hom W P) (WN : W->R)
    (hP : is_continuous_multilinear_space NX NY ep PN)
    (hT : is_continuous_multilinear_space NX NY et TN)
    (hW : is_continuous_multilinear_space NX PN ew WN) :
  exists J : Hom T W,
    (forall z u v, ep u (ew v (J z))=et (multilinear_arguments_join u v) z) /\
    (forall z, WN (J z)=TN z) /\
    (forall w, exists z, J z=w).
Proof.
have hf z : norm_bounded_multilinear NX NY (fun u=>et u z).
  split; first exact: continuous_multilinear_evaluation hT z.
  exists (TN z); split.
  - exact: multilinear_operator_nonnegative (continuous_multilinear_norm_laws hT z).
  - exact: multilinear_operator_bound (continuous_multilinear_norm_laws hT z).
have hex z : exists w, forall u v,
    ep u (ew v w)=et (multilinear_arguments_join u v) z.
  have [g [hgb hge]] := continuous_multilinear_block_curry_exists hNX hP (hf z).
  have [w hw] := continuous_multilinear_surjective hW hgb.
  exists w=>u v; by rewrite hw hge.
have [j hj] := choice hex.
have hlin : linear j.
  move=> c z z'; apply: (continuous_multilinear_extensional hW)=>v.
  apply: (continuous_multilinear_extensional hP)=>u.
  by rewrite !linearP /= !hj linearP.
pose J := @HomMap R T W j (introT (asboolP _) hlin).
exists J; split; first exact hj.
split.
- move=> z.
  have hn := @continuous_multilinear_block_curry_norm R p q X Y P NX NY
    hNX ep PN hP (fun u=>et u z) (fun v=>ew v (J z)) (TN z)
    (continuous_multilinear_norm_laws hT z) (hj z).
  have hw := continuous_multilinear_norm_laws hW (J z).
  apply/eqP; rewrite eq_le; apply/andP; split.
  + exact (multilinear_operator_least hw
      (multilinear_operator_nonnegative hn) (multilinear_operator_bound hn)).
  + exact (multilinear_operator_least hn
      (multilinear_operator_nonnegative hw) (multilinear_operator_bound hw)).
- move=> w.
  have hgb : norm_bounded_multilinear NX PN (fun v=>ew v w).
    split; first exact: continuous_multilinear_evaluation hW w.
    exists (WN w); split.
    + exact: multilinear_operator_nonnegative (continuous_multilinear_norm_laws hW w).
    + exact: multilinear_operator_bound (continuous_multilinear_norm_laws hW w).
  have hb := continuous_multilinear_block_uncurry hNX hP hgb.
  have [z hz] := continuous_multilinear_surjective hT hb.
  exists z; apply: (continuous_multilinear_extensional hW)=>v.
  apply: (continuous_multilinear_extensional hP)=>u.
  by rewrite /J /= hj hz multilinear_arguments_left_join multilinear_arguments_right_join.
Qed.
