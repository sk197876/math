(** Federer (1969), 3.1.11, p. 223: multiplying a
    fixed scalar coordinate form by a vector coefficient gives
    a bounded linear map into the multilinear-map space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom TensorFamilyUP RealNormUP NormDifferentialUP ContinuousMultilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continuous_multilinear_scalar_lift_exists]: the
    coefficient maps in the expansion of D^k f in Federer
    3.1.11, p. 223, are continuous linear maps.
    Their existence follows from the abstract representation laws;
    the theorem exposes no selected implementation. *)
Theorem continuous_multilinear_scalar_lift_exists (R : realType) k
    (X Y Z : lmodType R) (NX : X->R) (NY : Y->R)
    (hNY : is_real_norm NY)
    (ev : {ffun 'I_k->X}->Hom Z Y) (ZN : Z->R)
    (hZ : is_continuous_multilinear_space NX NY ev ZN)
    (phi : {ffun 'I_k->X}->R^o) :
  @norm_bounded_multilinear R k X R^o NX (fun r=>`|r|) phi ->
  exists L : Hom Y Z,
    (forall y u, ev u (L y)=(phi u)*:y) /\
    norm_bounded_linear NY ZN L.
Proof.
move=>[hm [C [hC hb]]].
have hf y : norm_bounded_multilinear NX NY (fun u=>(phi u)*:y).
  split.
  - move=>u i c x w; rewrite hm.
    by rewrite scalerDl scalerA.
  - exists (C*NY y); split; first exact: mulr_ge0 hC (real_seminorm_nonnegative hNY.1 y).
    move=>u; rewrite (real_seminorm_scale hNY.1).
    apply: le_trans (ler_wpM2r (real_seminorm_nonnegative hNY.1 y) (hb u)) _.
    by rewrite mulrAC.
have [l hl] := choice (fun y=>continuous_multilinear_surjective hZ (hf y)).
have hlin : linear l.
  move=>c y w; apply: (continuous_multilinear_extensional hZ)=>u.
  by rewrite hl (hom_linear (ev u)) !hl scalerDr !scalerA mulrC.
pose L := @HomMap R Y Z l (introT (asboolP _) hlin).
exists L; split; first exact hl.
exists C; split=> // y.
apply: (multilinear_operator_least (continuous_multilinear_norm_laws hZ (L y))).
- exact: mulr_ge0 hC (real_seminorm_nonnegative hNY.1 y).
- move=>u; rewrite /L /= hl (real_seminorm_scale hNY.1).
  apply: le_trans (ler_wpM2r (real_seminorm_nonnegative hNY.1 y) (hb u)) _.
  by rewrite mulrAC.
Qed.
