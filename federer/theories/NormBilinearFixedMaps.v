(** Federer (1969), 3.1.11, p. 220:
    fixing one argument of a bounded bilinear
    operation gives a bounded linear map. These
    maps support the operator identifications used
    in the inverse-function regularity argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP NormBoundedBilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_bilinear_left_fixed]:
    the linear map obtained by fixing the
    left factor, supporting the continuous bilinear
    operations of Federer 3.1.11, p. 220. *)
Definition norm_bilinear_left_fixed (R : realType) (U V W : lmodType R)
    (B : U->V->W) (hB : bilinear B) (u : U) : Hom V W :=
  @HomMap R V W (fun v=>B u v) (introT (asboolP _) (hB.2 u)).

(** Source for [norm_bilinear_right_fixed]:
    fixing the right factor gives the other
    linear map, supporting Federer 3.1.11, p. 220. *)
Definition norm_bilinear_right_fixed (R : realType) (U V W : lmodType R)
    (B : U->V->W) (hB : bilinear B) (v : V) : Hom U W :=
  @HomMap R U W (fun u=>B u v) (introT (asboolP _) (hB.1 v)).

(** Source for [norm_bilinear_left_fixed_bound]:
    the product norm estimate proves continuity
    after fixing the left factor, supporting
    Federer 3.1.11, p. 220. *)
Lemma norm_bilinear_left_fixed_bound (R : realType) (U V W : lmodType R)
    (NU : U->R) (NV : V->R) (NW : W->R)
    (hNU : is_real_norm NU) (B : U->V->W) (hB : bilinear B) u :
  norm_bounded_bilinear NU NV NW B ->
  norm_bounded_linear NV NW (norm_bilinear_left_fixed hB u).
Proof.
move=> [_ [C [hC hb]]].
exists (C*NU u); split.
- exact: mulr_ge0 hC (real_seminorm_nonnegative hNU.1 u).
- move=> v; rewrite -mulrA; exact: hb.
Qed.

(** Source for [norm_bilinear_right_fixed_bound]:
    the corresponding continuity bound after
    fixing the right factor, supporting Federer
    3.1.11, p. 220. *)
Lemma norm_bilinear_right_fixed_bound (R : realType) (U V W : lmodType R)
    (NU : U->R) (NV : V->R) (NW : W->R)
    (hNV : is_real_norm NV) (B : U->V->W) (hB : bilinear B) v :
  norm_bounded_bilinear NU NV NW B ->
  norm_bounded_linear NU NW (norm_bilinear_right_fixed hB v).
Proof.
move=> [_ [C [hC hb]]].
exists (C*NV v); split.
- exact: mulr_ge0 hC (real_seminorm_nonnegative hNV.1 v).
- move=> u; have he : (C*NV v)*NU u=C*(NU u*NV v) by ring.
  rewrite he; exact: hb.
Qed.
