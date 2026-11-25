(** Federer (1969), 3.1.1, pp. 209–210: finite bounds for the linear
    approximations and the differential of a continuous linear map.
    All assertions use the abstract norm laws, without finite dimension. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_bounded_linear_zero]: supporting zero-map case of
    the continuous linear maps in Federer 3.1.1, p. 209. *)
Lemma norm_bounded_linear_zero (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNY : is_real_norm NY) :
  norm_bounded_linear NX NY (0 : Hom X Y).
Proof.
exists 0; split; first exact: lexx.
by move=> h; rewrite hom_zeroE (real_seminorm_zero hNY.1) mul0r.
Qed.

(** Source for [norm_bounded_linear_add]: supporting closure of the
    continuous linear maps in Federer 3.1.1, pp. 209–210, under addition. *)
Lemma norm_bounded_linear_add (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNY : is_real_norm NY)
    (L M : Hom X Y) :
  norm_bounded_linear NX NY L -> norm_bounded_linear NX NY M ->
  norm_bounded_linear NX NY (L+M).
Proof.
move=> [C [hC hL]] [D [hD hM]].
exists (C+D); split; first exact: addr_ge0.
move=> h; rewrite hom_addE mulrDl.
exact: le_trans (real_seminorm_triangle hNY.1 _ _) (lerD (hL h) (hM h)).
Qed.

(** Source for [norm_bounded_linear_scale]: supporting closure under
    scalar multiplication of the linear maps in Federer 3.1.1, p. 209. *)
Lemma norm_bounded_linear_scale (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNY : is_real_norm NY)
    (L : Hom X Y) (c : R) :
  norm_bounded_linear NX NY L -> norm_bounded_linear NX NY (c *: L).
Proof.
move=> [C [hC hL]]; exists (`|c|*C); split; first by rewrite mulr_ge0.
move=> h; rewrite hom_scaleE (real_seminorm_scale hNY.1) -mulrA.
apply: ler_wpM2l; first exact: normr_ge0.
exact: hL.
Qed.

(** Source for [norm_bounded_linear_compose]: supporting boundedness
    of the composite differential in Federer 3.1.1(2), p. 210. *)
Lemma norm_bounded_linear_compose (R : realType) (X Y Z : lmodType R)
    (NX : X -> R) (NY : Y -> R) (NZ : Z -> R)
    (L : Hom X Y) (M : Hom Y Z) :
  norm_bounded_linear NX NY L -> norm_bounded_linear NY NZ M ->
  norm_bounded_linear NX NZ (hom_comp M L).
Proof.
move=> [C [hC hL]] [D [hD hM]].
exists (D*C); split; first by rewrite mulr_ge0.
move=> h; rewrite hom_compE -mulrA.
exact: le_trans (hM (L h)) (ler_wpM2l hD (hL h)).
Qed.

(** Source for [norm_differential_linear]: Federer 3.1.1(3), p. 210:
    a continuous linear map is its own differential. The restriction to
    any domain with a interior is included as a supporting generalisation. *)
Theorem norm_differential_linear (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : X -> Prop) (a : X) (L : Hom X Y) :
  norm_domain_interior NX A a -> norm_bounded_linear NX NY L ->
  has_norm_differential NX NY A L a L.
Proof.
move=> hA hL; split=> // e he.
exists 1; split; first exact: ltr01.
move=> h _ _; rewrite linearD /= addrAC addrK subrr (real_seminorm_zero hNY.1).
by rewrite mulr_ge0 //; [exact: ltW he|exact: real_seminorm_nonnegative hNX.1 h].
Qed.

(** Source for [norm_differential_constant]: supporting constant-map
    case of the differential in Federer 3.1.1, p. 209. *)
Theorem norm_differential_constant (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : X -> Prop) (a : X) (c : Y) :
  norm_domain_interior NX A a ->
  has_norm_differential NX NY A (fun _ => c) a 0.
Proof.
move=> hA; split=> //; first exact: norm_bounded_linear_zero hNY.
move=> e he; exists 1; split; first exact: ltr01.
move=> h _ _; rewrite subrr hom_zeroE subrr (real_seminorm_zero hNY.1).
by rewrite mulr_ge0 //; [exact: ltW he|exact: real_seminorm_nonnegative hNX.1 h].
Qed.
