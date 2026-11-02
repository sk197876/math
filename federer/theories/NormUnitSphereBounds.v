(** Federer (1969), 3.1.1, p. 209: supremum and infimum of the
    differential's lengths on unit directions. These normalisation laws
    apply in arbitrary dimension and do not assume attainment. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra.
From Federer Require Import Hom RealNormUP RealNormNormalization NormOperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_unit_direction_exists]: supporting nonempty unit
    sphere condition in Federer 3.1.1, p. 209. A nonzero vector can be
    divided by its norm. The zero-dimensional exception is kept explicit. *)
Lemma norm_unit_direction_exists (R : realType) (X : lmodType R)
    (NX : X -> R) (hNX : is_real_norm NX) :
  (exists x : X, x != 0) -> exists u, NX u = 1.
Proof.
move=> [x hx]; exists (real_norm_normalize NX x).
rewrite (real_norm_normalize_value hNX.1).
by rewrite (real_norm_zero_test hNX.1 hNX.2) (negbTE hx).
Qed.

(** Source for [norm_unit_upper_bound_extend]: supporting homogeneous
    extension of a unit-sphere upper bound in Federer 3.1.1, p. 209. *)
Lemma norm_unit_upper_bound_extend (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (L : Hom X Y) (C : R) :
  (forall u, NX u = 1 -> NY (L u) <= C) ->
  forall x, NY (L x) <= C*NX x.
Proof.
move=> hb x; have [->|hx] := eqVneq x 0.
  by rewrite linear0 (real_seminorm_zero hNY.1) (real_seminorm_zero hNX.1) mulr0.
have hu : NX (real_norm_normalize NX x) = 1.
  by rewrite (real_norm_normalize_value hNX.1)
    (real_norm_zero_test hNX.1 hNX.2) (negbTE hx).
have he : L x = NX x *: L (real_norm_normalize NX x).
  by rewrite -linearZ (real_norm_normalize_reconstruct hNX.2).
rewrite he (real_seminorm_scale hNY.1)
  (ger0_norm (real_seminorm_nonnegative hNX.1 x)) mulrC.
apply: ler_wpM2r; first exact: real_seminorm_nonnegative hNX.1 x.
exact: hb _ hu.
Qed.

(** Source for [norm_unit_lower_bound_extend]: supporting homogeneous
    extension of a unit-sphere lower bound in Federer 3.1.1, p. 209. *)
Lemma norm_unit_lower_bound_extend (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (L : Hom X Y) (C : R) :
  (forall u, NX u = 1 -> C <= NY (L u)) ->
  forall x, C*NX x <= NY (L x).
Proof.
move=> hb x; have [->|hx] := eqVneq x 0.
  by rewrite linear0 (real_seminorm_zero hNY.1) (real_seminorm_zero hNX.1) mulr0.
have hu : NX (real_norm_normalize NX x) = 1.
  by rewrite (real_norm_normalize_value hNX.1)
    (real_norm_zero_test hNX.1 hNX.2) (negbTE hx).
have he : L x = NX x *: L (real_norm_normalize NX x).
  by rewrite -linearZ (real_norm_normalize_reconstruct hNX.2).
rewrite he (real_seminorm_scale hNY.1)
  (ger0_norm (real_seminorm_nonnegative hNX.1 x)) mulrC.
apply: ler_wpM2l; first exact: real_seminorm_nonnegative hNX.1 x.
exact: hb _ hu.
Qed.

(** Source for [norm_operator_unit_approximation]: the supremum over
    unit directions in Federer 3.1.1, p. 209, is approximated from below.
    No norm-maximising vector is assumed to exist. *)
Theorem norm_operator_unit_approximation (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (L : Hom X Y) n :
  (exists x : X, x != 0) -> is_norm_operator_norm NX NY L n ->
  forall e : R, 0 < e -> exists u, NX u = 1 /\ n-e < NY (L u).
Proof.
move=> hX hn e he.
have [u hu] := norm_unit_direction_exists hNX hX.
case: (pselect (exists v, NX v = 1 /\ n-e < NY (L v)))=> [h|h]; first exact h.
have hb : forall v, NX v = 1 -> NY (L v) <= n-e.
  move=> v hv; case: (leP (NY (L v)) (n-e))=> // hh.
  exfalso; apply: h; exists v; by split.
have hpos : 0 <= n-e := le_trans (real_seminorm_nonnegative hNY.1 (L u)) (hb u hu).
have hall := @norm_unit_upper_bound_extend R X Y NX NY hNX hNY L (n-e) hb.
have hle := norm_operator_least hn hpos hall.
exfalso; by lra.
Qed.
