(** Federer (1969), 3.1.1(5), p. 210: linear coordinates on a
    finite-dimensional normed space are continuous. This supporting
    general bound follows from the project's norm-equivalence theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP LinearBasis FiniteNormEquivalence NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_finite_linear_bounded]: continuity of linear
    coordinates used in Federer 3.1.1(5), p. 210. More generally, every
    linear map from a finite-dimensional normed space into any normed
    space has a finite homogeneous bound. The auxiliary sum norm is
    used only inside this proof, via norm equivalence (2.7.16, p. 134). *)
Lemma norm_finite_linear_bounded (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) n (b : 'I_n -> X) (hb : is_basis b) (L : Hom X Y) :
  norm_bounded_linear NX NY L.
Proof.
pose N := fun x => NX x+NY (L x).
have hN : is_real_norm N.
  split.
  - split.
    + move=> x; exact: addr_ge0 (real_seminorm_nonnegative hNX.1 x)
        (real_seminorm_nonnegative hNY.1 (L x)).
    + move=> c x; rewrite /N linearZ /=
        (real_seminorm_scale hNX.1) (real_seminorm_scale hNY.1) mulrDr; reflexivity.
    + move=> x y; rewrite /N linearD /=.
      have hx := real_seminorm_triangle hNX.1 x y.
      have hy := real_seminorm_triangle hNY.1 (L x) (L y); by lra.
  - move=> x hx; apply: hNX.2.
    have h1 := real_seminorm_nonnegative hNX.1 x.
    have h2 := real_seminorm_nonnegative hNY.1 (L x).
    change (NX x+NY (L x) = 0) in hx; by lra.
have [C hC hc] := @finite_norm_comparison R X NX N hNX hN n b hb.
exists C; split; first exact: ltW hC.
move=> x; have hh := hc x; have hx := real_seminorm_nonnegative hNX.1 x.
change (is_true (NX x+NY (L x) <= C*NX x)) in hh; by lra.
Qed.
