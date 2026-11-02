(** Federer (1969), 3.1.1, p. 209: the epsilon remainder specification
    is equivalent to the printed punctured quotient limit. The proof
    treats the zero increment separately rather than assigning a value
    to the printed quotient there. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_quotient_limit]: Federer 3.1.1,
    p. 209, first displayed limit. In words: the norm of the error,
    divided by the positive norm of the increment, tends to zero. *)
Definition norm_differential_quotient_limit (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (A : X -> Prop) (f : X -> Y) (a : X) (L : Hom X Y) :=
  forall e : R, 0 < e -> exists d : R, 0 < d /\
    forall h, A (a+h) -> 0 < NX h < d ->
      NY (f (a+h)-f a-L h) / NX h < e.

(** Source for [norm_differential_quotient_iff]: exact equivalence with
    Federer's definition in 3.1.1, p. 209. The finite-bound requirement
    is separately proved equivalent to norm-topology continuity. *)
Theorem norm_differential_quotient_iff (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : X -> Prop) (f : X -> Y) (a : X) (L : Hom X Y) :
  has_norm_differential NX NY A f a L <->
  norm_domain_interior NX A a /\ norm_bounded_linear NX NY L /\
    norm_differential_quotient_limit NX NY A f a L.
Proof.
split.
- move=> hf; split; first exact: norm_differential_interior hf.
  split; first exact: norm_differential_bounded hf.
  move=> e he; have he2 : 0 < e/2 by rewrite divr_gt0 // ltr0n.
  have [d [hd hrem]] := norm_differential_remainder hf he2.
  exists d; split=> // h ha /andP [hn hs].
  rewrite ltr_pdivrMr //.
  apply: le_lt_trans (hrem h ha hs) _.
  rewrite ltr_pM2r //; by lra.
- move=> [hA [hL hlim]]; split=> // e he.
  have [d [hd hb]] := hlim e he; exists d; split=> // h ha hs.
  have [->|hh] := eqVneq h 0.
    by rewrite addr0 subrr linear0 subrr (real_seminorm_zero hNY.1)
      (real_seminorm_zero hNX.1) mulr0.
  have hn : 0 < NX h by rewrite (real_norm_positive hNX.1 hNX.2).
  have hsmall : 0 < NX h < d by apply/andP; split.
  have hbound := hb h ha hsmall.
  apply: ltW; by move: hbound; rewrite ltr_pdivrMr.
Qed.
