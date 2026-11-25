(** Federer (1969), 4.1.19, p. 377: a
    flat cochain is real linear on the
    original F_m(U), with one finite bound
    valid for every compact index. The least
    nonnegative bound defines its norm, including
    empty domains and zero coefficient spaces. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Bilinear Hom ModuleQuotient RealNormUP
  NormDifferentialUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentSpaces SmoothCompactSet CurrentFlatNorm
  CurrentFlatDualSeminormBasic CurrentFlatFiniteArithmetic
  FlatCurrentsUP FlatCurrentFinite FlatCurrentClosure FlatCurrentUnionSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FlatCochainUP.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation hNX :=
  (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation W := (@flat_current_union_space R h2 n m U hU).
Local Notation inc := (@flat_current_union_inclusion R h2 n m U hU).
Local Notation FK := (@current_flat_norm R h2 n m U hU).
Local Notation flatK := (@is_flat_current_supported_in R h2 n m U hU).

(** Source for [is_original_flat_cochain_bound]: the
    literal one-sided inequality in the first sentence
    of Federer 4.1.19, p. 377, for
    the same real constant at every compact K.
    Each displayed flat value is finite on its
    original domain F_(m,K)(U), by 4.1.12, p. 368. *)
Definition is_original_flat_cochain_bound (alpha : Hom W R^o) (c : R) :=
  forall (K : smooth_compact_set hNX U) (T : W),
    flatK K (inc T) -> alpha T <= c*fine (FK K (inc T)).

(** Source for [is_flat_cochain_bound]: the absolute
    version of the original common bound, equivalent
    by linearity at -T, Federer 4.1.19,
    p. 377. Its nonnegative convention makes
    the least bound meaningful also on a zero space. *)
Definition is_flat_cochain_bound (alpha : Hom W R^o) (c : R) :=
  0 <= c /\ forall (K : smooth_compact_set hNX U) (T : W),
    flatK K (inc T) -> `|alpha T| <= c*fine (FK K (inc T)).

(** Source for [is_flat_cochain]: the first definition
    of Federer 4.1.19, p. 377, on
    the literal compact-index union. Linearity is in
    the functional type; one finite common bound
    is required, not a separate bound for each K. *)
Definition is_flat_cochain (alpha : Hom W R^o) : Prop :=
  exists c : R, is_flat_cochain_bound alpha c.

(** Source for [is_flat_cochain_norm]: the norm
    F(alpha) is the least nonnegative common bound
    in Federer 4.1.19, p. 377.
    This specification is independent of a supremum
    construction or of any representing differential forms. *)
Definition is_flat_cochain_norm (alpha : Hom W R^o) (a : R) :=
  is_flat_cochain_bound alpha a /\
  forall c, is_flat_cochain_bound alpha c -> a <= c.

(** Source for [flat_cochain_original_absolute_bound]:
    negating the original flat current turns the
    printed one-sided bound into the absolute bound,
    supporting Federer 4.1.19, p. 377.
    The same K and the same real c are retained. *)
Theorem flat_cochain_original_absolute_bound (alpha : Hom W R^o) (c : R) :
  is_original_flat_cochain_bound alpha c <->
    forall (K : smooth_compact_set hNX U) (T : W),
      flatK K (inc T) -> `|alpha T| <= c*fine (FK K (inc T)).
Proof.
split.
- move=> hBound K T hFlat.
  have hIncNeg : inc (-T)%R = -inc T.
    have h := linZ (hom_linear inc) (-1:R) T.
    by rewrite !scaleN1r in h.
  have hAlphaNeg : alpha (-T)%R = -alpha T.
    have h := linZ (hom_linear alpha) (-1:R) T.
    by rewrite !scaleN1r in h.
  have hNeg : flatK K (inc (-T)%R).
    rewrite hIncNeg -scaleN1r.
    exact: (@subspace_scale R _
      (@flat_current_subspace R h2 n m U hU K) (-1) (inc T) hFlat).
  have hFinite := @flat_current_supported_finite R h2 n m U hU K
    (inc T) hFlat.
  have hNegValue : FK K (inc (-T)%R) = FK K (inc T).
    rewrite hIncNeg.
    exact: (@current_flat_finite_negate R h2 n m U hU K (inc T) hFinite).
  have hPositive := hBound K T hFlat.
  have hNegative := hBound K (-T)%R hNeg.
  rewrite hAlphaNeg hNegValue in hNegative.
  rewrite ler_norml; apply/andP; split; last exact: hPositive.
  by rewrite lerNl; exact: hNegative.
- move=> hBound K T hFlat.
  exact: (le_trans (ler_norm _) (hBound K T hFlat)).
Qed.

(** Source for [flat_cochain_bound_original_iff]:
    the nonnegative absolute-bound formulation retains
    exactly the original inequality of Federer 4.1.19,
    p. 377, for every compact index. *)
Theorem flat_cochain_bound_original_iff (alpha : Hom W R^o) (c : R) :
  is_flat_cochain_bound alpha c <->
    0 <= c /\ is_original_flat_cochain_bound alpha c.
Proof.
split.
- move=> [hC hBound]; split; first exact: hC.
  exact: (flat_cochain_original_absolute_bound alpha c).2 hBound.
- move=> [hC hBound]; split; first exact: hC.
  exact: (flat_cochain_original_absolute_bound alpha c).1 hBound.
Qed.

(** Source for [flat_cochain_original_bound_member]:
    any finite printed bound gives a flat
    cochain, Federer 4.1.19, p. 377.
    Enlarging it to its absolute value handles
    zero spaces without assuming a nonzero current. *)
Theorem flat_cochain_original_bound_member (alpha : Hom W R^o) (c : R) :
  is_original_flat_cochain_bound alpha c -> is_flat_cochain alpha.
Proof.
move=> hOriginal.
have hAbsolute := (flat_cochain_original_absolute_bound alpha c).1 hOriginal.
exists `|c|; split; first exact: normr_ge0.
move=> K T hFlat.
have hNonnegative : (0 <= FK K (inc T))%E.
  exact: (@current_flat_dual_nonnegative R h2 n m U hU K
    (@current_value R h2 n U hU m (inc T))).
have hFine : 0 <= fine (FK K (inc T)) := fine_ge0 hNonnegative.
exact: (le_trans (hAbsolute K T hFlat)
  (ler_wpM2r hFine (ler_norm c))).
Qed.

(** Source for [flat_cochain_norm_unique]: the least
    common bound in Federer 4.1.19, p. 377,
    is unique independently of its construction and
    of the later measurable representation. *)
Theorem flat_cochain_norm_unique (alpha : Hom W R^o) (a b : R) :
  is_flat_cochain_norm alpha a -> is_flat_cochain_norm alpha b -> a = b.
Proof.
move=> hA hB; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (hA.2 b hB.1).
- exact: (hB.2 a hA.1).
Qed.
End FlatCochainUP.
