(** Federer (1969), 4.1.12, p. 368: the
    original compact flat closures, their union, and
    the locally flat currents. These predicates are
    stated on actual currents before choosing any
    subspace carrier or proving completeness. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  SmoothCompactSet SmoothTestSpaces CurrentFlatNorm NormalCurrentsUP CurrentContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FlatCurrentsUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation ScalarTest := (@current_test_space R h2 n U hU 0%N).
Local Notation hScalar := (@current_smooth_space_laws R h2 n U hU 0%N).

(** Source for [is_flat_current_supported_in]: the
    F_K closure of N_(m,K)(U) in D_m(U), the
    first flat-chain definition in Federer 4.1.12,
    p. 368. Every positive tolerance admits an
    original normal current with the same compact
    support constraint and smaller flat error. *)
Definition is_flat_current_supported_in (K:smooth_compact_set hNX U) (T:C):Prop:=
  forall epsilon:R,0<epsilon->exists S:C,
    @normal_currents_supported_in R h2 n U hU m K S /\
    (@current_flat_norm R h2 n m U hU K ((T-S)%R)<epsilon%:E)%E.

(** Source for [is_flat_current]: F_m(U) is the
    union over every compact K contained in U
    of the original F_(m,K)(U), Federer 4.1.12,
    p. 368. No compact support is fixed globally. *)
Definition is_flat_current (T:C):Prop:=
  exists K:smooth_compact_set hNX U,is_flat_current_supported_in K T.

(** Source for [is_locally_flat_current]: the original
    condition that T contracted with every compact
    scalar test belongs to F_m(U), Federer 4.1.12,
    p. 368. The literal original test space and
    actual smooth contraction are retained. *)
Definition is_locally_flat_current (T:C):Prop:=
  forall gamma:ScalarTest,is_flat_current
    (@current_contraction R h2 n 0%N m U hU (smooth_test_inclusion hScalar gamma) T).

(** Source for [is_germwise_flat_current]: the original
    local agreement condition in Federer 4.1.12,
    p. 368: every x in U has a flat S with
    x outside the support of T-S. Its equivalence
    with local flatness is proved separately. *)
Definition is_germwise_flat_current (T:C):Prop:=
  forall x:X,U x->exists S:C,is_flat_current S /\
    ~@current_support R h2 n U hU m ((T-S)%R) x.
End FlatCurrentsUP.
