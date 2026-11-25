(** Federer (1969), 4.1.16, p. 374: apply the preceding
    exact flat image estimate to a nonexpanding map. A
    valid bound one need not be the least Lipschitz constant;
    first compare the actual least constant with one. This
    retains zero constants and degree zero. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP LipschitzBasic LipschitzConstant SmoothCompactSet CurrentSpaces
  FlatCurrentsUP CurrentFlatNorm FlatCurrentSpaces LinearSubspaceRepresentationUP
  CurrentLipschitzCompactImage CurrentLipschitzFlatCoefficient
  CurrentFlatLipschitzPushforwardSealed CurrentCompactLipschitzPushforwardFlatBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_nonexpanding_flat_coefficient_bound]:
    the flat coefficient max{L^m,L^(m+1)} is at most one
    when 0<=L<= 1, by 4.1.14, p. 371, used in
    4.1.16, p. 374. No division by L occurs. *)
Lemma current_nonexpanding_flat_coefficient_bound (R : realType) m (L : R) :
  0<=L -> L<= 1 -> current_lipschitz_flat_coefficient m L<= 1.
Proof.
move=> hL hLone; rewrite /current_lipschitz_flat_coefficient ge_max.
apply/andP; split; exact: exprn_ile1 _ hL hLone.
Qed.

Section FlatCurrentNonexpandingPushforward.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n nu m : nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U : set X) (V : set Y).
Hypothesis hU : forall x,U x->norm_domain_interior NX U x.
Hypothesis hV : forall y,V y->norm_domain_interior NY V y.
Variable f : X -> Y.
Hypothesis hImage : forall x,U x->V (f x).
Hypothesis hLocal : @is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Variable K : smooth_compact_set hNX U.
Hypothesis hBound : @is_metric_lipschitz_bound R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY)
  (smooth_compact_carrier K) f 1.
Local Notation fK := (@current_lipschitz_compact_image R n nu U V
  hU f hImage hLocal K).

(** Source for [current_flat_nonexpanding_pushforward_bound]:
    F_(fK)(f#T)<=F_K(T) for the nonexpanding retraction
    in Federer 4.1.16, p. 374. This is a consequence
    of the exact 4.1.14 bound on the actual opaque image,
    with arbitrary flat T and no finite-mass or normality
    premise. K may be empty and the degree may be zero. *)
Theorem current_flat_nonexpanding_pushforward_bound
    (T : @current_space R h2 n U hU m)
    (hGlobal : @is_flat_current R h2 n m U hU T)
    (hT : @is_flat_current_supported_in R h2 n m U hU K T) :
  (@current_flat_norm R h2 nu m V hV fK
    (@CurrentFlatLipschitzPushforward.value R h2 n nu m
      U V hU hV f hImage hLocal T hGlobal)<=
    @current_flat_norm R h2 n m U hU K T)%E.
Proof.
pose hLipschitz := metric_lipschitz_of_bound hBound.
pose L := metric_lipschitz_constant hLipschitz.
have hLeast := metric_lipschitz_constant_specification hLipschitz.
have hL : 0<=L := metric_lipschitz_constant_nonnegative hLipschitz.
have hLone : L<= 1 := metric_lipschitz_constant_minimal hLipschitz hBound.
have hCap := current_nonexpanding_flat_coefficient_bound m hL hLone.
have hOriginal := @current_flat_lipschitz_pushforward_flat_bound R h2 n nu m
  U V hU hV f hImage hLocal K L hLeast T hGlobal hT.
have [z hZ] := subspace_representation_full
  (@flat_current_space_laws R h2 n m U hU K) hT.
pose a := @flat_current_norm R h2 n m U hU K z.
have ha : 0<=a := real_seminorm_nonnegative
  (@flat_current_norm_is_norm R h2 n m U hU K).1 z.
have hValue : @current_flat_norm R h2 n m U hU K T=a%:E.
  rewrite -hZ; exact: (@flat_current_norm_value R h2 n m U hU K z).
apply: le_trans hOriginal _.
rewrite hValue -EFinM lee_fin.
have hScalar := ler_wpM2r ha hCap.
by rewrite mul1r in hScalar.
Qed.
End FlatCurrentNonexpandingPushforward.
