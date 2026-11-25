(** Federer (1969), 4.1.24, p. 380: the original
    rectifiable approximation property implies finite mass,
    support in the exact K, and membership in the
    original compact flat class. Reuse normality and support
    of the actual image approximants and the preceding
    supported normal mass-closure theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP LipschitzBasic SmoothCompactSet CurrentSpaces CurrentSupportGeometry
  CurrentMassSealed CurrentMassFiniteAlgebra CompactRepresentedCurrentMass
  NormalCurrentsUP CurrentNormalMassClosure FlatCurrentsUP
  CurrentFlatLipschitzPushforwardBasic PolyhedralNormal PolyhedralCurrentFlat
  RectifiableCurrentApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RectifiableCurrentBasic.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation M:=(@CurrentMass.value R h2 n m U hU).
Local Notation Rect:=(@is_rectifiable_current_supported_in R h2 n m U hU K).
Local Notation Approx:=(@is_rectifiable_image_approximant R h2 n m U hU K).

(** Source for [rectifiable_image_approximant_normal_supported]:
    each original image approximant is normal and supported
    in K, in the first assertion after the definition
    of 4.1.24, p. 380. This uses the preceding
    actual Lipschitz image laws and proved polyhedral normality. *)
Theorem rectifiable_image_approximant_normal_supported (Q:C):
  Approx Q->@normal_currents_supported_in R h2 n U hU m K Q.
Proof.
move=>[d [Z [hZ [A [f [hImage [hLip [P [hP [hAK <-]]]]]]]]]].
pose hLocal:=metric_lipschitz_is_local hLip.
pose hFlat:@is_flat_current R h2 d m Z hZ P:=ex_intro _ A
  (@integral_polyhedral_current_flat_supported R h2 d m Z hZ A P hP).
have hPNormal:=@integral_polyhedral_current_normal_support R h2 d m Z hZ A P hP.
split.
- exact:(@current_flat_lipschitz_pushforward_normal R h2 d n m Z U hZ hU
    f hImage hLocal P hFlat hPNormal.1).
- move=>x hx.
  have[y hy <-]:=@current_flat_lipschitz_pushforward_support R h2 d n m Z U hZ hU
    f hImage hLocal P hFlat x hx.
  exact:hAK y (hPNormal.2 y hy).
Qed.

(** Source for [rectifiable_current_normal_mass_closure]: the
    defining image approximants already belong to the exact
    supported normal class, so the original rectifiable class
    lies in its mass closure, Federer 4.1.24, p. 380. *)
Theorem rectifiable_current_normal_mass_closure (T:C):
  Rect T->@is_normal_current_mass_closure R h2 n m U hU K T.
Proof.
move=>hT epsilon hEpsilon.
have[Q [hQ hError]]:=hT epsilon hEpsilon.
exists Q;split;last exact:hError.
exact:rectifiable_image_approximant_normal_supported hQ.
Qed.

(** Source for [rectifiable_current_support]: the support
    of the original mass limit lies in exactly K,
    part of the asserted inclusion in 4.1.24, p. 380.
    No support premise was added to its definition. *)
Theorem rectifiable_current_support (T:C):
  Rect T->@current_support R h2 n U hU m T `<=` smooth_compact_carrier K.
Proof.
move=>hT;apply:normal_current_mass_closure_support.
exact:rectifiable_current_normal_mass_closure hT.
Qed.

(** Source for [rectifiable_current_flat_supported]: R_(m,K)
    lies in the original F_(m,K), with the same K,
    Federer 4.1.24, p. 380. Apply the existing
    mass-closure inclusion; no enlargement is used. *)
Theorem rectifiable_current_flat_supported (T:C):
  Rect T->@is_flat_current_supported_in R h2 n m U hU K T.
Proof.
move=>hT;apply:normal_current_mass_closure_is_flat.
exact:rectifiable_current_normal_mass_closure hT.
Qed.

(** Source for [rectifiable_current_finite_mass]: the original
    approximation property implies finite M(T), as used in
    the diagram and the metrics of 4.1.24, pp. 381–382.
    One normal approximant with mass error below one
    suffices; finite mass is not an extra hypothesis. *)
Theorem rectifiable_current_finite_mass (T:C):Rect T->(M T< +oo)%E.
Proof.
move=>hT;have[Q [hQ hError]]:=hT 1 ltr01.
have hNormal:=rectifiable_image_approximant_normal_supported hQ.
have hQFinite:(M Q< +oo)%E.
  exact:(@compact_represented_current_finite_mass R h2 n m U hU Q
    hNormal.1.1.1 hNormal.1.2).
have hDifference:(M (T-Q)< +oo)%E:=lt_trans hError (ltry 1).
have hSum:=@current_finite_mass_linear_combination R h2 n m U hU 1
  (T-Q) Q hDifference hQFinite.
by rewrite scale1r subrK in hSum.
Qed.
End RectifiableCurrentBasic.
