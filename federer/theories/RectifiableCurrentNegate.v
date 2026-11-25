(** Federer (1969), 4.1.24, p. 380: the
    original rectifiable class is closed under additive
    inversion. Negate the actual integral polyhedral input
    of each image witness and use the preceding actual
    pushforward linearity and finite mass estimate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP LipschitzBasic SmoothCompactSet CurrentSpaces CurrentMassSealed
  CurrentMassBasic CurrentFiniteMassLinearBound CurrentMassFiniteAlgebra
  FlatCurrentsUP FlatCurrentUnion CurrentFlatLipschitzPushforwardSealed
  CurrentFlatLipschitzPushforwardBasic CurrentFlatPushforwardZero
  PolyhedralCurrentAlgebra PolyhedralCurrentFlat RectifiableCurrentApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [polyhedral_lipschitz_image_negate]: the original
    image witnesses respect inversion, in the subgroup assertion
    of 4.1.24, p. 380. All evidence of the
    negated polyhedral membership gives the same actual image. *)
Lemma polyhedral_lipschitz_image_negate (R:realType) (h2:(1+1:R)!=0)
    d n m (Z:set (R_n R d)) (U:set (R_n R n))
    (hZ:forall x,Z x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R d)) Z x)
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (A:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R d)) Z)
    (f:R_n R d->R_n R n) (hImage:forall x,Z x->U (f x))
    (hLip:@is_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) Z f)
    (P:@current_space R h2 d Z hZ m)
    (hP:@integral_polyhedral_current_class R h2 d m Z hZ A P)
    (hNeg:@integral_polyhedral_current_class R h2 d m Z hZ A (-P)):
  @polyhedral_lipschitz_image R h2 d n m Z U hZ hU A f hImage hLip (-P) hNeg=
    -(@polyhedral_lipschitz_image R h2 d n m Z U hZ hU A f hImage hLip P hP).
Proof.
pose hLocal:=metric_lipschitz_is_local hLip.
pose hFlat:@is_flat_current R h2 d m Z hZ P:=ex_intro _ A
  (@integral_polyhedral_current_flat_supported R h2 d m Z hZ A P hP).
pose hNegative:@is_flat_current R h2 d m Z hZ (-P):=ex_intro _ A
  (@integral_polyhedral_current_flat_supported R h2 d m Z hZ A (-P) hNeg).
pose hZero:@is_flat_current R h2 d m Z hZ 0:=ex_intro _ A
  (@integral_polyhedral_current_flat_supported R h2 d m Z hZ A 0
    (@integral_polyhedral_current_zero R h2 d m Z hZ A)).
pose hCombination:=@flat_current_linear_combination R h2 d m Z hZ (-1) P 0 hFlat hZero.
have hInput:(-1:R)*:P+0= -P by rewrite scaleN1r addr0.
have hCongruence:=@current_flat_lipschitz_pushforward_congruence
  R h2 d n m Z U hZ hU f hImage hLocal
  ((-1:R)*:P+0) (-P) hCombination hNegative hInput.
have hLinear:=@current_flat_lipschitz_pushforward_linear
  R h2 d n m Z U hZ hU f hImage hLocal (-1) P 0 hFlat hZero.
unfold polyhedral_lipschitz_image.
apply:(eq_trans (esym hCongruence));apply:(eq_trans hLinear).
by rewrite (@current_flat_lipschitz_pushforward_zero R h2 d n m Z U hZ hU
  f hImage hLocal hZero) scaleN1r addr0.
Qed.

Section RectifiableCurrentNegate.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation M:=(@CurrentMass.value R h2 n m U hU).
Local Notation Rect:=(@is_rectifiable_current_supported_in R h2 n m U hU K).
Local Notation Approx:=(@is_rectifiable_image_approximant R h2 n m U hU K).

(** Source for [rectifiable_image_approximant_negate]: an original
    image witness is negated without changing its source,
    map or compact index, Federer 4.1.24, p. 380. *)
Theorem rectifiable_image_approximant_negate (Q:C):Approx Q->Approx (-Q).
Proof.
move=>[d [Z [hZ [A [f [hImage [hLip [P [hP [hAK hValue]]]]]]]]]].
pose hNeg:=@integral_polyhedral_current_negate R h2 d m Z hZ A P hP.
exists d,Z,hZ,A,f,hImage,hLip,(-P),hNeg;split;first exact:hAK.
by rewrite (@polyhedral_lipschitz_image_negate R h2 d n m Z U hZ hU
  A f hImage hLip P hP hNeg) hValue.
Qed.

(** Source for [rectifiable_current_negate]: inversion preserves
    the original approximation definition, part of the
    additive subgroup assertion in 4.1.24, p. 380.
    The required finite mass of each approximation error
    is derived from its original strict tolerance bound. *)
Theorem rectifiable_current_negate (T:C):Rect T->Rect (-T).
Proof.
move=>hT epsilon hEpsilon.
have[Q [hQ hError]]:=hT epsilon hEpsilon.
exists (-Q);split;first exact:rectifiable_image_approximant_negate hQ.
have hFinite:(M (T-Q)< +oo)%E:=lt_trans hError (ltry epsilon).
have[a [ha hA]]:=@current_finite_mass_value R h2 n m U hU (T-Q) hFinite.
have hUpper:(M (T-Q)<=a%:E)%E by rewrite hA.
have hBound:=@current_finite_mass_scale_bound R h2 n m U hU (-1) (T-Q) a hUpper.
rewrite scaleN1r normrN normr1 mul1r in hBound.
have hDifference:(-T)-(-Q)= -(T-Q) by rewrite opprB opprK addrC.
rewrite hDifference.
apply:(le_lt_trans hBound).
have h:=hError;by rewrite hA in h.
Qed.

(** Source for [rectifiable_current_negate_iff]: inversion is an
    involution on the exact original fixed-K class,
    a consequence of its subgroup law, 4.1.24, p. 380. *)
Corollary rectifiable_current_negate_iff (T:C):Rect (-T)<->Rect T.
Proof.
split;last exact:rectifiable_current_negate.
move=>hT;have h:=rectifiable_current_negate hT;by rewrite opprK in h.
Qed.
End RectifiableCurrentNegate.
