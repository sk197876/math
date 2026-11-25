(** Federer (1969), 4.1.24, p. 381: the
    zero-dimensional rectifiable and integral polyhedral
    classes agree. The literal defining images are
    integral point currents, and the earlier integer
    mass gap closes that class in the mass
    distance. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP LipschitzBasic SmoothCompactSet CurrentSpaces
  PolyhedralCurrentAlgebra PolyhedralCurrentUnion IntegralCurrentClassesUP
  RectifiableCurrentApproximationUP RectifiableCurrentWitnesses
  IntegralPolyhedralZeroMassClosed IntegralPolyhedralZeroLipschitzImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section RectifiableZeroPolyhedral.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU 0%N).
Local Notation Rect:=(@is_rectifiable_current_supported_in R h2 n 0%N U hU K).
Local Notation Poly:=(@integral_polyhedral_current_class R h2 n 0%N U hU K).

(** Source for [rectifiable_zero_image_polyhedral]: every
    original defining Lipschitz image in degree zero
    is an integral polyhedral current with index K,
    the first step of R_0=P-script_0 in
    4.1.24, p. 381. *)
Theorem rectifiable_zero_image_polyhedral (Q:C):
  @is_rectifiable_image_approximant R h2 n 0%N U hU K Q->Poly Q.
Proof.
move=>[d [Z [hZ [A [f [hImage [hLip [P [hP [hAK <-]]]]]]]]]].
unfold polyhedral_lipschitz_image.
exact:(@integral_polyhedral_zero_lipschitz_pushforward R h2 d n Z U hZ hU
  f hImage (metric_lipschitz_is_local hLip) A K hAK P hP _).
Qed.

(** Source for [rectifiable_zero_polyhedral_iff]: the
    literal equality R_(0,K)(U)=P-script_(0,K)(U),
    Federer 4.1.24, p. 381. Integer coefficients
    are retained; the right side is not the
    real linear span of point currents. Empty
    U and K require no separate hypotheses. *)
Theorem rectifiable_zero_polyhedral_iff (T:C):Rect T<->Poly T.
Proof.
split;last exact:integral_polyhedral_current_rectifiable_supported.
move=>hT;apply:integral_polyhedral_zero_mass_closed=>epsilon hEpsilon.
have[Q [hQ hError]]:=hT epsilon hEpsilon.
exists Q;split;last exact:hError.
exact:rectifiable_zero_image_polyhedral hQ.
Qed.
End RectifiableZeroPolyhedral.

(** Source for [rectifiable_zero_polyhedral_union_iff]: the
    printed full compact-union equality R_0(U)=P-script_0(U),
    Federer 4.1.24, p. 381. Both directions retain
    their original compact witness and integer coefficients. *)
Theorem rectifiable_zero_polyhedral_union_iff (R:realType)
    (h2:(1+1:R)!=0) n (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU 0%N):
  @is_rectifiable_current R h2 n U hU 0%N T<->
    @is_integral_polyhedral_current R h2 n 0%N U hU T.
Proof.
split;move=>[K hT];exists K.
- exact:(@rectifiable_zero_polyhedral_iff R h2 n U hU K T).1 hT.
- exact:(@rectifiable_zero_polyhedral_iff R h2 n U hU K T).2 hT.
Qed.
