(** Federer (1969), 3.1.13, p. 225:
    uniform higher-derivative bounds for the normalized
    partition. The constants depend only on m
    and G_0,...,G_i, not on the open cover. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness RealNormUP ContinuousMultilinearUP ContinuousMultilinearZero
  NormHigherDifferentialUP NormHigherDifferentialUnique NormHigherDifferentialLocal
  NormClassHigherUP NormClassHigherFields NormPartitionUnityUP
  InnerSmoothUnitBump UniformFunctionNormUP FedererCoverRadius EuclideanPartitionBallCoverUP
  EuclideanPartitionBumps EuclideanPartitionFamilyUP EuclideanPartitionDenominatorBounds
  EuclideanPartitionBumpDerivativeBounds NormScalarProductSolveBound
  PartitionDerivativeBoundsUP PartitionDerivativeBoundsLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section NormalizedBounds.
Variable R : realType.
Variable m : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) R^o.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space N
  (fun t : R^o=>`|t|) (@ev i) (@ZN i).
Variable Dmu : forall i, X->Z i.
Variables G V : nat->R.
Hypothesis hDmu : forall i x, has_norm_higher_differential N ev ZN
  (fun _=>True) (inner_smooth_unit_bump (@euclidean_inner_productP R m)) i x (Dmu i x).
Hypothesis hG : forall i, is_uniform_function_norm (fun x=>@ZN i (Dmu i x)) (G i).
Hypothesis hV : is_partition_derivative_bounds ((129 : R)^+m) G V.
Variables (Phi : set (set X)) (S : set X).
Hypothesis ho : forall T, Phi T -> open T.
Hypothesis hS : is_federer_partition_ball_cover Phi S.
Variables (sigma : X->R) (v : X->X->R).
Hypothesis hfamily : is_euclidean_partition_family ev ZN Phi S sigma v.
Local Notation U := (\bigcup_(T in Phi) T).
Local Notation h := (federer_cover_radius Phi).

(** Source for [euclidean_partition_normalized_derivative_bound]:
    ||D^i v_s(x)||<=V_i h(x)^(-i),
    Federer 3.1.13, p. 225.
    The proof differentiates sigma*v_s=u_s
    and uses sigma>=1, the exact
    denominator bound, and lower-order estimates.
    All derivatives are the actual recursive ones. *)
Theorem euclidean_partition_normalized_derivative_bound s :
  S s -> forall k x (z : Z k), U x ->
    has_norm_higher_differential N ev ZN U (v s) k x z ->
    @ZN k z<=V k/(h x)^+k.
Proof.
move=>hs; elim/ltn_ind=>k ih x z hx hz.
case:k ih z hz=>[|n] ih z hz.
- have hrange := norm_partition_range (partition_family_partition hfamily) hs hx.
  rewrite hV.1 expr0 divr1
    (continuous_multilinear_zero_norm (@scalar_absolute_value_norm R) (@hZ 0%N))
    hz.2 (ger0_norm (andP hrange).1).
  exact: (andP hrange).2.
- have hsig := partition_family_denominator_smooth hfamily n.+1.
  have hvs := norm_partition_smooth (partition_family_partition hfamily) hs n.+1.
  have [Ds [hDs _]] := norm_class_higher_fields hN (@scalar_absolute_value_norm R) hZ hsig.
  have [Dv [hDv _]] := norm_class_higher_fields hN (@scalar_absolute_value_norm R) hZ hvs.
  have hubump := @euclidean_partition_bump_smooth R m Phi S Z ev ZN hZ s hs n.+1.
  have [Du [hDu _]] := norm_class_higher_fields hN (@scalar_absolute_value_norm R) hZ hubump.
  have hU y (hy : U y) := (hsig.1 y hy).1.
  have hDuU := (@norm_higher_differential_open_restriction R (R_n R m) R^o
    N (fun t : R^o=>`|t|) hN (@scalar_absolute_value_norm R) Z ev ZN hZ
    n.+1 (fun _=>True) U (euclidean_partition_bump Phi s)
    (fun _ _=>I) hU x hx (Du n.+1 x)).1 (hDu n.+1 (leqnn _) x I).
  have hsame := norm_higher_differential_unique hN (@scalar_absolute_value_norm R) hZ
    hz (hDv n.+1 (leqnn _) x hx).
  rewrite hsame.
  have hprod y (hy : U y) : sigma y*v s y=euclidean_partition_bump Phi s y.
    rewrite (partition_family_normalization hfamily hs hy) mulrC divfK //.
    exact: (lt0r_neq0 (lt_le_trans ltr01 (partition_family_denominator_lower hfamily hy))).
  have hB := @euclidean_partition_bump_derivative_bound R m Z ev ZN hZ
    Phi S n.+1 (Dmu n.+1) (G n.+1) ho hS (hDmu n.+1) (hG n.+1)
    s x (Du n.+1 x) hs hx (hDu n.+1 (leqnn _) x I).
  have hBs j (hj : (j<=n.+1)%N) :
      @ZN j (Ds j x)<=129^+m*G j/(h x)^+j.
    exact: (@euclidean_partition_denominator_derivative_bound R m Z ev ZN hZ
      Phi S ho hS sigma v hfamily j (Dmu j) (G j) (hDmu j) (hG j)
      x (Ds j x) hx (hDs j hj x hx)).
  have hBv j (hj : (j<n.+1)%N) : @ZN j (Dv j x)<=V j/(h x)^+j.
    exact: (ih j hj x (Dv j x) hx (hDv j (leqW hj) x hx)).
  have hh := @norm_scalar_product_solve_bound R (R_n R m) N hN Z ev ZN hZ
    U sigma (v s) (euclidean_partition_bump Phi s) n.+1 x
    (fun j=>Ds j x) (fun j=>Dv j x) (Du n.+1 x)
    (G n.+1/(h x)^+n.+1)
    (fun j=>129^+m*G j/(h x)^+j) (fun j=>V j/(h x)^+j)
    hx hsig hvs hprod (partition_family_denominator_lower hfamily hx)
    (fun j hj=>hDs j hj x hx) (fun j hj=>hDv j hj x hx)
    hDuU hB hBs hBv.
  by rewrite (partition_derivative_bounds_scaled_recurrence (h x) n hV) in hh.
Qed.
End NormalizedBounds.
