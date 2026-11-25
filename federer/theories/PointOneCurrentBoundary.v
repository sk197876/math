(** Federer (1969), 4.1.15, p. 373: the original
    point one-current has boundary psi'(0) of infinite
    mass. Reuse the already proved norm differential,
    mass representation and normal point-support obstruction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormDifferentialDirectional NormClassOneUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct ExteriorGrading ExteriorPowers AlternatingForms
  AlternatingZero AlternatingPairing CurrentSpaces CurrentBoundary
  CurrentTestExteriorDerivative CurrentFullScalarTestDifferential
  ExteriorFirstPairingTuple CurrentMassSealed CurrentFiniteMassRepresentation
  NormalCurrentsUP CurrentNormalPointSupportZero PointOneCurrent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PointOneCurrentBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X:=(R_n R 1%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation NS:=(fun t:R^o=>`|t|).
Local Notation hNS:=(@scalar_absolute_value_norm R).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation T:=(@point_one_current R h2).
Local Notation B:=(@current_boundary R h2 1%N 0%N Full hFull T).
Local Notation e:=(@coordinate_basis R 1%N ord0).
Local Notation DT0:=(@current_test_space R h2 1%N Full hFull 0%N).
Local Notation scalar:=(fun (psi:DT0) x=>zero_form_value
  (@current_test_value R h2 1%N Full hFull 0%N psi x)).

(** Source for [point_one_current_boundary_evaluation]: the literal
    (boundary T)(psi)=psi'(0) formula in 4.1.15, p. 373.
    D is the actual norm differential of the scalar test
    coefficient, not a caller-supplied value of its derivative. *)
Theorem point_one_current_boundary_evaluation (psi:DT0) (D:Hom X R^o):
  has_norm_differential NX NS Full (scalar psi) (0:X) D ->
  @current_value R h2 1%N Full hFull 0%N B psi=D e.
Proof.
move=>hD.
have [A [hA hPair]]:=@current_full_scalar_test_differential R h2 1%N psi.
have hEqual:D=A 0.
  exact:(norm_differential_unique hNX hNS hD
    (norm_class_one_differential hA Logic.I)).
rewrite current_boundary_evaluation point_one_current_evaluation.
have hPoint:=hPair (0:X) e.
rewrite exterior_first_pairing_tuple in hPoint.
by rewrite hEqual;exact:hPoint.
Qed.

(** Source for [point_one_current_boundary_actual_derivative]: every
    original scalar test has the derivative used by the
    boundary formula in 4.1.15, p. 373. *)
Theorem point_one_current_boundary_actual_derivative (psi:DT0):
  exists D:Hom X R^o,has_norm_differential NX NS Full (scalar psi) (0:X) D /\
    @current_value R h2 1%N Full hFull 0%N B psi=D e.
Proof.
have [A [hA _]]:=@current_full_scalar_test_differential R h2 1%N psi.
have hD:=norm_class_one_differential hA (a:=(0:X)) Logic.I.
exists (A 0);split;first exact:hD.
exact:point_one_current_boundary_evaluation hD.
Qed.

(** Source for [point_one_current_not_normal]: the point
    example of 4.1.15, p. 373, cannot be normal.
    Reuse the earlier normal one-current point-support theorem. *)
Theorem point_one_current_not_normal:
  ~@is_normal_current R h2 1%N Full hFull 1%N T.
Proof.
move=>hNormal;apply:(@point_one_current_nonzero R h2).
exact:(@current_normal_point_support_zero R h2 Full hFull T (0:X)
  hNormal (@point_one_current_support_subset R h2)).
Qed.

(** Source for [point_one_current_boundary_mass]: the literal
    M(boundary T)=infinity assertion in 4.1.15, p. 373.
    If it were finite, 4.1.7 would represent both T
    and its boundary, contradicting the preceding point-support law. *)
Theorem point_one_current_boundary_mass:
  @CurrentMass.value R h2 1%N 0%N Full hFull B=(+oo)%E.
Proof.
have hNotFinite:~(@CurrentMass.value R h2 1%N 0%N Full hFull B < +oo)%E.
  move=>hFinite;apply:point_one_current_not_normal.
  split;last exact:(@point_one_current_compact R h2).
  split;first exact:(@point_one_current_representable R h2).
  exact:(@current_finite_mass_representation R h2 1%N 0%N
    Full hFull B hFinite).
have hTop:(+oo<=@CurrentMass.value R h2 1%N 0%N Full hFull B)%E.
  rewrite leNgt;apply/negP;exact:hNotFinite.
apply/eqP;by rewrite eq_le leey hTop.
Qed.
End PointOneCurrentBoundary.
