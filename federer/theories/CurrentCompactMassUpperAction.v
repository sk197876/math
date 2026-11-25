(** Federer (1969), 4.1.12, pp. 367–369: a
    finite upper mass bound controls every original
    compact-index test action. Reuse the preceding exact
    supported mass-action theorem and mass supremum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothCompactSet SmoothTestSpaces
  SmoothFunctionTopology SmoothDerivativeSeminormUP SmoothDerivativeSeminormLaws CurrentMassSealed CurrentMassBasic CurrentCompactMassAction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactMassUpperAction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation nu := (smooth_function_derivative_seminorm (@current_smooth_derivative_laws R h2 n U hU m)).
Local Notation inc := (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU m)).

(** Source for [current_compact_mass_upper_action]:
    M(T)<=a gives |T(phi)|<=a nu_K^0(phi)
    when spt T is contained in K, supporting
    the flat mass and product bounds of Federer
    4.1.12, pp. 367–369. An upper bound,
    rather than equality with the mass, suffices. *)
Theorem current_compact_mass_upper_action (T:C) a:
  (@CurrentMass.value R h2 n m U hU T<=a%:E)%E->
  @current_support R h2 n U hU m T `<=` smooth_compact_carrier K->
  forall phi:DT,`|@current_value R h2 n U hU m T phi|<=a * nu K 0%N (inc phi).
Proof.
move=>hUpper hSupport phi.
have hFinite:=le_lt_trans hUpper (ltry a).
have [b [hb hMass]]:=@current_finite_mass_value R h2 n m U hU T hFinite.
have hReal:b<=a by move:hUpper;rewrite hMass lee_fin.
apply:(le_trans (@current_compact_mass_action_bound R h2 n m U hU K T b hMass hSupport phi)).
exact:(ler_wpM2r (smooth_derivative_seminorm_nonnegative
  (smooth_function_derivative_seminorm_laws (@current_smooth_derivative_laws R h2 n U hU m) K 0%N)
  (inc phi)) hReal).
Qed.
End CurrentCompactMassUpperAction.
