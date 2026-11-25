(** Federer (1969), 3.4.5, p. 321: the actual
    adapted surface equation is a nonzero analytic scalar
    multiple of the homogeneous cubic after normalization. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals ring.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanCoordinateSplit
  FlatExponentialSealed FlatExponentialOrder CartanSurfaceUP CartanSurfaceSealed
  CartanAxisCoordinate CubicConePolynomialDivisibility.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Equation.
Variable R:realType.
Local Notation X:=(R_n R 3).

(** Source for [cartan_normalization_equation]: the exact
    original cubic equation, with its actual coefficient,
    agrees with minus a(z) times the normalized cone
    equation for every original point with z<1,
    supporting the local/global example in 3.4.5, p. 321. *)
Lemma cartan_normalization_equation (T:X->X):
  (forall v,(T v) ord0=v ord0) ->
  (forall v,(T v) (Ordinal (isT:(1<3)%N))=v (Ordinal (isT:(1<3)%N))) ->
  (forall v,(T v) ord_max=cartan_axis_coordinate (v ord_max)) ->
  forall v:X,v ord_max<1 ->
  v ord_max*((v ord0)^+2+(v (Ordinal (isT:(1<3)%N)))^+2)-
    (v ord0)^+3*FlatExponential.value (1-v ord_max)=
    -FlatExponential.value (1-v ord_max)*cubic_cone_polynomial_value (T v).
Proof.
move=>hX hY hZ v hv.
have hPos:0<FlatExponential.value (1-v ord_max) by rewrite flat_exponential_positive subr_gt0.
have hNonzero:FlatExponential.value (1-v ord_max)!=0 by rewrite gt_eqF.
have hLift0:lift (@ord0 2) (@ord0 1)=Ordinal (isT:(1<3)%N) by apply:val_inj.
have hLiftLast:lift (@ord0 2) (@ord_max 1)=@ord_max 2 by apply:val_inj.
rewrite /cubic_cone_polynomial_value /coordinate_head /coordinate_tail !ffunE
  hLift0 hLiftLast hX hY hZ /cartan_axis_coordinate.
by field.
Qed.

(** Source for [cartan_normalization_surfaceP]: the actual
    analytic coordinate change sends precisely the original
    surface points to actual cone points on the original
    domain z<1, supporting 3.4.5, p. 321. *)
Lemma cartan_normalization_surfaceP (T:X->X):
  (forall v,(T v) ord0=v ord0) ->
  (forall v,(T v) (Ordinal (isT:(1<3)%N))=v (Ordinal (isT:(1<3)%N))) ->
  (forall v,(T v) ord_max=cartan_axis_coordinate (v ord_max)) ->
  forall v:X,v ord_max<1 ->
  (CartanSurface.set v <->cubic_cone_polynomial_value (T v)=0).
Proof.
move=>hX hY hZ v hv.
have hE:=cartan_normalization_equation hX hY hZ hv.
have hNonzero:FlatExponential.value (1-v ord_max)!=0.
  have hPos:0<FlatExponential.value (1-v ord_max) by rewrite flat_exponential_positive subr_gt0.
  by rewrite gt_eqF.
rewrite (cartan_surface_membership (@CartanSurface.laws R) v).
split.
- move=>hSurface.
  have hZero:-FlatExponential.value (1-v ord_max)*cubic_cone_polynomial_value (T v)=0.
    by rewrite -hE hSurface subrr.
  move/eqP:hZero;rewrite mulf_eq0 oppr_eq0 (negbTE hNonzero) orFb=>/eqP;exact.
- move=>hCone.
  have hZero:=hE;rewrite hCone mulr0 in hZero.
  by move/eqP:hZero;rewrite subr_eq0=>/eqP.
Qed.
End Equation.
