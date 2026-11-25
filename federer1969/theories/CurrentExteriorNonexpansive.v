(** Federer (1969), 4.1.8, p. 361: coordinate
    inclusions and projections preserve or contract the
    original mass. This supporting general contraction
    is the original exterior-map estimate of 1.8.1,
    p. 39, including the scalar degree separately. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct ExteriorGrading ExteriorMaps ExteriorPowers
  CurrentCoefficientNorms CurrentZeroDegreeExteriorLaws
  OperatorNormUP OperatorNormSealed MassComassMaps Comass Mass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentExteriorNonexpansive.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation BX := (@euclidean_inner_product R m).
Local Notation BY := (@euclidean_inner_product R n).
Local Notation hBX := (@euclidean_inner_productP R m).
Local Notation hBY := (@euclidean_inner_productP R n).
Variable f:{linear X->Y}.
Hypothesis hContract:forall x,inner_norm hBY (f x)<=inner_norm hBX x.

(** Source for [current_exterior_nonexpansive]: the original
    nonexpansive map contracts mass in every degree,
    supporting Federer 4.1.8, p. 361, by 1.8.1, p. 39.
    Zero-dimensional source and target spaces are retained. *)
Theorem current_exterior_nonexpansive q (x:exterior_power X q):
  @current_vector_mass R h2 n q (exterior_power_map f q x)<=
    @current_vector_mass R h2 m q x.
Proof.
case:q x=>[|k] x.
- rewrite -{1}(exterior_zeroth_inverseK x) exterior_power_map_zeroth_scalar
    current_vector_mass_zeroth_scalar current_vector_mass_zeroth_value.
  exact:lexx.
- pose L:=@OperatorNorm.value R X Y BX BY hBX hBY m (@coordinate_basis R m)
    (@coordinate_basisP R m) f.
  have hL:=@OperatorNorm.laws R X Y BX BY hBX hBY m (@coordinate_basis R m)
    (@coordinate_basisP R m) f.
  have hL0:0<=L:=operator_norm_nonnegative hL.
  have hL1:L<=1.
    have[z [hz hValue]]:=operator_norm_attained hL.
    have hActual:inner_norm hBY (f z)=L:=hValue.
    rewrite -hActual;exact:le_trans (hContract z) hz.
  have hPower d:L^+d<=1:=exprn_ile1 d hL0 hL1.
  have hBound:=@mass_pushforward_bound R h2 X Y BX BY hBX hBY m
    (@coordinate_basis R m) (@coordinate_basisP R m) f L hL k.+1 (ltn0Sn k)
    (@comass R h2 X BX hBX m (@coordinate_basis R m) (@coordinate_basisP R m) k.+1 (ltn0Sn k))
    (@comass R h2 Y BY hBY n (@coordinate_basis R n) (@coordinate_basisP R n) k.+1 (ltn0Sn k))
    (@comassP R h2 X BX hBX m (@coordinate_basis R m) (@coordinate_basisP R m) k.+1 (ltn0Sn k))
    (@comassP R h2 Y BY hBY n (@coordinate_basis R n) (@coordinate_basisP R n) k.+1 (ltn0Sn k))
    x (@current_vector_mass R h2 m k.+1 x)
    (@current_vector_mass R h2 n k.+1 (exterior_power_map f k.+1 x))
    (@massP R h2 X BX hBX m (@coordinate_basis R m) (@coordinate_basisP R m) k.+1 (ltn0Sn k) x)
    (@massP R h2 Y BY hBY n (@coordinate_basis R n) (@coordinate_basisP R n) k.+1 (ltn0Sn k)
      (exterior_power_map f k.+1 x)).
  apply:le_trans hBound _.
  have h:=ler_wpM2r (real_seminorm_nonnegative (@current_vector_mass_real_norm R h2 m k.+1).1 x)
    (hPower k.+1).
  by rewrite mul1r in h.
Qed.
End CurrentExteriorNonexpansive.
