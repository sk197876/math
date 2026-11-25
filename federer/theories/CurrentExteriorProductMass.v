(** Federer (1969), 4.1.8, p. 361: the original
    product mass upper bound uses 1.8.1, p. 39.
    Retain both scalar endpoints with their actual
    absolute-scalar norms rather than applying a
    positive-degree statement in degree zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates
  ExteriorGrading ExteriorPowers ExteriorHomogeneousProducts CurrentCoefficientNorms
  CurrentPositiveCoefficientNorms CurrentZeroDegreeExteriorLaws MassWedgeBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentExteriorProductMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation V := (R_n R n).
Local Notation N := (fun d=>@current_vector_mass R h2 n d).
Local Notation hN := (fun d=>@current_vector_mass_real_norm R h2 n d).

(** Source for [current_exterior_product_mass_zero_left]:
    the original mass product is exact for a scalar
    first factor, supporting Federer 4.1.8, p. 361. *)
Theorem current_exterior_product_mass_zero_left d
    (x:exterior_power V 0) (y:exterior_power V d):
  N d (exterior_product x y)=N 0 x*N d y.
Proof.
rewrite -{1}(exterior_zeroth_inverseK x) exterior_product_zeroth_scalar_left.
rewrite (real_seminorm_scale (hN d).1) current_vector_mass_zeroth_value.
by [].
Qed.

(** Source for [current_exterior_product_mass_zero_right]:
    the original mass product is exact for a scalar
    second factor, supporting Federer 4.1.8, p. 361. *)
Theorem current_exterior_product_mass_zero_right d
    (x:exterior_power V d) (y:exterior_power V 0):
  N (d+0) (exterior_product x y)=N d x*N 0 y.
Proof.
have hScalar:=@exterior_product_zeroth_scalar_right R V d (exterior_zeroth_inverse V y) x.
rewrite (exterior_zeroth_inverseK y) in hScalar.
have hMass:=congr1 (N d) hScalar.
rewrite current_vector_mass_reindex (real_seminorm_scale (hN d).1) in hMass.
by rewrite hMass current_vector_mass_zeroth_value mulrC.
Qed.

(** Source for [current_exterior_product_mass_bound]:
    mass(xi wedge eta) is at most mass(xi)mass(eta)
    in every degree, supporting Federer 4.1.8, p. 361,
    by the original 1.8.1 estimate and scalar endpoints. *)
Theorem current_exterior_product_mass_bound i j
    (x:exterior_power V i) (y:exterior_power V j):
  N (i+j) (exterior_product x y)<=N i x*N j y.
Proof.
case:i x=>[|p] x;first by rewrite current_exterior_product_mass_zero_left.
case:j y=>[|q] y;first by rewrite current_exterior_product_mass_zero_right.
have hSum:(0<p.+1+q.+1)%N:=leq_trans (ltn0Sn p) (leq_addr q.+1 p.+1).
exact:(@mass_wedge_bound R h2 V (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
  n (@coordinate_basis R n) (@coordinate_basisP R n) p.+1 q.+1 (ltn0Sn p) (ltn0Sn q)
  (@current_form_comass R h2 n p.+1) (@current_form_comass R h2 n q.+1)
  (@current_form_comass R h2 n (p.+1+q.+1))
  (@current_positive_comass_laws R h2 n p.+1 (ltn0Sn p))
  (@current_positive_comass_laws R h2 n q.+1 (ltn0Sn q))
  (@current_positive_comass_laws R h2 n (p.+1+q.+1) hSum)
  x y (N p.+1 x) (N q.+1 y) (N (p.+1+q.+1) (exterior_product x y))
  (@current_positive_mass_laws R h2 n p.+1 (ltn0Sn p) x)
  (@current_positive_mass_laws R h2 n q.+1 (ltn0Sn q) y)
  (@current_positive_mass_laws R h2 n (p.+1+q.+1) hSum (exterior_product x y))).
Qed.
End CurrentExteriorProductMass.
