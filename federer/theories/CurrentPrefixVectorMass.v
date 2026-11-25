(** Federer (1969), 4.1.23, p. 379:
    the chosen coordinate m-vector is simple
    and has exactly unit mass. Reuse the
    original orthonormal-product norm and simple-mass
    equality, with the separate scalar unit in degree zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom GradedComponents InnerProductUP InnerNorm
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates
  ExteriorAlgebra ExteriorGrading ExteriorPowers FiniteExteriorPowers
  ExteriorNorm ExteriorFrameUnitNorm AssociatedSubspace SimpleElementary
  SimpleZeroDegree OrthonormalFamilies Comass Mass MassEquality
  CurrentCoefficientNorms CurrentScalarUnitNorm CurrentDiracDensity.
From Federer Require Import EuclideanStiefelInnerSplitting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_empty_frame_scalar_unit]:
    the empty coordinate product is
    the original scalar unit in
    every ambient space, supporting the
    m=0 endpoint of Federer
    4.1.23, pp. 379–380. *)
Lemma current_empty_frame_scalar_unit (R : realType) n
    (e : 'I_0 -> R_n R n) :
  e_lambda e (ord_tuple 0)=@current_scalar_multivector_unit R n.
Proof.
apply: val_inj.
change (component_val (e_lambda e (ord_tuple 0))=
  component_val (@current_scalar_multivector_unit R n)).
by rewrite (tuple0 (ord_tuple 0)) e_lambdaE /current_scalar_multivector_unit
  zeroth_inclusion_val /exterior_scalar scale1r /= ?exterior_word_nil.
Qed.

(** Source for [current_orthonormal_product_mass_one]:
    an original orthonormal m-frame
    has exterior product of mass
    one, supporting the simple-unit
    reduction of Federer 4.1.23,
    p. 379. The positive-degree
    theorem of 1.8.1 is used
    only in its original degree range. *)
Lemma current_orthonormal_product_mass_one (R : realType)
    (h2 : (1+1:R)!=0) n m (e : 'I_m -> R_n R n) :
  orthonormal_family (@euclidean_inner_product R n) e ->
  @current_vector_mass R h2 n m (e_lambda e (ord_tuple m))= 1.
Proof.
case: m e=> [|m] e hFrame.
- rewrite current_empty_frame_scalar_unit; exact: current_scalar_multivector_unit_mass.
- pose X := R_n R n.
  pose B := @euclidean_inner_product R n.
  pose hB := @euclidean_inner_productP R n.
  pose b := @coordinate_basis R n.
  pose hb := @coordinate_basisP R n.
  pose hm := ltn0Sn m.
  pose kappa := @comass R h2 X B hB n b hb m.+1 hm.
  pose hk := @comassP R h2 X B hB n b hb m.+1 hm.
  have h := @simple_mass_euclidean R h2 X B hB n b hb m.+1 hm kappa hk
    (e_lambda e (ord_tuple m.+1))
    (@current_vector_mass R h2 n m.+1 (e_lambda e (ord_tuple m.+1)))
    (@product_simple R X m.+1 e) (@massP R h2 X B hB n b hb m.+1 hm _).
  rewrite (@orthonormal_product_unit_norm R h2 X B hB m.+1 e hFrame) in h.
  exact: h.
Qed.

(** Source for [current_prefix_vector_mass_one]:
    mass(e_1 wedge ... wedge e_m) = 1
    for the exact prefix frame
    used in Federer 4.1.23,
    pp. 379–380, including the
    empty product and R^0. *)
Lemma current_prefix_vector_mass_one (R : realType)
    (h2 : (1+1:R)!=0) n m (hMN : (m<=n)%N) :
  @current_vector_mass R h2 n m
    (e_lambda (fun i : 'I_m => @coordinate_basis R n (widen_ord hMN i))
      (ord_tuple m))= 1.
Proof.
have hInjective : injective (@widen_ord m n hMN).
  move=> i j hEqual; apply: val_inj.
  exact: (congr1 (fun k : 'I_n => val k) hEqual).
apply: current_orthonormal_product_mass_one=> i j.
rewrite (@euclidean_coordinate_orthonormal_family R n).
by rewrite (inj_eq hInjective).
Qed.
