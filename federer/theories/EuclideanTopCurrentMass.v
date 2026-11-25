(** Federer (1969), 4.1.7, p. 358:
    the original coordinate top vector has mass
    one, supporting the variation and orientation
    formulas for E^n. The positive-degree proof
    reuses 1.8.1; degree zero retains the
    established absolute scalar norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GradedComponents SimpleZeroDegree InnerProductUP InnerNorm GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates
  ExteriorAlgebra ExteriorGrading ExteriorPowers FiniteExteriorPowers ExteriorNorm ExteriorFrameUnitNorm
  SimpleElementary Comass Mass MassEquality CurrentCoefficientNorms CurrentScalarUnitNorm CurrentDiracDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_top_current_vector_mass_one]:
    the mass of e_1 wedge ... wedge e_n
    is one, supporting Federer 4.1.7, p. 358,
    by the simple-vector equality of 1.8.1,
    p. 38, and the orthonormal top-product norm
    of 1.7.7, p. 34. The n=0 endpoint
    uses the original exterior scalar unit. *)
Theorem euclidean_top_current_vector_mass_one (R:realType) (h2:(1+1:R)!=0) n:
  @current_vector_mass R h2 n n (e_lambda (@coordinate_basis R n) (ord_tuple n)) = 1.
Proof.
case:n=>[|n].
- have hUnit:e_lambda (@coordinate_basis R 0) (ord_tuple 0)=@current_scalar_multivector_unit R 0.
    apply:val_inj.
    change (component_val (e_lambda (@coordinate_basis R 0) (ord_tuple 0))=
      component_val (@current_scalar_multivector_unit R 0)).
    by rewrite (tuple0 (ord_tuple 0)) e_lambdaE /current_scalar_multivector_unit
      zeroth_inclusion_val /exterior_scalar scale1r /= ?exterior_word_nil.
  rewrite hUnit; exact:current_scalar_multivector_unit_mass.
- pose V:=R_n R n.+1.
  pose B:=@euclidean_inner_product R n.+1.
  pose hB:=@euclidean_inner_productP R n.+1.
  pose e:=@coordinate_basis R n.+1.
  pose he:=@coordinate_basisP R n.+1.
  pose hm:=ltn0Sn n.
  pose kappa:=@comass R h2 V B hB n.+1 e he n.+1 hm.
  pose hk:=@comassP R h2 V B hB n.+1 e he n.+1 hm.
  have h:=@simple_mass_euclidean R h2 V B hB n.+1 e he n.+1 hm kappa hk
    (e_lambda e (ord_tuple n.+1))
    (@mass R h2 V B hB n.+1 e he n.+1 hm (e_lambda e (ord_tuple n.+1)))
    (@product_simple R V n.+1 e) (@massP R h2 V B hB n.+1 e he n.+1 hm _).
  rewrite (@euclidean_top_product_unit_norm R h2 n.+1) in h; exact:h.
Qed.
