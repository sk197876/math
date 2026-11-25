(** Federer (1969), 4.1.7, p. 356:
    a Radon measure is the zero-current
    with the original scalar unit density.
    Its degree-zero mass is the absolute
    scalar norm already retained from 1.8.1. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP InnerNorm InnerExteriorLowDegrees ExteriorGrading ExteriorPowers
  ExteriorNorm GrassmannAbbreviations EuclideanInnerProduct CurrentCoefficientNorms CurrentDiracDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_scalar_multivector_unit_mass]:
    the original zero-vector unit has mass one,
    supporting the measure/current identification of
    Federer 4.1.7, p. 356, by 1.7.5,
    p. 32, and the absolute degree-zero convention. *)
Lemma current_scalar_multivector_unit_mass (R:realType) (h2:(1+1:R)!=0) n:
  @current_vector_mass R h2 n 0%N (@current_scalar_multivector_unit R n) = 1.
Proof.
change (@exterior_norm R h2 (R_n R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) 0%N (exterior_zeroth_inclusion (R_n R n) 1) = 1).
apply:inner_norm_value; first exact:ler01.
by rewrite (@exterior_inner_zeroth R h2 (R_n R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) 1 1) mulr1 expr1n.
Qed.
