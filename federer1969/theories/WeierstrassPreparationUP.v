(** Federer (1969), 3.4.6(2), p. 322: original
    analytic preparation and its monic transverse polynomial,
    specified before proving their existence or uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP NormAnalyticUP AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_weierstrass_polynomial_germ]: the
    original monic degree-k expression in xi with transverse
    analytic coefficients zero at the origin, 3.4.6(2),
    p. 322. Its representatives and actual neighbourhood
    equation are required without choosing an implementation. *)
Definition is_weierstrass_polynomial_germ (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (xi:Hom X R^o) (projection:Hom X K) k
    (W:@analytic_germ_ring R X NX hNX 0)
    (Wi:'I_k->@analytic_germ_ring R K NK hNK 0):Prop:=
  exists w:analytic_representative_type hNX (0:X),analytic_germ w=W /\
  exists coefficients:'I_k->analytic_representative_type hNK (0:K),
    (forall i,analytic_germ (coefficients i)=Wi i) /\
    (forall i,analytic_representative_value (coefficients i) 0=0) /\
    exists U:set X,U 0 /\
      @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
        U (analytic_representative_value w) /\
      forall x,U x ->analytic_representative_value w x=(xi x)^+k+
        \sum_(i<k) (xi x)^+i*analytic_representative_value (coefficients i) (projection x).

(** Source for [is_weierstrass_preparation]: the original
    equation Q phi=W, nonzero Q(0), and monic transverse
    expression with Wi(0)=0, 3.4.6(2), p. 322.
    Existence and uniqueness are separate proof obligations. *)
Record is_weierstrass_preparation (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (xi:Hom X R^o) (projection:Hom X K) k
    (Phi Q W:@analytic_germ_ring R X NX hNX 0)
    (Wi:'I_k->@analytic_germ_ring R K NK hNK 0):Prop:={
  (** Source for [weierstrass_preparation_identity]: the
      original germ equation, 3.4.6(2), p. 322. *)
  weierstrass_preparation_identity:Q*Phi=W;
  (** Source for [weierstrass_preparation_unit_value]: the
      original multiplier is nonzero at the origin,
      3.4.6(2), p. 322. *)
  weierstrass_preparation_unit_value:exists q:analytic_representative_type hNX (0:X),
    analytic_germ q=Q /\analytic_representative_value q 0<>0;
  (** Source for [weierstrass_preparation_polynomial]: the
      original monic transverse polynomial and vanishing
      coefficients, 3.4.6(2), p. 322. *)
  weierstrass_preparation_polynomial:
    @is_weierstrass_polynomial_germ R X K NX NK hNX hNK xi projection k W Wi
}.
