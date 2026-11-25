(** Supporting Federer (1969), 3.4.8(5), p. 328:
    the original polynomial germ map is linear over the actual
    constant germs. Its independently specified representatives
    and the public original germ arithmetic prove the connection. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  RingScalarRestriction PolynomialFunctions AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermRing AnalyticGermRingLaws AnalyticRepresentativeRingEquations AnalyticScalarsSealed
  AnalyticPolynomialGermUP AnalyticPolynomialGermSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Linearity.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Variable hNX:is_real_norm NX.
Variable a:X.
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
Local Notation scalar:=(@AnalyticScalars.map R X NX hNX a).
Local Notation V:=[the lmodType R of ring_restricted_space scalar G^o].

(** Source for [analytic_polynomial_germ_linear]: supporting original
    Taylor interpolation for Federer 3.4.8(5), p. 328. Exact original
    representatives give linearity over the original constants, without
    choosing a power-series representation of the analytic germ. *)
Theorem analytic_polynomial_germ_linear (J:PolynomialFunction X R^o->G):
  is_analytic_polynomial_germ_map J ->linear (J:PolynomialFunction X R^o->V).
Proof.
move=>hJ c P Q.
have [p [hP hJP]]:=hJ P.
have [q [hQ hJQ]]:=hJ Q.
have [r [hR hJR]]:=hJ (c*:P+Q).
pose C:=@analytic_constant_representative R X NX hNX a c.
pose u:=@analytic_multiply_representatives R X NX hNX a C p.
pose v:=@analytic_add_representatives R X NX hNX a u q.
have hEqual:analytic_germ r = analytic_germ v.
  apply:analytic_germ_pointwise_equality=>x.
  rewrite hR.
  change ((c*:P+Q) x = c*analytic_representative_value p x+analytic_representative_value q x).
  by rewrite hP hQ.
change (J (c*:P+Q) = scalar c*J P+J Q).
rewrite hJR hEqual /v analytic_representative_add_ring_equation
  /u analytic_representative_multiply_ring_equation -hJP -hJQ.
by rewrite (@AnalyticScalars.laws R X NX hNX a c).
Qed.
End Linearity.

(** Source for [analytic_polynomial_germ_hom]: hierarchy adapter for
    the proved original polynomial germ linearity, supporting Federer
    3.4.8(5), p. 328. The map's implementation remains sealed. *)
Definition analytic_polynomial_germ_hom (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e) a:
  {linear PolynomialFunction X R^o->
    [the lmodType R of ring_restricted_space
      (@AnalyticScalars.map R X (inner_norm hB) (inner_norm_real_norm hB) a)
      (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) a)^o]}:=
  HB.pack (@AnalyticPolynomialGerms.map R X B hB n e he a)
    (GRing.isLinear.Build _ _ _ _ _
      (analytic_polynomial_germ_linear (@AnalyticPolynomialGerms.laws R X B hB n e he a))).
