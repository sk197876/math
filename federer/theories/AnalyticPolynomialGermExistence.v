(** Supporting Federer (1969), 3.4.8(5), p. 328:
    existing finite-dimensional polynomial analyticity gives the
    actual polynomial germ map. The construction proves existence;
    only independent representative laws are used downstream. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  PolynomialFunctions FiniteInnerScalarPolynomialAnalytic NormAnalyticUP
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing AnalyticGermRingLaws AnalyticPolynomialGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [analytic_polynomial_germ_map_exists]: supporting
    original polynomial germ existence for Federer 3.4.8(5), p. 328.
    Apply proved polynomial analyticity in every finite dimension
    and at every original centre, including dimension zero. *)
Theorem analytic_polynomial_germ_map_exists (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e) a:
  exists J:PolynomialFunction X R^o->@analytic_germ_ring R X (inner_norm hB)
    (inner_norm_real_norm hB) a,is_analytic_polynomial_germ_map J.
Proof.
pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
have hEach (P:PolynomialFunction X R^o):exists p:@analytic_representative_type R X NX hNX a,
    forall x,analytic_representative_value p x = P x.
  have hA:=@finite_inner_scalar_polynomial_analytic R X B hB n e he P a Logic.I.
  have [p hP]:=@analytic_representative_from_domain R X NX hNX a setT P hA.
  exists p=>x;by rewrite hP.
have [representative hValues]:=choice hEach.
exists (fun P=>analytic_germ (representative P))=>P.
exists (representative P);split;first exact:hValues P.
reflexivity.
Qed.

(** Source for [analytic_polynomial_germ_map_unique]: supporting
    uniqueness of the exact original representative connection,
    Federer 3.4.8(5), p. 328, by the existing pointwise germ law. *)
Lemma analytic_polynomial_germ_map_unique (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a
    (J K:PolynomialFunction X R^o->@analytic_germ_ring R X NX hNX a):
  is_analytic_polynomial_germ_map J ->is_analytic_polynomial_germ_map K ->J = K.
Proof.
move=>hJ hK;apply:funext=>P.
have [p [hP ->]]:=hJ P;have [q [hQ ->]]:=hK P.
apply:analytic_germ_pointwise_equality=>x;by rewrite hP hQ.
Qed.
