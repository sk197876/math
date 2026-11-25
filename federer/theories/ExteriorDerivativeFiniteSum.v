(** Federer (1969), 4.1.6, pp. 353–355:
    actual exterior differentiation commutes with
    finite sums and depends only on the form on
    its original open domain. Empty sums retain
    the necessary original interior condition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLocal
  NormDifferentialFiniteCalculus GrassmannAbbreviations Alternating
  ExteriorDifferentialUP ExteriorDifferentialSealed ExteriorDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_derivative_domain_agreement]:
    forms agreeing on U have the same actual
    exterior derivative there, supporting the finite
    reconstruction in Federer 4.1.6,
    pp. 353–355. *)
Lemma exterior_derivative_domain_agreement (R:realType) (V W:lmodType R)
    (NV:V->R) (hNV:is_real_norm NV) m (P:A_m V W m->R)
    (U:V->Prop) (phi psi:V->A_m V W m) a b:
  (forall x,U x->phi x=psi x)->has_exterior_derivative NV P U phi a b->
  has_exterior_derivative NV P U psi a b.
Proof.
move=>hEqual [L [hL hB]]; exists L; split; last exact:hB.
exact:(norm_differential_domain_agreement hNV hEqual hL).
Qed.

(** Source for [exterior_derivative_finite_sum]: repeated
    application of the original addition rule,
    Federer 4.1.6, pp. 353–355. Every
    summand uses the actual derivative graph. *)
Theorem exterior_derivative_finite_sum (R:realType) (h2:(1+1:R)!=0) n (W:lmodType R)
    (NV:R_n R n->R) (hNV:is_real_norm NV) m (P:A_m (R_n R n) W m->R) (hP:is_real_norm P)
    (U:R_n R n->Prop) a (I:finType)
    (phi:I->R_n R n->A_m (R_n R n) W m) (d:I->A_m (R_n R n) W m.+1):
  norm_domain_interior NV U a->
  (forall i,has_exterior_derivative NV P U (phi i) a (d i))->
  has_exterior_derivative NV P U (\sum_i phi i) a (\sum_i d i).
Proof.
move=>hInterior hTerms.
pose L i:=sval (constructive_indefinite_description (hTerms i)).
have hL i:=svalP (constructive_indefinite_description (hTerms i)).
exists (\sum_i L i); split.
- apply:(norm_differential_finite_sum hNV hP hInterior)=>i _; exact:(hL i).1.
- have hMap:@exterior_differential_map R h2 n W m (\sum_i L i)=\sum_i d i.
    rewrite linear_sum; apply:eq_bigr=>i _.
    exact:(exterior_differential_value_unique (@ExteriorDifferential.laws R h2 n W m (L i)) (hL i).2).
  rewrite -hMap; exact:ExteriorDifferential.laws.
Qed.
