(** Federer (1969), 3.1.18, p. 229, first display: rank at least v
    if and only if the v-th exterior power is nonzero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom LinearBasis ExteriorAlgebra ExteriorGrading ExteriorMaps
  FiniteExteriorPowers GradedComponents ExteriorMapNormContinuity
  ExteriorHadamardBound IndependentProducts SimpleElementary
  LinearRankUP LinearRankAtLeast.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_product_tuple_reindex]: supporting the tuple
    representation of the exterior-power test in 3.1.18, p. 229. *)
Lemma exterior_product_tuple_reindex (K:fieldType) (X:lmodType K)
    (I:choiceType) (e:I->X) v (t:v.-tuple I) :
  e_lambda e t=e_lambda (fun i=>e (tnth t i)) (ord_tuple v).
Proof.
apply: val_inj; change (exterior_word [seq e i|i<-t]=
  exterior_word [seq e (tnth t i)|i<-ord_tuple v]).
have h := congr1 (fun u:v.-tuple I=>[seq e i|i<-u]) (tuple_map_ord t).
apply: congr1; by move: h; rewrite /= -map_comp.
Qed.

(** Source for [linear_rank_exteriorP]: the equality between the
    rank-threshold set and the nonzero exterior-power set in Federer
    3.1.18, p. 229, for any finite-dimensional source. Degree zero is
    included: the exterior map acts identically on scalars. *)
Theorem linear_rank_exteriorP (K:fieldType) (h2:(1+1:K)!=0)
    (X Y:lmodType K) n (b:'I_n->X) (hb:is_basis b)
    (L:Hom X Y) v :
  linear_rank_at_least L v <->
  exists xi:exterior_power X v, exterior_power_map (hom_as_linear L) v xi!=0.
Proof.
split.
- move=>[e he]; exists (e_lambda e (ord_tuple v)).
  rewrite exterior_power_map_e_lambda.
  change (e_lambda (fun i=>L (e i)) (ord_tuple v)!=0).
  exact (@independent_product_nonzero K h2 Y v (fun i=>L (e i)) he).
- move=>[xi hxi]; apply: contrapT=>hno.
  have hbase t : exterior_power_map (hom_as_linear L) v
      (@finite_e_lambda K n X b v t)=0.
    apply/eqP; apply/negPn/negP=>hnz.
    apply: hno; exists (fun i=>b (tnth (val t) i)).
    apply: exterior_product_nonzero_independent.
    move: hnz; rewrite /finite_e_lambda exterior_power_map_e_lambda
      exterior_product_tuple_reindex.
    by [].
  have hall : forall z:exterior_power X v, exterior_power_map (hom_as_linear L) v z=0.
    apply: (basis_induction (@finite_e_lambda_basis K n X b hb h2 v))=>[|x y hx hy|c x hx|t].
    + exact: linear0.
    + by rewrite linearD hx hy add0r.
    + rewrite linearZ hx.
      exact (@scaler0 K (exterior_power Y v) c).
    + exact: hbase.
  by move: hxi; rewrite hall eqxx.
Qed.
