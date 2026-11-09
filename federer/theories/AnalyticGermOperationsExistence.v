(** Federer (1969), 3.4.5, p. 319: analytic germ
    operations exist because functional operations preserve local agreement. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric LocalGermUP LocalGermEquivalence LocalGermLift LocalGermSealed
  AnalyticGermRepresentatives AnalyticGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_operations_exists]: addition,
    multiplication and negation induce operations on the original
    analytic germs of 3.4.5, p. 319. The proof
    selects representatives only within the existence argument. *)
Theorem analytic_germ_operations_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X):
  exists (add mul:analytic_germ_space hNX a->analytic_germ_space hNX a->analytic_germ_space hNX a)
    (opp:analytic_germ_space hNX a->analytic_germ_space hNX a),is_analytic_germ_operations add mul opp.
Proof.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose P:=@analytic_representative_type R X NX hNX a.
pose value:=@analytic_representative_value R X NX hNX a.
pose germ:=@analytic_germ R X NX hNX a.
have hG:=@LocalGerms.laws T R P value a.
pose add:=@analytic_add_representatives R X NX hNX a.
pose mul:=@analytic_multiply_representatives R X NX hNX a.
pose opp:=@analytic_negate_representative R X NX hNX a.
have hAdd (f f' g g':P):
    @locally_equal_at T R a (value f) (value f') ->@locally_equal_at T R a (value g) (value g') ->
    @locally_equal_at T R a (value (add f g)) (value (add f' g')).
  exact:(@locally_equal_binary T R R R a (fun x y=>x+y) (value f) (value f') (value g) (value g')).
have hMul (f f' g g':P):
    @locally_equal_at T R a (value f) (value f') ->@locally_equal_at T R a (value g) (value g') ->
    @locally_equal_at T R a (value (mul f g)) (value (mul f' g')).
  exact:(@locally_equal_binary T R R R a (fun x y=>x*y) (value f) (value f') (value g) (value g')).
have hOpp (f g:P):@locally_equal_at T R a (value f) (value g) ->
    @locally_equal_at T R a (value (opp f)) (value (opp g)).
  exact:(@locally_equal_unary T R R a (fun x=> -x) (value f) (value g)).
have [addG hAddG]:=@local_germ_binary_lift_exists T R P value a
  (analytic_germ_space hNX a) germ hG add hAdd.
have [mulG hMulG]:=@local_germ_binary_lift_exists T R P value a
  (analytic_germ_space hNX a) germ hG mul hMul.
have [oppG hOppG]:=@local_germ_unary_lift_exists T R P value a
  (analytic_germ_space hNX a) germ hG opp hOpp.
exists addG,mulG,oppG;by constructor.
Qed.
