(** Federer (1969), 3.4.12, p. 339: holomorphic germ
    operations exist because functional operations preserve local agreement. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed NormMetric LocalGermUP LocalGermEquivalence LocalGermLift LocalGermSealed
  HolomorphicGermRepresentatives HolomorphicGermArithmeticRepresentatives HolomorphicGermUP HolomorphicGermOperationsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_germ_operations_exists]: addition,
    multiplication and negation induce operations on the original
    holomorphic germs of 3.4.12, p. 339. The proof
    selects representatives only within the existence argument. *)
Theorem holomorphic_germ_operations_exists (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) (a:X):
  exists (add mul:holomorphic_germ_space hNX a->holomorphic_germ_space hNX a->holomorphic_germ_space hNX a)
    (opp:holomorphic_germ_space hNX a->holomorphic_germ_space hNX a),is_holomorphic_germ_operations add mul opp.
Proof.
pose C:=ComplexScalars.C R.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose P:=@holomorphic_representative_type R X NX hNX a.
pose value:=@holomorphic_representative_value R X NX hNX a.
pose germ:=@holomorphic_germ R X NX hNX a.
have hG:=@LocalGerms.laws T C P value a.
pose add:=@holomorphic_add_representatives R X NX hNX a.
pose mul:=@holomorphic_multiply_representatives R X NX hNX a.
pose opp:=@holomorphic_negate_representative R X NX hNX a.
have hAdd (f f' g g':P):
    @locally_equal_at T C a (value f) (value f') ->@locally_equal_at T C a (value g) (value g') ->
    @locally_equal_at T C a (value (add f g)) (value (add f' g')).
  exact:(@locally_equal_binary T C C C a (fun x y=>x+y) (value f) (value f') (value g) (value g')).
have hMul (f f' g g':P):
    @locally_equal_at T C a (value f) (value f') ->@locally_equal_at T C a (value g) (value g') ->
    @locally_equal_at T C a (value (mul f g)) (value (mul f' g')).
  exact:(@locally_equal_binary T C C C a (fun x y=>x*y) (value f) (value f') (value g) (value g')).
have hOpp (f g:P):@locally_equal_at T C a (value f) (value g) ->
    @locally_equal_at T C a (value (opp f)) (value (opp g)).
  exact:(@locally_equal_unary T C C a (fun x=> -x) (value f) (value g)).
have [addG hAddG]:=@local_germ_binary_lift_exists T C P value a
  (holomorphic_germ_space hNX a) germ hG add hAdd.
have [mulG hMulG]:=@local_germ_binary_lift_exists T C P value a
  (holomorphic_germ_space hNX a) germ hG mul hMul.
have [oppG hOppG]:=@local_germ_unary_lift_exists T C P value a
  (holomorphic_germ_space hNX a) germ hG opp hOpp.
exists addG,mulG,oppG;by constructor.
Qed.
