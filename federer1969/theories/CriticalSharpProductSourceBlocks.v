(** Federer (1969), 3.4.4, p. 318: the
    original Cantor coordinate source agrees with each actual product step. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  RealMetricBackground EuclideanBlockCoordinates EuclideanOneCoordinate EuclideanScalarLastProduct
  CriticalSharpProductUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_sharp_source_empty_last_block]: the
    R^nu initial factor of the printed product in
    3.4.4, p. 318. No last coordinates
    impose a Cantor membership condition at this stage. *)
Lemma critical_sharp_source_empty_last_block (R:realType) nu
    (A:set (real_line_metric R)):
  @critical_sharp_product_source R nu nu A=setT.
Proof.
apply/seteqP;split=>x;first by [].
move=>_ i hi.
have hFalse:=leq_ltn_trans hi (ltn_ord i);by rewrite ltnn in hFalse.
Qed.

(** Source for [critical_sharp_source_scalar_product]: adjoining
    one original Cantor coordinate gives exactly the printed
    next source factor, 3.4.4, p. 318.
    All preceding coordinates remain unchanged and the
    appended scalar is the actual final coordinate. *)
Lemma critical_sharp_source_scalar_product (R:realType) n nu
    (A:set (real_line_metric R)):
  (nu<=n)%N ->@critical_sharp_product_source R (n+1) nu A=
    [set z | @critical_sharp_product_source R n nu A (euclidean_scalar_last_first z) /\
      A (euclidean_scalar_last_second z)].
Proof.
move=>hNu;apply/seteqP;split=>z hz.
- split.
  + move=>i hi.
    have hIndex:(nu<=lshift 1 i)%N:=hi.
    have h:=hz (lshift 1 i) hIndex.
    by rewrite /euclidean_scalar_last_first /euclidean_block_split ffunE.
  + have hIndex:(nu<=rshift n (ord0:'I_1))%N.
      by rewrite /= addn0.
    have h:=hz (rshift n ord0) hIndex.
    by rewrite /euclidean_scalar_last_second /euclidean_one_project /euclidean_block_split ffunE.
- move=>i hi;case:(split_ordP i) hi=>[j ->|j ->] hi.
  + have h:=hz.1 j hi.
    by move:h;rewrite /euclidean_scalar_last_first /euclidean_block_split ffunE.
  + rewrite (ord1 j).
    by move:hz.2;rewrite /euclidean_scalar_last_second /euclidean_one_project /euclidean_block_split ffunE.
Qed.
