(** Federer 1.1.4, p. 11: the exception when both spaces have infinite
    dimension. Every tensor has finite coordinate support after any linear
    readout into the countable free space. A proved countable retract in
    each original infinite space supplies an actual map outside Phi. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp finmap.
From Federer Require Import TensorUP TensorProduct TensorSpan Hom HomTensor
  FreeVector LinearBasis InfiniteSequence CountableRetraction
  FiniteSpans FiniteFamilyOrthogonalSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [tensor_coordinate_fresh_index]: Federer 1.1.4, p. 11;
    a finite set of natural coordinates omits a coordinate. Supporting
    finite-rank obstruction; no globally selected index is exported. *)
Lemma tensor_coordinate_fresh_index (S : {fset nat}) : exists j, j \notin S.
Proof.
pose M := (\max_(j <- S) j)%N.
exists M.+1; apply/negP=> hj.
have h : (M.+1 <= M)%N.
  apply: leq_bigmax_seq; first exact: hj.
  by [].
by rewrite ltnn in h.
Qed.

(** Source for [tensor_Hom_finite_coordinate_support]: Federer 1.1.4,
    p. 11, supporting finite-rank obstruction for Phi. An arbitrary linear
    readout of all values of one tensor map has common finite support in
    the countable free space; the original source and target are arbitrary. *)
Theorem tensor_Hom_finite_coordinate_support (K : fieldType)
    (V W : lmodType K)
    (q : {linear W -> free_vector K (Choice.clone nat _)})
    (t : tensor_space (Hom V K^o) W) :
  exists S : {fset nat}, forall v j, j \notin S ->
    q (@tensor_Hom K V W t v) j = 0.
Proof.
elim/tensor_induction: t=> [|t u [S hS] [T hT]|a t [S hS]|alpha w].
- exists fset0=> v j _; by rewrite linear0 hom_zeroE linear0 free_zeroE.
- exists (S `|` T)%fset=> v j; rewrite in_fsetU negb_or=> /andP [hjS hjT].
  by rewrite linearD hom_addE linearD free_addE (hS v j hjS) (hT v j hjT) addr0.
- exists S=> v j hj.
  by rewrite linearZ hom_scaleE linearZ free_scaleE (hS v j hj) mulr0.
- exists (finsupp (q w))=> v j hj.
  by rewrite tensor_HomE linearZ free_scaleE (fsfun_dflt hj) mulr0.
Qed.

(** Source for [tensor_Hom_infinite_missing_image]: Federer 1.1.4,
    p. 11, the simultaneous infinite-dimension exception. A map between
    the actual original spaces has no tensor preimage. The independent
    sequence and its linear retract are proved earlier from the explicit
    no-finite-spanning-family definition of infinite dimension. *)
Theorem tensor_Hom_infinite_missing_image (K : fieldType)
    (V W : lmodType K) (hV : infinite_dimensional V) (hW : infinite_dimensional W) :
  exists f : Hom V W, ~ exists t, @tensor_Hom K V W t = f.
Proof.
pose f := hom_of_linear (linear_comp (countable_inclusion hW) (countable_retraction hV)).
exists f; move=> [t ht].
have [S hS] := tensor_Hom_finite_coordinate_support (countable_retraction hW) t.
have [j hj] := tensor_coordinate_fresh_index S.
have h := hS (countable_inclusion hV (delta K j)) j hj.
have heq : countable_retraction hW
    (f (countable_inclusion hV (delta K j))) = delta K j.
  change (countable_retraction hW (countable_inclusion hW
    (countable_retraction hV (countable_inclusion hV (delta K j)))) = delta K j).
  by rewrite !countable_retractionK.
rewrite ht heq deltaE eqxx in h.
by move: h; apply/eqP; rewrite oner_eq0.
Qed.

(** Source for [finite_basis_or_infinite_dimension]: Federer 1.1.4,
    p. 11, supporting dimension alternative. Finite spanning gives a basis
    by the project's proved finite linear algebra, so this does not assume
    an infinite basis or a dimension dichotomy as a project axiom. *)
Lemma finite_basis_or_infinite_dimension (K : fieldType) (V : lmodType K) :
  (exists n (e : 'I_n -> V), is_basis e) \/ infinite_dimensional V.
Proof.
case: (pselect (infinite_dimensional V))=> hi; first by right.
left; move: hi; rewrite /infinite_dimensional=> /existsNP [n /existsNP [e he]].
have hs : forall v, in_finite_span e v.
  move=> v.
  have hv : ~ forall c : 'I_n -> K, v != \sum_i c i *: e i.
    by move=> hv; apply: he; exists v.
  have /existsNP [c hc] := hv.
  case hEq: (v == \sum_i c i *: e i).
  - exists c; exact: eqP hEq.
  - by exfalso; apply: hc; exact: negbT hEq.
exact: (@finite_spanning_basis_exists K V n e hs).
Qed.

From Federer Require Import HomTensorGeneral.

(** Source for [tensor_Hom_surjective_iff_finite_factor]: Federer
    1.1.4, p. 11, the complete epimorphism criterion including its
    simultaneous-infinite exception. Both original spaces remain arbitrary;
    the finite basis and infinite-rank alternatives are proved above. *)
Theorem tensor_Hom_surjective_iff_finite_factor (K : fieldType)
    (V W : lmodType K) :
  (forall f : Hom V W, exists t, @tensor_Hom K V W t = f) <->
  ((exists n (e : 'I_n -> V), is_basis e) \/
   (exists n (e : 'I_n -> W), is_basis e)).
Proof.
split; last exact: tensor_Hom_finite_factor_surjective.
move=> hsurj.
case: (finite_basis_or_infinite_dimension V)=> [hfin|hinfV]; first by left.
case: (finite_basis_or_infinite_dimension W)=> [hfin|hinfW]; first by right.
have [f hf] := @tensor_Hom_infinite_missing_image K V W hinfV hinfW.
by exfalso; apply: hf; exact: hsurj.
Qed.
