(** Federer (1969), 3.2.5, p. 245: replace a
    pullback weight by zero outside A and the actual
    positive-Jacobian locus. Specify the auxiliary weight
    by its laws before proving measurable existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialZeroExtension BorelAreaSelection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_area_rank_weight]: auxiliary positive-rank
    cutoff in the characteristic-approximation proof of Federer
    3.2.5, p. 245. These are laws to be proved,
    not additional project axioms. *)
Record is_area_rank_weight (R:realType) m n (f:R_n R m->R_n R n)
    (A:set (R_n R m)) (g:R_n R n->R) (u:R_n R m->extended_real_line R):Prop:={
  (** Source for [area_rank_weight_on]: retain g(f(x)) on
      A and the positive-Jacobian locus, supporting 3.2.5,
      p. 245. *)
  area_rank_weight_on:forall x,A x -> positive_euclidean_jacobian_locus f x -> u x=(g (f x))%:E;
  (** Source for [area_rank_weight_off]: use zero on the
      discarded source part in the proof of 3.2.5, p. 245. *)
  area_rank_weight_off:forall x,~(A x /\ positive_euclidean_jacobian_locus f x) -> u x=0
}.

(** Source for [area_rank_weight_graph]: graph characterization
    of the auxiliary cutoff used in Federer 3.2.5,
    p. 245. Reuse the already opaque zero-extension laws. *)
Lemma area_rank_weight_graph (R:realType) m n (f:R_n R m->R_n R n)
    (A:set (R_n R m)) (g:R_n R n->R) (u:R_n R m->extended_real_line R):
  is_area_rank_weight f A g u -> forall x z,
  partial_function_graph (partial_function_zero_extension (0:extended_real_line R) A
    (partial_function_zero_extension (0:extended_real_line R) (positive_euclidean_jacobian_locus f)
      (partial_function_total (fun x=>(g (f x))%:E:extended_real_line R)))) x z <-> u x=z.
Proof.
move=>hU x z; case:(pselect (A x))=>hA.
- rewrite (partial_function_zero_extension_on _ _ _ hA).
  case:(pselect (positive_euclidean_jacobian_locus f x))=>hP.
  + rewrite (partial_function_zero_extension_on _ _ _ hP).
    change ((g (f x))%:E=z <-> u x=z); by rewrite (area_rank_weight_on hU hA hP).
  + rewrite (partial_function_zero_extension_off _ _ _ hP)
      (area_rank_weight_off hU (fun h=>hP h.2)).
    by split=>->.
- rewrite (partial_function_zero_extension_off _ _ _ hA)
    (area_rank_weight_off hU (fun h=>hA h.1)).
  by split=>->.
Qed.

(** Source for [area_rank_weight_nonnegative]: the nonnegative
    characteristic approximation in Federer 3.2.5, p. 245.
    The cutoff introduces only zeros, retaining nonnegativity. *)
Lemma area_rank_weight_nonnegative (R:realType) m n (f:R_n R m->R_n R n)
    (A:set (R_n R m)) (g:R_n R n->R) (u:R_n R m->extended_real_line R):
  is_area_rank_weight f A g u -> (forall y,(0<=g y)%R) -> forall x,0<=u x.
Proof.
move=>hU hg x; case:(pselect (A x /\ positive_euclidean_jacobian_locus f x))=>h.
- rewrite (area_rank_weight_on hU h.1 h.2) lee_fin; exact:hg.
- by rewrite (area_rank_weight_off hU h).
Qed.
