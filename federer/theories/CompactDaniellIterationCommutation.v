(** Federer (1969), 2.6.6, p. 120: consistency of finite products
    constructed by 2.6.4, p. 119, requires independence of integration
    order. This supporting lemma derives that fact from uniqueness of the
    product Daniell functional. It applies to signed functionals and uses no
    product-measure regularity. Source context: DaniellProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import TopologicalProductMaps ProperMapUP DaniellSpacePushforward
  CompactSupportFunctionUP DaniellIntegralUP DaniellProductUP DaniellProductUniqueness
  IteratedCompactDaniell IteratedCompactFunctionalAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [topological_swap_continuous]: supporting continuity
    of factor exchange for the finite products in Federer 2.6.6,
    p. 120, and the product functional of 2.6.4, p. 119. *)
Lemma topological_swap_continuous (X Y : topologicalType) :
  continuous (fun p : X*Y=>(p.2,p.1)).
Proof.
apply: topological_pair_continuous; [exact: second_projection_continuous|exact: first_projection_continuous].
Qed.

(** Source for [topological_swap_proper]: factor exchange preserves
    compact supports, supporting Federer 2.6.6, p. 120. *)
Lemma topological_swap_proper (X Y : topologicalType) :
  is_proper_map (fun p : X*Y=>(p.2,p.1)).
Proof.
move=> K hK.
have he : (fun p : X*Y=>(p.2,p.1)) @^-1` K = (fun p : Y*X=>(p.2,p.1)) @` K.
  apply/seteqP; split.
  - by move=> [x y] h; exists (y,x).
  - by move=> p [q hq <-]; case: q hq.
rewrite he; apply: continuous_compact _ hK.
exact: continuous_subspaceT (@topological_swap_continuous Y X).
Qed.

(** Source for [compact_daniell_iterations_commute]: order independence
    of the binary Daniell product of 2.6.4, p. 119, used for
    the finite-marginal consistency in Federer 2.6.6, p. 120.
    This is proved from the tensor-generator specification and uniqueness. *)
Theorem compact_daniell_iterations_commute (R : realType) (X Y : topologicalType)
    (A : (X -> R) -> R) (B : (Y -> R) -> R) :
  hausdorff_space X -> locally_compact (@setT X) ->
  hausdorff_space Y -> locally_compact (@setT Y) ->
  is_daniell_integral (@compactly_supported_continuous_functions R X) A ->
  is_daniell_integral (@compactly_supported_continuous_functions R Y) B ->
  forall h, compactly_supported_continuous_functions h ->
    B (fun y=>A (fun x=>h (x,y)))=A (fun x=>B (fun y=>h (x,y))).
Proof.
move=> hX hlX hY hlY hA hB.
pose C := fun h : X*Y -> R=> B (fun y=>A (fun x=>h (x,y))).
pose D := fun h : X*Y -> R=> A (fun x=>B (fun y=>h (x,y))).
have hC : is_daniell_product A B C.
  split; first exact: (@iterated_compact_functional_daniell R X Y A B hX hlX hY hlY hA hB).
  move=> f g hf hg; exact: iterated_compact_functional_generator hA hB hf hg.
have hD : is_daniell_product A B D.
  split.
  - exact: (@daniell_pushforward_daniell R (Y*X)%type (X*Y)%type (fun p=>(p.2,p.1))
      (@topological_swap_continuous Y X) (@topological_swap_proper Y X)
      (fun h=>A (fun x=>B (fun y=>h (y,x))))
      (@iterated_compact_functional_daniell R Y X B A hY hlY hX hlX hB hA)).
  - move=> f g hf hg.
    have he : (fun p : Y*X=>f p.2*g p.1)=(fun p : Y*X=>g p.1*f p.2).
      by apply: funext=> p; rewrite mulrC.
    have hh := @iterated_compact_functional_generator R Y X B A g f hB hA hg hf.
    have hh' := congr1 (fun h : Y*X -> R=>A (fun x=>B (fun y=>h (y,x)))) he.
    exact: eq_trans hh' (eq_trans hh (mulrC _ _)).
move=> h hh; exact: (@daniell_product_unique R X Y A B C D hX hlX hY hlY hC hD h hh).
Qed.
