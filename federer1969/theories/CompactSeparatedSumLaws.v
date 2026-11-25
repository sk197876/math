(** Federer (1969), 2.6.4, p. 119: linear extension from separated products
    to their finite sums, supporting the final tensor diagram and
    uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportFunctionLattice CompactSeparatedProduct
  CompactProductApproximationUP FunctionLatticeUP DaniellIntegralUP DaniellFiniteSums DaniellSpaceEmbedding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_compact_separated_sum_member]: finite
    sums in the top-arrow image belong to K(X times Y),
    Federer 2.6.4, p. 119, final diagram. *)
Lemma finite_compact_separated_sum_member (R : realType) (X Y : topologicalType)
    (h : (X*Y) -> R) : is_finite_compact_separated_sum h ->
  compactly_supported_continuous_functions h.
Proof.
move=> [F [a [b [hab he]]]].
have hfun : h=(fun p => \sum_(j <- F) a j p.1*b j p.2) by apply: funext=> p; exact: he.
rewrite hfun; apply: (@function_lattice_sequence_sum R (X*Y)%type Y _
  (@compactly_supported_continuous_functions_lattice R (X*Y)%type) F _
  (@compactly_supported_zero_function R (X*Y)%type))=> j hj.
exact (@compactly_supported_separated_product R X Y (a j) (b j) (hab j hj).1 (hab j hj).2).
Qed.

(** Source for [compact_daniell_agree_finite_separated_sums]:
    supporting extension of the final diagram from generators to
    the whole algebraic tensor image, Federer 2.6.4, p. 119. *)
Lemma compact_daniell_agree_finite_separated_sums (R : realType) (X Y : topologicalType)
    (C D : ((X*Y) -> R) -> R) :
  is_daniell_integral (@compactly_supported_continuous_functions R (X*Y)%type) C ->
  is_daniell_integral (@compactly_supported_continuous_functions R (X*Y)%type) D ->
  (forall f g, compactly_supported_continuous_functions f -> compactly_supported_continuous_functions g ->
    C (fun p : X*Y => f p.1*g p.2)=D (fun p : X*Y => f p.1*g p.2)) ->
  forall h, is_finite_compact_separated_sum h -> C h=D h.
Proof.
move=> hC hD hagree h [F [a [b [hab he]]]].
have hfun : h=(fun p => \sum_(j <- F) a j p.1*b j p.2) by apply: funext=> p; exact: he.
have hmem j : j \in F -> compactly_supported_continuous_functions (fun p : X*Y => a j p.1*b j p.2).
  move=> hj; exact (@compactly_supported_separated_product R X Y (a j) (b j) (hab j hj).1 (hab j hj).2).
have hL := @compactly_supported_continuous_functions_lattice R (X*Y)%type.
have h0 := @compactly_supported_zero_function R (X*Y)%type.
rewrite hfun (@daniell_finite_sum R (X*Y)%type _ C hL hC Y F _ h0 hmem)
  (@daniell_finite_sum R (X*Y)%type _ D hL hD Y F _ h0 hmem).
rewrite !big_seq; apply: eq_bigr=> j hj; exact (@hagree (a j) (b j) (hab j hj).1 (hab j hj).2).
Qed.
