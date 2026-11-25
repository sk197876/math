(** Federer (1969), 2.5.14, pp. 107–108: the Radon measure represents the
    positive variation lambda. This supporting algebra extends a
    positive-cone functional to all K(X), before applying the scalar Radon
    representation theorem. The positive and negative parts are those of
    2.5.1, p. 91. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws FunctionLatticeSeminormUP
  VectorFunctionLattice PositiveDifferenceFunctional PositiveDifferenceLinear
  CompactSupportFunctionUP CompactUniformNorm MonotoneCompactSupportFunctional
  MonotoneDaniellIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_positive_difference_daniell]: the
    positive/negative-parts extension of the variation used
    in Federer 2.5.14, p. 108, has the monotone Daniell
    laws on all K(X). The parts formula is 2.5.1,
    p. 91; this lemma exposes its laws for reuse without
    inspecting an existence witness. *)
Theorem compact_positive_difference_daniell (R : realType) (X : topologicalType)
    (B : (X -> R) -> R) :
  hausdorff_space X -> locally_compact (@setT X) ->
  (forall f g, positive_function_lattice (@compactly_supported_continuous_functions R X) f ->
    positive_function_lattice (@compactly_supported_continuous_functions R X) g ->
    B (fun x => f x+g x)=B f+B g) ->
  (forall c f, 0<=c -> positive_function_lattice (@compactly_supported_continuous_functions R X) f ->
    B (fun x => c*f x)=c*B f) ->
  (forall f, positive_function_lattice (@compactly_supported_continuous_functions R X) f -> 0<=B f) ->
  is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) (positive_difference_functional B) /\
    forall f, positive_function_lattice (@compactly_supported_continuous_functions R X) f -> positive_difference_functional B f=B f.
Proof.
move=> hh hl hadd hscale hpos.
pose L := @compactly_supported_continuous_functions R X.
have hL := @compact_support_vector_lattice R X.
pose A := positive_difference_functional B.
have hlin : is_linear_functional_on_functions L A :=
  @positive_difference_functional_linear R X L hL B hadd hscale.
have hzero : B (fun _ : X => 0)=0.
  have hz : positive_function_lattice L (fun _ => 0).
    split; first exact: hL.2.1.
    by move=> x.
  have h := hscale 0 (fun _ => 0) (lexx _) hz.
  have he : (fun _ : X => 0*0)=(fun _ => (0 : R)) by apply: funext=> x; rewrite mul0r.
  by rewrite he mul0r in h.
have hagree f : positive_function_lattice L f -> A f=B f.
  move=> hf; rewrite /A /positive_difference_functional.
  have hp : (fun x => Order.max (f x) 0)=f by apply: funext=> x; rewrite max_l //; exact: hf.2.
  have hn : (fun x => Order.max (-f x) 0)=(fun _ => 0).
    by apply: funext=> x; rewrite max_r // oppr_le0; exact: hf.2.
  by rewrite hp hn hzero subr0.
split=> //.
apply: (@monotone_compact_support_linear_daniell R X A hh hl hlin)=> f g hf hg hfg.
pose d x := g x-f x.
have hd : positive_function_lattice L d.
  split; first exact: (@function_lattice_ordered_difference R X L hL.1 f g hf hg hfg).
  by move=> x; rewrite /d subr_ge0; exact: hfg.
have he : (fun x => f x+d x)=g by apply: funext=> x; rewrite /d addrCA subrr addr0.
have h := hlin.1 f d hf hd.1.
rewrite he (hagree d hd) in h; rewrite h lerDl; exact: hpos.
Qed.

(** Source for [compact_positive_cone_extension]: supporting
    extension of lambda from K(X)+ to K(X) for the vector
    paragraph of Federer 2.5.14, p. 108. Only the agreement
    and Daniell laws of the resulting extension are exposed. *)
Theorem compact_positive_cone_extension (R : realType) (X : topologicalType)
    (B : (X -> R) -> R) :
  hausdorff_space X -> locally_compact (@setT X) ->
  (forall f g, positive_function_lattice (@compactly_supported_continuous_functions R X) f ->
    positive_function_lattice (@compactly_supported_continuous_functions R X) g ->
    B (fun x => f x+g x)=B f+B g) ->
  (forall c f, 0<=c -> positive_function_lattice (@compactly_supported_continuous_functions R X) f ->
    B (fun x => c*f x)=c*B f) ->
  (forall f, positive_function_lattice (@compactly_supported_continuous_functions R X) f -> 0<=B f) ->
  exists A, is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) A /\
    forall f, positive_function_lattice (@compactly_supported_continuous_functions R X) f -> A f=B f.
Proof.
move=> hh hl hadd hscale hpos; exists (positive_difference_functional B).
exact: compact_positive_difference_daniell hh hl hadd hscale hpos.
Qed.
