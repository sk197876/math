(** Federer (1969), 2.5.20, p. 114: private realization of E=K(Y) by the
    subtype of compactly supported continuous functions. This construction
    proves existence of the abstract evaluation interface; later proofs use
    its sealed laws. The functions import supplies pointwise algebra on
    ordinary maps. Source context: CompactFunctionSpaceUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
(* Only elementary continuity of real multiplication is used as
   topological background for the subtype closure proof. *)
From mathcomp.analysis.normedtype_theory Require Import normed_module.
From Federer Require Import CompactSupportFunctionUP CompactSupportFunctionLattice
  CompactFunctionSpaceUP FunctionLatticeUP RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Construction.
Variable R : realType.
Variable Y : topologicalType.
Local Notation F := (GRing.Lmodule.clone R (Y -> R^o) _).

(** Source for [compact_function_pred]: boolean subtype
    predicate for the private realization of E=K(Y) in
    Federer 2.5.20, p. 114. *)
Definition compact_function_pred (f : F) := `[< compactly_supported_continuous_functions f >].

(** Source for [CompactFunction]: actual-function realization
    proving existence of E=K(Y), Federer 2.5.20, p. 114. *)
Record CompactFunction := CompactFunctionMap {
  (** Source for [compact_function_value]: the evaluation map
      of the function space in Federer 2.5.20, p. 114. *)
  compact_function_value : Y -> R;
  (** Source for [compact_function_membership]: membership in
      K(Y) for the realization of Federer 2.5.20, p. 114. *)
  compact_function_membership : compact_function_pred compact_function_value
}.

(** Source for [compact_function_rect]: subtype eliminator
    supporting the vector-space realization of Federer 2.5.20,
    p. 114; not a separate assertion of the book. *)
Definition compact_function_rect (P : CompactFunction -> Type)
    (h : forall f hf, P (@CompactFunctionMap f hf)) (z : CompactFunction) : P z :=
  match z as z' return P z' with @CompactFunctionMap f hf => h f hf end.
HB.instance Definition _ := [isSub for compact_function_value by compact_function_rect].
HB.instance Definition _ := [Choice of CompactFunction by <:].

(** Source for [compact_function_closed]: K(Y) is a vector
    space under pointwise operations in Federer 2.5.20,
    p. 114, using the closure properties of 2.5.13, p. 106. *)
Lemma compact_function_closed : GRing.submod_closed compact_function_pred.
Proof.
split.
- apply/asboolP; exact: compactly_supported_zero_function.
- move=> c f g /asboolP hf /asboolP hg; apply/asboolP.
  change (compactly_supported_continuous_functions (fun y => c*f y+g y)).
  have hcf : compactly_supported_continuous_functions (fun y => c*f y).
    split.
    - move=> y; apply: (@continuousM R Y (fun _ => c) f y); last exact: hf.1.
      exact: cvg_cst.
    - by apply: (compact_support_unary_operation hf.2)=> y ->; rewrite mulr0.
  exact (@function_lattice_add R Y (@compactly_supported_continuous_functions R Y)
    (@compactly_supported_continuous_functions_lattice R Y) (fun y => c*f y) g hcf hg).
Qed.
HB.instance Definition _ := GRing.SubChoice_isSubLmodule.Build R F
  compact_function_pred CompactFunction compact_function_closed.

(** Source for [compact_function_space_witness]: verified
    existence of the abstract function-space laws for E=K(Y),
    Federer 2.5.20, p. 114, including the empty-space case. *)
Lemma compact_function_space_witness : is_compact_function_space compact_function_value.
Proof.
constructor.
- by move=> c f g y.
- move=> f; exact: (elimT (asboolP _) (compact_function_membership f)).
- exact: val_inj.
- move=> f hf; exists (@CompactFunctionMap f (introT (asboolP _) hf)); by [].
Qed.
End Construction.
