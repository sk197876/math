(** Federer (1969), 2.5.1, p. 91: the examples of all finite real-valued
    functions and of continuous real-valued functions. These are proofs that
    the examples satisfy the abstract lattice specification; the latter
    remains the interface for subsequent integration theory. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
(* Only elementary continuity of real arithmetic is imported as
   topological background; lattice closure itself is proved below. *)
From mathcomp.analysis.normedtype_theory Require Import normed_module.
From Federer Require Import RealMetricBackground FunctionLatticeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [all_functions_lattice]: first example in Federer 2.5.1, p.
    91 *)
Lemma all_functions_lattice (R : realType) (X : Type) :
  is_function_lattice (setT : set (X -> R)).
Proof. by constructor. Qed.

(** Source for [continuous_functions_lattice]: continuous-function example
    in Federer 2.5.1, p. 91 No separation, compactness or local compactness
    assumption is required of the source topology. *)
Theorem continuous_functions_lattice (R : realType) (X : topologicalType) :
  is_function_lattice [set f : X -> R | continuous (f : X -> real_line_metric R)].
Proof.
constructor.
- move=> f g hf hg x; exact: (@continuousD R R^o X f g x (hf x) (hg x)).
- move=> c f hc hf x; apply: (@continuousM R X (fun _ => c) f x); last exact: hf.
  exact: cvg_cst.
- move=> f g hf hg x; exact: (@continuous_min R X f g x (hf x) (hg x)).
- move=> c f hc hf x; apply: (@continuous_min R X f (fun _ => c) x); first exact: hf.
  exact: cvg_cst.
- move=> f g hf hg hfg x; exact: (@continuousB R R^o X g f x (hg x) (hf x)).
Qed.
