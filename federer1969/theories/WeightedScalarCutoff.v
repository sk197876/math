(** Federer (1969), 3.2.20, p. 257: source integrands
    on the disjoint compact images are the cutoffs of one finite
    approximate-Jacobian representative. The existing opaque
    characteristic function supplies the cutoff laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  TotalScalarCutoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_scalar_cutoff_graph]: supporting exact
    source graph identity in the summation in Federer 3.2.20,
    p. 257, with the subset convention of 2.4.10, p. 85.
    The arbitrary extended weight may be infinite; it is multiplied
    by the actual finite cutoff density, including density zero. *)
Lemma weighted_scalar_cutoff_graph (R : realType) (X : Type)
    (A : set X) (w : X -> \bar R) (J : X -> R) x y :
  partial_function_graph (partial_function_zero_extension (0:extended_real_line R) A
    (partial_function_total (fun x=>w x* (J x)%:E : extended_real_line R))) x y <->
  partial_function_graph (partial_function_total
    (fun x=>w x* (total_scalar_cutoff A J x)%:E : extended_real_line R)) x y.
Proof.
case: (pselect (A x))=> hx.
- rewrite (partial_function_zero_extension_on _ _ _ hx).
  change (w x* (J x)%:E=y <-> w x* (total_scalar_cutoff A J x)%:E=y).
  by rewrite (total_scalar_cutoff_on J hx).
- rewrite (partial_function_zero_extension_off _ _ _ hx).
  change (y=0 <-> w x* (total_scalar_cutoff A J x)%:E=y).
  rewrite (total_scalar_cutoff_off J hx) mule0; split=> hy; exact: (esym hy).
Qed.

(** Source for [scalar_cutoff_embedding_graph]: supporting finite
    source density in the chart summation of Federer 3.2.20,
    p. 257. This is the weight-one case of the exact
    weighted cutoff graph, with finite values embedded in the
    extended real line. *)
Lemma scalar_cutoff_embedding_graph (R : realType) (X : Type)
    (A : set X) (J : X -> R) x y :
  partial_function_graph (partial_function_zero_extension (0:extended_real_line R) A
    (partial_function_total (fun x=>(J x)%:E : extended_real_line R))) x y <->
  partial_function_graph (partial_function_total
    (fun x=>(total_scalar_cutoff A J x)%:E : extended_real_line R)) x y.
Proof.
have hOneJ : (fun x=>1* (J x)%:E : extended_real_line R)=
    (fun x=>(J x)%:E : extended_real_line R).
  by apply: funext=> t; rewrite mul1e.
have hOneP : (fun x=>1* (total_scalar_cutoff A J x)%:E : extended_real_line R)=
    (fun x=>(total_scalar_cutoff A J x)%:E : extended_real_line R).
  by apply: funext=> t; rewrite mul1e.
have hh := @weighted_scalar_cutoff_graph R X A (fun _=>1) J x y.
by rewrite hOneJ hOneP in hh.
Qed.
