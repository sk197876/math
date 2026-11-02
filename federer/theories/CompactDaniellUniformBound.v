(** Federer (1969), 2.6.4, p. 119: uniform bounds for a Daniell functional
    on functions with fixed compact support, supporting the product
    functional. The argument is the order-bound estimate of 2.5.13, pp.
    106–107. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws DaniellIntegralUP DaniellIntegralAlgebra
  CompactSupportFunctionUP CompactSupportFunctionLattice CompactCutoffUP CompactCutoff
  FunctionLatticeSeminormUP LatticeOrderAbsoluteBound DaniellSpaceCompactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_daniell_scaled_order_bound]: supporting
    two-sided order-interval bound for the final proposition in
    Federer 2.6.4, p. 119, obtained by the positive and
    negative parts used in 2.5.13, pp. 106–107. *)
Lemma compact_daniell_scaled_order_bound (R : realType) (X : topologicalType)
    (A : (X -> R) -> R) (u : X -> R) :
  is_daniell_integral (@compactly_supported_continuous_functions R X) A ->
  positive_function_lattice (@compactly_supported_continuous_functions R X) u ->
  exists C, 0<=C /\ forall f, compactly_supported_continuous_functions f ->
    forall e, 0<e -> (forall x, `|f x|<=e*u x) -> `|A f|<=e*C.
Proof.
move=> hA hu.
have hL := @compactly_supported_continuous_functions_lattice R X.
have hlin := @daniell_compact_support_linear R X A hA.
have hb := @daniell_integral_order_bounded R X _ A hA u hu.1.
have [c [hc hbound]] := @lattice_positive_interval_absolute_bound R X _ A hL hlin.1 u hu.1 hb.
exists (c+c); split; first exact (addr_ge0 hc hc).
move=> f hf e he hfe.
have hp : positive_function_lattice (@compactly_supported_continuous_functions R X) (fun x => Order.max (f x) 0).
  split; first exact (@function_lattice_positive_part R X _ hL f hf).
  by move=> x; rewrite le_max lexx orbT.
have hn : positive_function_lattice (@compactly_supported_continuous_functions R X) (fun x => Order.max (-f x) 0).
  split; first exact (@function_lattice_negative_part R X _ hL f hf).
  by move=> x; rewrite le_max lexx orbT.
have hep x : 0<=e*u x := mulr_ge0 (ltW he) (hu.2 x).
have hpu x : Order.max (f x) 0<=e*u x.
  rewrite ge_max hep andbT; exact: le_trans (ler_norm _) (hfe x).
have hnu x : Order.max (-f x) 0<=e*u x.
  rewrite ge_max hep andbT; apply: le_trans (ler_norm _) _; by rewrite normrN.
have hbp := @lattice_scaled_positive_interval_bound R X _ A hL hlin u _ e c he hp.1 hp.2 hpu hbound.
have hbn := @lattice_scaled_positive_interval_bound R X _ A hL hlin u _ e c he hn.1 hn.2 hnu hbound.
have hid : A (fun x => Order.max (f x) 0)=A f+A (fun x => Order.max (-f x) 0).
  rewrite -(daniell_integral_add hA hf hn.1); congr A; apply: funext=> x.
  by rewrite !maxEle; case: (lerP (f x) 0)=> h1; case: (lerP (-f x) 0)=> h2 /=; lra.
have hv : A f=A (fun x => Order.max (f x) 0)-A (fun x => Order.max (-f x) 0) by lra.
rewrite hv mulrDr; exact: le_trans (ler_normB _ _) (lerD hbp hbn).
Qed.

(** Source for [compact_daniell_fixed_support_bound]: supporting
    uniform continuity on a fixed compact support for Federer
    2.6.4, p. 119. The cutoff comes only from its
    sealed specification; no bound depends on the particular f. *)
Theorem compact_daniell_fixed_support_bound (R : realType) (X : topologicalType)
    (A : (X -> R) -> R) (K : set X) :
  hausdorff_space X -> locally_compact (@setT X) -> compact K ->
  is_daniell_integral (@compactly_supported_continuous_functions R X) A ->
  exists C, 0<=C /\ forall f, compactly_supported_continuous_functions f ->
    (forall x, ~K x -> f x=0) -> forall e, 0<e ->
    (forall x, K x -> `|f x|<=e) -> `|A f|<=e*C.
Proof.
move=> hh hl hK hA.
pose u := @compact_cutoff R X K hh hl hK.
have hu := @compact_cutoff_specification R X K hh hl hK.
have hup : positive_function_lattice (@compactly_supported_continuous_functions R X) u.
  split; first exact: compact_cutoff_function hu.
  move=> x; exact: (andP (compact_cutoff_range hu x)).1.
have [C [hC hb]] := @compact_daniell_scaled_order_bound R X A u hA hup.
exists C; split=> // f hf hz e he hfe; apply: (@hb f hf e he)=> x.
case: (pselect (K x))=> hx.
- rewrite /u (compact_cutoff_on_set hu hx) mulr1; exact: hfe x hx.
- rewrite (hz x hx) normr0; exact: mulr_ge0 (ltW he) (hup.2 x).
Qed.
