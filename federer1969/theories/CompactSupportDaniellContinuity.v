(** Federer (1969), 2.5.13, pp. 106–107: compactness and order boundedness
    imply continuity on increasing sequences. We use g-h_0 as their common
    compactly supported nonnegative bound, avoiding a change of the original
    sequence. Indices start at zero rather than one. The cutoff is used only
    through its sealed laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import FunctionLatticeUP DaniellIntegralUP LatticeAdditiveFunctional FunctionLatticeSeminormUP
  MonotoneDaniellIntegralUP ExtendedRealOrderLimit RealErrorOrderLimit IncreasingScalarErrors
  CompactSupportFunctionUP CompactSupportFunctionLattice CompactCutoffUP CompactCutoff
  CompactIncreasingUniformApproximation LatticeOrderAbsoluteBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_support_increasing_functional_limit]: the concluding
    limit in Federer 2.5.13, p. 107, with the uniform approximation and
    order-interval estimate of its proof. The functional need not be
    positive. *)
Theorem compact_support_increasing_functional_limit (R : realType) (X : topologicalType)
    (A : (X -> R) -> R) (hh : hausdorff_space X) (hl : locally_compact (@setT X)) :
  is_linear_functional_on_functions (@compactly_supported_continuous_functions R X) A ->
  (forall u, positive_function_lattice (@compactly_supported_continuous_functions R X) u ->
    exists b, forall k, lattice_positive_order_interval (@compactly_supported_continuous_functions R X) u k -> A k<=b) ->
  forall f g, (forall n, compactly_supported_continuous_functions (f n)) ->
    compactly_supported_continuous_functions g -> real_functions_increase_to f g ->
    extended_order_limit (fun n => (A (f n))%:E) (A g)%:E.
Proof.
move=> hA hb f g hf hg hi.
pose L := @compactly_supported_continuous_functions R X.
have hL := @compactly_supported_continuous_functions_lattice R X.
have hdiff n x := @increasing_scalar_error_bounds R X f g hi n x.
have hfg n : function_le (f n) g.
  move=> x; have h := (andP (hdiff n x)).1; by rewrite subr_ge0 in h.
pose d n x := g x-f n x.
have hd n : L (d n) := @function_lattice_ordered_difference R X L hL (f n) g (hf n) hg (hfg n).
pose H := d 0%N.
pose K := real_function_support H.
have hK : compact K := (hd 0%N).2.
pose u := @compact_cutoff R X K hh hl hK.
have hu := @compact_cutoff_specification R X K hh hl hK.
have huL : L u := compact_cutoff_function hu.
have hu0 : function_nonnegative u by move=> x; exact: (andP (compact_cutoff_range hu x)).1.
have [c [hc hbound]] := @lattice_positive_interval_absolute_bound R X L A hL hA.1 u huL (hb u (conj huL hu0)).
have hval n : A (d n)=A g-A (f n).
  have hadd := hA.1 (f n) (d n) (hf n) (hd n).
  have heq : (fun x => f n x+d n x)=g by apply: funext=> x; rewrite /d addrCA subrr addr0.
  rewrite heq in hadd; by rewrite hadd addrAC subrr add0r.
apply: real_error_extended_order_limit=> e he.
have hcp : c<c+1 by rewrite ltrDl; exact: ltr01.
have hden : 0<c+1 := le_lt_trans hc hcp.
pose delta := e/(c+1).
have hdelta : 0<delta by rewrite /delta divr_gt0.
have [N hN] := @compact_increasing_uniform_approximation R X K f g delta hK
  (fun n => (hf n).1) hg.1 hi hdelta.
exists N=> n hn.
have hp : function_nonnegative (d n) by move=> x; exact: (andP (hdiff n x)).1.
have hdu x : d n x<=delta*u x.
  case: (pselect (K x))=> hx.
  - rewrite /u (compact_cutoff_on_set hu hx) mulr1; exact: ltW (hN n hn x hx).
  - have hH : H x=0 := real_function_zero_off_support hx.
    have hbd : d n x<=H x := (andP (hdiff n x)).2.
    have hz : d n x<=0 by rewrite hH in hbd.
    apply: le_trans hz _; exact: mulr_ge0 (ltW hdelta) (hu0 x).
have h := @lattice_scaled_positive_interval_bound R X L A hL hA u (d n) delta c hdelta (hd n) hp hdu hbound.
rewrite hval distrC in h; apply: le_lt_trans h _.
have hm : delta*c<delta*(c+1) by rewrite ltr_pM2l //.
by rewrite /delta divfK ?gt_eqF // in hm.
Qed.
