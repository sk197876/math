(** Federer (1969), 2.5.7, p. 98: L is the total scalar Lp vector lattice
    after the erratum p. 2, book p. 98 line 10. The proof retains countably
    measurable supports at infinity and does not impose finite total
    measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP FunctionLatticeUP FunctionLatticeLaws VectorFunctionLattice
  SummableRealFunctionLattice TotalScalarLpUP TotalScalarMeasurability TotalScalarLpClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_scalar_lp_subtract]: supporting vector difference
    closure in Federer 2.5.7, pp. 98–99 *)
Lemma total_scalar_lp_subtract (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (f g : X -> R) :
  total_scalar_lp mu p f -> total_scalar_lp mu p g ->
  total_scalar_lp mu p (fun x => (f x-g x)%R).
Proof.
move=> hf hg.
have hn := @total_scalar_lp_scale R X mu hm p (-1)%R g hg.
have hs := @total_scalar_lp_add R X mu hm p f _ hf hn.
have he : (fun x => (f x + -1*g x)%R)=(fun x => (f x-g x)%R).
  by apply: funext=> x; rewrite mulN1r.
by rewrite he in hs.
Qed.

(** Source for [total_scalar_lp_positive_part]: supporting lattice closure
    in Federer 2.5.7, pp. 98–99 Norm domination preserves membership even at
    the infinity endpoint. *)
Lemma total_scalar_lp_positive_part (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (f : X -> R) :
  total_scalar_lp mu p f -> total_scalar_lp mu p (fun x => Order.max (f x) 0%R).
Proof.
move=> hf; apply: (@total_scalar_lp_domination R X mu hm p f _ hf).
- exact: (@function_lattice_positive_part R X _ (@total_scalar_measurable_lattice R X mu hm) f hf.2.1).
- move=> x; case: (leP (f x) 0%R)=> h.
  + by rewrite normr0 normr_ge0.
  + exact: lexx.
Qed.

(** Source for [total_scalar_lp_minimum]: supporting binary minimum closure
    in Federer 2.5.7, p. 98 The identity min(f,g)=f-positive_part(f-g)
    avoids any constant-integrability assumption. *)
Lemma total_scalar_lp_minimum (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (f g : X -> R) :
  total_scalar_lp mu p f -> total_scalar_lp mu p g ->
  total_scalar_lp mu p (fun x => Order.min (f x) (g x)).
Proof.
move=> hf hg.
have hd := @total_scalar_lp_subtract R X mu hm p f g hf hg.
have hp := @total_scalar_lp_positive_part R X mu hm p _ hd.
have hs := @total_scalar_lp_subtract R X mu hm p f _ hf hp.
have he : (fun x => (f x-Order.max (f x-g x)%R 0%R)%R)=(fun x => Order.min (f x) (g x)).
  apply: funext=> x; case: (leP (f x) (g x))=> h.
  - by rewrite max_r ?subr_le0 // subr0.
  - by rewrite max_l ?subr_ge0 ?ltW // opprB addrCA subrr addr0.
by rewrite he in hs.
Qed.

(** Source for [total_scalar_lp_truncation]: nonnegative constant truncation
    required by the lattice definition in Federer 2.5.1, p. 91, for L in
    2.5.7, p. 98 The constant need not belong to L. *)
Lemma total_scalar_lp_truncation (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (c : R) (f : X -> R) :
  (0 <= c)%R -> total_scalar_lp mu p f ->
  total_scalar_lp mu p (fun x => Order.min (f x) c).
Proof.
move=> hc hf; apply: (@total_scalar_lp_domination R X mu hm p f _ hf).
- exact: (@function_lattice_truncation R X _ (@total_scalar_measurable_lattice R X mu hm) c f hc hf.2.1).
- move=> x; exact: nonnegative_ceiling_absolute_bound hc.
Qed.

(** Source for [total_scalar_lp_vector_lattice]: full lattice and
    vector-space laws for the corrected domain L in Federer 2.5.7, p. 98 All
    exponents 1 <= p <= infinity and the zero measure are included. *)
Theorem total_scalar_lp_vector_lattice (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p :
  1 <= p -> is_vector_function_lattice (total_scalar_lp mu p).
Proof.
move=> hp; split.
- constructor.
  + move=> f g; exact: (@total_scalar_lp_add R X mu hm p f g).
  + move=> c f hc; exact: (@total_scalar_lp_scale R X mu hm p c f).
  + move=> f g; exact: (@total_scalar_lp_minimum R X mu hm p f g).
  + move=> c f; exact: (@total_scalar_lp_truncation R X mu hm p c f).
  + move=> f g hf hg hfg; exact: (@total_scalar_lp_subtract R X mu hm p g f hg hf).
- split; first exact: (@total_scalar_lp_zero R X mu hm p hp).
  move=> c f; exact: (@total_scalar_lp_scale R X mu hm p c f).
Qed.
