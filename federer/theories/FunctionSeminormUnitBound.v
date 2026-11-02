(** Federer (1969), 2.5.7, pp. 98–99: the unit-ball bound implies |mu(f)| <=
    M norm(f), including zero seminorm. Erratum p. 2, book p. 98 lines
    10–11, requires total functions and the closed unit ball. This is a
    supporting abstract seminorm argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FunctionLatticeUP LatticeAdditiveFunctional VectorFunctionLattice FunctionLatticeSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [function_seminorm_zero]: supporting zero-member fact for the
    corrected unit ball in Federer 2.5.7, p. 98 *)
Lemma function_seminorm_zero (R : realType) (X : Type)
    (L : set (X -> R)) (N : (X -> R) -> R)
    (hL : is_vector_function_lattice L) (hN : is_finite_function_seminorm L N) :
  N (fun _ => 0)=0.
Proof.
have hh := @function_seminorm_scale R X L N hN 0 (fun _ => 0) hL.2.1.
have he : (fun _ : X => (0 : R)*0)=(fun _ => 0) by apply: funext=> x; rewrite mul0r.
by rewrite he normr0 mul0r in hh.
Qed.

(** Source for [functional_unit_bound_nonnegative]: zero lies in the
    corrected ball of Federer 2.5.7, p. 98, so every upper bound is
    nonnegative, even for the zero space *)
Lemma functional_unit_bound_nonnegative (R : realType) (X : Type)
    (L : set (X -> R)) (A N : (X -> R) -> R)
    (hL : is_vector_function_lattice L) (hA : is_linear_functional_on_functions L A)
    (hN : is_finite_function_seminorm L N) M :
  (forall f, L f -> N f <= 1 -> `|A f| <= M) -> 0 <= M.
Proof.
move=> hb.
have hn : N (fun _ => 0) <= 1 by rewrite (@function_seminorm_zero R X L N hL hN) ler01.
have hh := hb _ hL.2.1 hn.
by rewrite (@lattice_additive_zero R X L A hL.1 hA.1 (fun _ => 0) hL.2.1) normr0 in hh.
Qed.

(** Source for [unit_bounded_functional_annihilates_kernel]: zero-seminorm
    case of the bound used in Federer 2.5.7, pp. 98–99 Arbitrarily large
    scalar multiples remain in the ball. *)
Lemma unit_bounded_functional_annihilates_kernel (R : realType) (X : Type)
    (L : set (X -> R)) (A N : (X -> R) -> R)
    (hL : is_vector_function_lattice L) (hA : is_linear_functional_on_functions L A)
    (hN : is_finite_function_seminorm L N) M :
  (forall f, L f -> N f <= 1 -> `|A f| <= M) ->
  forall f, L f -> N f=0 -> A f=0.
Proof.
move=> hb f hf hn; have hM := @functional_unit_bound_nonnegative R X L A N hL hA hN M hb.
apply/eqP; apply/negPn; apply/negP=> ha.
have hap : 0 < `|A f| by rewrite normr_gt0.
pose c := (M+1)/`|A f|.
have hc : 0 <= c by rewrite /c divr_ge0 // addr_ge0 //; exact: ler01.
have hcf := hL.2.2 c f hf.
have hcn : N (fun x => c*f x) <= 1.
  by rewrite (@function_seminorm_scale R X L N hN c f hf) hn mulr0 ler01.
have hh := hb _ hcf hcn.
rewrite (hA.2 c f hf) normrM (ger0_norm hc) /c mulfVK ?gt_eqF // in hh.
by move: hh; rewrite gerDl ler10.
Qed.

(** Source for [unit_bounded_functional_norm_bound]: supporting norm
    inequality in Federer 2.5.7, pp. 98–99 The zero-seminorm case is proved
    separately rather than dividing by zero. *)
Theorem unit_bounded_functional_norm_bound (R : realType) (X : Type)
    (L : set (X -> R)) (A N : (X -> R) -> R)
    (hL : is_vector_function_lattice L) (hA : is_linear_functional_on_functions L A)
    (hN : is_finite_function_seminorm L N) M :
  (forall f, L f -> N f <= 1 -> `|A f| <= M) ->
  forall f, L f -> `|A f| <= M * N f.
Proof.
move=> hb f hf.
have hn := @function_seminorm_nonnegative R X L N hN f hf.
case: (eqVneq (N f) 0)=> [he|he].
- rewrite (@unit_bounded_functional_annihilates_kernel R X L A N hL hA hN M hb f hf he).
  by rewrite normr0 he mulr0.
- have hp : 0 < N f by rewrite lt_neqAle eq_sym he hn.
  have hi : 0 <= (N f)^-1 by rewrite invr_ge0.
  have hcf := hL.2.2 (N f)^-1 f hf.
  have hcn : N (fun x => (N f)^-1*f x) <= 1.
    by rewrite (@function_seminorm_scale R X L N hN _ f hf) (ger0_norm hi) mulVf //.
  have hh := hb _ hcf hcn.
  rewrite (hA.2 (N f)^-1 f hf) normrM (ger0_norm hi) mulrC in hh.
  by rewrite ler_pdivrMr in hh.
Qed.
