(** Federer (1969), 1.6.5, p. 26, final pairing computation. Supporting
    contraction rule for an ordered family: if the contracting one-forms are
    dual to the first factors and vanish on the rest, contraction retains
    the remaining factors. The proof transports the checked basis formula of
    1.5.2 through a linear map from a free vector space; the family in the
    target need not be a basis or independent. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From mathcomp.classical Require Import boolp.
From Federer Require Import SimpleVectors CovectorProductNaturality InteriorNaturality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [indexed_exterior_product_natural]: Federer 1.6.5,
    pp. 25-26, induced maps on exterior products. Supporting
    naturality for any indexed ordered product, including the
    initial and complementary index lists used in the proof. *)
Lemma indexed_exterior_product_natural (K : fieldType) (V W : lmodType K)
  (I : choiceType) (f : {linear V -> W}) (e : I -> V) m (t : m.-tuple I) :
  exterior_power_map f m (e_lambda e t) = e_lambda (fun i => f (e i)) t.
Proof.
apply: val_inj.
change (exterior_algebra_map f (component_val (e_lambda e t)) =
  component_val (e_lambda (fun i => f (e i)) t)).
by rewrite !e_lambdaE exterior_algebra_map_word -map_comp.
Qed.

Section Frame.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable W : lmodType K.
Variables n N : nat.
Hypothesis hn : (n <= N)%N.
Variable v : 'I_N -> W.
Variable a : 'I_n -> A_m W K^o 1.
Hypothesis hframe : forall j i,
  one_hom (a j) (v i) = if widen_ord hn j == i then 1 else 0.
Local Notation U := (GRing.Lmodule.clone K (free_vector K (Choice.clone 'I_N _)) _).
Local Notation d := (@delta K (Choice.clone 'I_N _)).
Local Notation hd := (free_basis K (Choice.clone 'I_N _)).
Local Notation omega := (fun i => one_form (dual_basis hd i)).
Local Notation F := (basis_synthesis v).
Local Notation lambda := (Lambda_initial hn).

(** Source for [frame_one_form_pullback]: Federer 1.6.5, p. 26,
    the forms omega_j composed with f on the chosen product factors.
    Supporting identity: their pullbacks to the free model are the
    first n dual basis forms. *)
Lemma frame_one_form_pullback j : A_m_dual F (a j) = omega (widen_ord hn j).
Proof.
apply: one_hom_injective; apply: hom_ext => x.
apply: (basis_linear_ext hd
  (hom_as_linear (one_hom (A_m_dual F (a j))))
  (hom_as_linear (one_hom (omega (widen_ord hn j))))) x => i.
change (one_hom (A_m_dual F (a j)) (d i) = one_hom (omega (widen_ord hn j)) (d i)).
rewrite !one_homE A_m_dualE one_formE dual_basisE (eq_sym i (widen_ord hn j)).
have ht : map_tuple F [tuple d i] = [tuple v i].
  apply: val_inj; change ([:: F (d i)] = [:: v i]); by rewrite basis_synthesisE.
rewrite ht; exact: hframe.
Qed.

(** Source for [frame_form_pullback]: Federer 1.6.5, p. 26,
    product of the forms omega_j composed with f. Supporting
    identity identifying that product with the initial dual product
    in the free model, by multiplicativity of pullback. *)
Lemma frame_form_pullback :
  A_m_dual F (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) a) =
    omega_lambda h2 omega lambda.
Proof.
rewrite one_forms_wedge_natural /omega_lambda.
congr (one_forms_wedge _ _ _ _).
apply: funext => j.
rewrite /Lambda_initial /initial_tuple tnth_mktuple.
exact: frame_one_form_pullback.
Qed.

(** Source for [interior_initial_frame]: Federer 1.6.5, p. 26,
    final contraction of the transverse factors. Supporting
    general rule: the product dual to the initial factors removes
    exactly those factors, with sign one. The remaining factors
    may be dependent, and the statement includes empty blocks. *)
Theorem interior_initial_frame :
  left_interior h2 hn (e_lambda v (ord_tuple N))
    (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) a) =
      e_lambda v (val (top_complement lambda)).
Proof.
have hdual : forall i j, omega i [tuple d j] = if i == j then 1 else 0.
  by move=> i j; rewrite one_formE dual_basisE (eq_sym j i).
have hc := @left_interior_natural K h2 U W F n N hn
  (e_lambda d (val (Lambda_top N)))
  (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) a).
rewrite frame_form_pullback in hc.
change (exterior_power_map F (N-n)
  (D_upper h2 (e_lambda d (val (Lambda_top N))) hn (omega_lambda h2 omega lambda)) =
  left_interior h2 hn (exterior_power_map F N (e_lambda d (ord_tuple N)))
    (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) a)) in hc.
rewrite (@D_upper_basis K h2 U N d omega hd hdual n hn lambda)
  /top_complement initial_complement_N expr0 scale1r
  !indexed_exterior_product_natural in hc.
have hf : (fun i => F (d i)) = v by apply: funext => i; exact: basis_synthesisE.
by rewrite hf in hc; exact: esym hc.
Qed.
End Frame.
