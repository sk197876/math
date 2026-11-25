(** Federer (1969), 2.5.7, p. 98: the finite seminorm restricted to
    total-domain Lp functions. The finite projection below is exact on Lp;
    values outside Lp are irrelevant to the abstract seminorm laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP TotalScalarLpUP TotalScalarLpNormLaws TotalScalarLpNormOrder
  TotalScalarLpClosure FunctionLatticeSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_total_scalar_lp_norm]: finite value of phi_(p) on L
    in Federer 2.5.7, p. 98 This uses the existing abstract norm and does
    not construct a different norm. *)
Definition finite_total_scalar_lp_norm (R : realType) (X : choiceType)
    (mu : set X -> \bar R) p (f : X -> R) := fine (total_scalar_lp_norm mu p f).

(** Source for [finite_total_scalar_lp_norm_exact]: exact identification
    with the extended norm on L in Federer 2.5.7, p. 98 *)
Lemma finite_total_scalar_lp_norm_exact (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (f : X -> R) :
  total_scalar_lp mu p f -> (finite_total_scalar_lp_norm mu p f)%:E=total_scalar_lp_norm mu p f.
Proof. move=> hf; rewrite /finite_total_scalar_lp_norm fineK //; exact: (@total_scalar_lp_finite_value R X mu hm p f hf). Qed.

(** Source for [finite_total_scalar_lp_norm_laws]: supporting abstract
    seminorm laws for the corrected total-domain space in Federer 2.5.7, p.
    98 Both finite exponents and infinity are covered. *)
Theorem finite_total_scalar_lp_norm_laws (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p :
  is_finite_function_seminorm (total_scalar_lp mu p) (finite_total_scalar_lp_norm mu p).
Proof.
constructor.
- move=> f hf; apply: fine_ge0.
  exact: (@total_scalar_lp_norm_nonnegative R X mu hm p f hf.1 hf.2.1).
- move=> c f hf.
  have hs := @total_scalar_lp_scale R X mu hm p c f hf.
  have he := @total_scalar_lp_norm_scale R X mu hm p c f hf.1 hf.2.1.
  rewrite -(@finite_total_scalar_lp_norm_exact R X mu hm p _ hs)
    -(@finite_total_scalar_lp_norm_exact R X mu hm p f hf) -EFinM in he.
  by injection he.
- move=> f g hf hg.
  have hs := @total_scalar_lp_add R X mu hm p f g hf hg.
  have hh := @total_scalar_lp_norm_triangle R X mu hm p f g hf.1 hf.2.1 hg.2.1.
  rewrite -(@finite_total_scalar_lp_norm_exact R X mu hm p _ hs)
    -(@finite_total_scalar_lp_norm_exact R X mu hm p f hf)
    -(@finite_total_scalar_lp_norm_exact R X mu hm p g hg) -EFinD lee_fin in hh.
  exact: hh.
Qed.

(** Source for [finite_total_scalar_lp_norm_order]: real-valued order
    comparison used to bound positive variations in Federer 2.5.7, p. 98 *)
Lemma finite_total_scalar_lp_norm_order (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (f g : X -> R) :
  total_scalar_lp mu p f -> total_scalar_lp mu p g ->
  (forall x, (`|f x| <= `|g x|)%R) ->
  (finite_total_scalar_lp_norm mu p f <= finite_total_scalar_lp_norm mu p g)%R.
Proof.
move=> hf hg hfg.
have hh := @total_scalar_lp_norm_order R X mu hm p f g hf.1 hf.2.1 hg.2.1 hfg.
by rewrite -(@finite_total_scalar_lp_norm_exact R X mu hm p f hf)
  -(@finite_total_scalar_lp_norm_exact R X mu hm p g hg) lee_fin in hh.
Qed.
