(** Federer (1969), 4.1.7, pp. 355–357: the
    original real comass agrees with the induced
    multilinear norm used in 4.1.6. This supporting
    equality uses the released simple-unit factors
    from 1.8.1, p. 38. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  AlternatingForms AlternatingPairing CovectorProducts AlternatingFormNormUP
  AlternatingFormUnitBounds ComassUP ComassBounds ComassTupleBounds SimpleUnitFactors.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_comass_induced_norm]: equality
    of the two original real-form norms used in
    Federer 4.1.7, pp. 355–357, by the unit-factor
    parametrisation of 1.8.1, p. 38. *)
Theorem positive_comass_induced_norm (R:realType) (h2:(1+1:R)!=0)
    (V:lmodType R) (B:V->V->R) (hB:is_inner_product B) m (hm:(0<m)%N)
    (P:A_m V R^o m->R)
    (hP:is_alternating_form_norm (inner_norm hB) (fun c:R^o=>`|c|) P)
    (phi:A_m V R^o m) c:
  is_comass h2 hB phi c -> c = P phi.
Proof.
move=>hc; have hNX:=inner_norm_real_norm hB.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply:(@comass_least_upper_bound R h2 V B hB m phi c hc (P phi))=>xi hxi.
  have [u [hu ->]]:=@simple_unit_ball_factors R h2 V B hB m hm xi hxi.
  rewrite pairing_e_lambda.
  apply:(le_trans (ler_norm _)).
  apply:(alternating_form_unit_tuple_bound hNX (hP phi))=>i.
  by rewrite tnth_map tnth_ord_tuple; exact:hu.
- apply:(alternating_form_unit_tuple_least hNX (@scalar_absolute_value_norm R)
    (hP phi) (@comass_nonnegative R h2 V B hB m phi c hm hc))=>t ht.
  exact:(@comass_unit_tuple_bound R h2 V B hB m hm phi c hc t ht).
Qed.
