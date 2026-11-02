(** Federer (1969), 2.5.14, p. 108: supporting absolute bounds for the
    compactness proof of vector-functional continuity. Symmetry of the
    norm-bounded class turns the one-sided bound in 2.5.12(5), p. 103, into
    an absolute-value bound. Source context:
    OrderBoundedVectorFunctionalUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP FunctionLatticeUP VectorDaniellHypotheses
  OrderBoundedVectorFunctionalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [order_bounded_vector_zero]: linearity forces
    T(0)=0, supporting the variation estimate invoked in
    Federer 2.5.14, p. 108, from 2.5.12(5), p. 103. *)
Lemma order_bounded_vector_zero (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (L : set (X -> R)) (Q : set (X -> E))
    (T : (X -> E) -> R) : is_vector_function_space Q ->
  is_order_bounded_vector_functional N L Q T -> T (fun _=>0)=0.
Proof.
move=> hQ hT.
have he := @order_bounded_vector_scale R X E N L Q T hT 0 (fun _=>0) (vector_function_space_zero hQ).
have hz : (fun _ : X=>0*:(0 : E))=(fun _=>0) by apply: funext=> x; rewrite scale0r.
by rewrite hz mul0r in he.
Qed.

(** Source for [order_bounded_vector_absolute_bound]: symmetry
    gives a nonnegative absolute bound on the class nu o w<=f,
    supporting the compactness proof of Federer 2.5.14, p. 108. *)
Lemma order_bounded_vector_absolute_bound (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (L : set (X -> R)) (Q : set (X -> E)) (T : (X -> E) -> R)
    (f : X -> R) : is_vector_function_space Q ->
  is_order_bounded_vector_functional N L Q T -> positive_function_lattice L f ->
  exists c : R, 0<=c /\ forall w, Q w -> function_le (fun x=>N (w x)) f -> `|T w|<=c.
Proof.
move=> hQ hT hf; have [c hc] := @order_bounded_vector_bound R X E N L Q T hT f hf.
have hz : function_le (fun _ : X=>N (0 : E)) f.
  by move=> x; rewrite (real_seminorm_zero hN.1); exact: hf.2.
have hc0 := hc _ (vector_function_space_zero hQ) hz.
rewrite (order_bounded_vector_zero hQ hT) in hc0.
exists c; split=> // w hw hwf.
have hneg := @vector_function_space_scale R X E Q hQ (-1) w hw.
have hnf : function_le (fun x=>N (-1*:w x)) f.
  move=> x; rewrite (real_seminorm_scale hN.1) normrN normr1 mul1r; exact: hwf.
have hn := hc _ hneg hnf.
rewrite (@order_bounded_vector_scale R X E N L Q T hT (-1) w hw) mulN1r in hn.
rewrite ler_norml; apply/andP; split; last exact: hc w hw hwf.
by rewrite lerNl; exact: hn.
Qed.

(** Source for [order_bounded_vector_scaled_bound]: rescaling
    nu o w<=delta f gives |T(w)|<=delta c, the vector
    counterpart of the estimate used in Federer 2.5.13,
    p. 107, as invoked in 2.5.14, p. 108. *)
Lemma order_bounded_vector_scaled_bound (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (L : set (X -> R)) (Q : set (X -> E)) (T : (X -> E) -> R)
    (f : X -> R) (c d : R) (w : X -> E) :
  is_vector_function_space Q -> is_order_bounded_vector_functional N L Q T ->
  (forall v, Q v -> function_le (fun x=>N (v x)) f -> `|T v|<=c) ->
  0<d -> Q w -> function_le (fun x=>N (w x)) (fun x=>d*f x) -> `|T w|<=d*c.
Proof.
move=> hQ hT hb hd hw hwf.
have hdi : 0<=d^-1 by rewrite invr_ge0; exact: ltW hd.
have hscaled := @vector_function_space_scale R X E Q hQ (d^-1) w hw.
have hsf : function_le (fun x=>N (d^-1*:w x)) f.
  move=> x; rewrite (real_seminorm_scale hN.1) (ger0_norm hdi).
  have h : d^-1*N (w x)<=d^-1*(d*f x).
    by rewrite ler_pM2l ?invr_gt0 //; exact: hwf.
  by rewrite mulrA mulVf ?gt_eqF // mul1r in h.
have hh := hb _ hscaled hsf.
rewrite (@order_bounded_vector_scale R X E N L Q T hT (d^-1) w hw) normrM (ger0_norm hdi) in hh.
have h : d*(d^-1*`|T w|)<=d*c by rewrite ler_pM2l.
by rewrite mulrA mulfV ?gt_eqF // mul1r in h.
Qed.
