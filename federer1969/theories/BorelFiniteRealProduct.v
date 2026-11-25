(** Federer (1969), 3.2.22, p. 259: products
    of exact Borel scalar Jacobian representatives remain
    Borel. This uses only the real-line topology and
    the Borel product-map laws of 2.2.14, p. 70. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets cardinality topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground RealLineSeparability SeparableMetricBaseSealed
  CountableOpenBaseUP BorelFunctionUP BorelFunctionBasic BorelProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [borel_finite_real_product]: supporting the
    scalar Jacobian product in Federer 3.2.22,
    p. 259. The Borel pair map and continuous
    real multiplication prove the product Borel. The
    countable real base is used only through its opaque
    laws; no selected global scalar representative is added. *)
Lemma borel_finite_real_product (R:realType) (X:topologicalType)
    (f g:X->real_line_metric R):
  is_borel_function f ->is_borel_function g ->
  is_borel_function (fun x=>(f x*g x:real_line_metric R)).
Proof.
move=>hf hg.
have [D [hCount hDense]]:=@real_line_countable_dense R.
pose B:=@SeparableMetricBase.value R [the metricType R of real_line_metric R] D hCount hDense.
have hB:=@SeparableMetricBase.laws R [the metricType R of real_line_metric R] D hCount hDense.
have hPair:=@borel_pair_function X [the topologicalType of real_line_metric R]
  [the topologicalType of real_line_metric R] f g B B hB hB hf hg.
have hMul:continuous (fun p:real_line_metric R*real_line_metric R=>(p.1* p.2:real_line_metric R)).
  move=>p; apply:(@continuousM R [the topologicalType of (real_line_metric R*real_line_metric R)%type]
    fst snd p); [exact:cvg_fst|exact:cvg_snd].
exact:(borel_function_composition hPair (continuous_borel_function hMul)).
Qed.
