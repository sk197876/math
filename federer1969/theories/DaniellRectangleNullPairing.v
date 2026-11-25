(** Federer (1969), 2.5.20, p. 114: a rectangle outside the support of mu
    gives almost-vanishing kernel pairings. Scalar uniqueness in 2.5.9, p.
    100, applied after multiplication by a supported test on X, proves this
    intermediate step. Source context: CompactFunctionSupportedTests.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MeasureUP RadonMeasureUP
  MeasureAlmostUP MeasureSplit CountablyMeasurableBasic MeasurableFunctionUP
  MeasurableIdentityCriterion MeasurableTotalBasic BorelFunctionBasic
  TotalScalarMeasurability TotalScalarArithmetic TotalScalarLpUP FunctionLatticeUP FunctionLatticeRegularityUP
  CompactSupportFunctionUP CompactSupportFunctionLattice CompactSupportProducts
  CompactSeparatedProduct SeparatedFunctionSupport CompactSupportDaniellSupport
  DaniellIntegralUP DaniellSpaceWeakTopology DaniellSpaceCompactness DaniellSpaceEmbedding
  DaniellDisintegrationUP RealIntegralFunctionalUP RegularLatticeZeroPairing
  SummableRealFunctionUP MeasureIntegralUP SubtypeCompactHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [daniell_rectangle_supported_pairing_zero]:
    supporting vanishing step for the fibre support assertion
    in Federer 2.5.20, p. 114. For a rectangle U times V
    outside spt mu, every g supported in U and f supported
    in V satisfies g(x)k(x)(f)=0 almost everywhere.
    Regularity refers to the actual representing measure. *)
Theorem daniell_rectangle_supported_pairing_zero (R : realType) (X Y : topologicalType)
    (phi : set X -> \bar R) (mu : ((X*Y) -> R) -> R)
    (F : (X -> R) -> R)
    (k : X -> daniell_weak_space (@compactly_supported_continuous_functions R Y))
    (U : set X) (V : set Y) (g : X -> R) (f : Y -> R) :
  hausdorff_space (X*Y)%type -> compact (@setT X) -> compact (@setT Y) ->
  is_measure phi -> is_radon_measure phi ->
  is_real_integral_functional phi (@compactly_supported_continuous_functions R X) F ->
  is_function_lattice_regular (@compactly_supported_continuous_functions R X) phi ->
  is_daniell_integral (@compactly_supported_continuous_functions R (X*Y)%type) mu ->
  is_daniell_integral_decomposition phi mu k ->
  U `*` V `<=` ~` compact_support_daniell_support mu ->
  compactly_supported_continuous_functions g -> real_function_support g `<=` U ->
  compactly_supported_continuous_functions f -> real_function_support f `<=` V ->
  measure_almost_everywhere phi [set x | g x*k x f=0].
Proof.
move=> hh hX hY hm hr hrep hreg hmu hk hUV hg hgU hf hfV.
have hid := (measurable_identity_iff_open_sets hm).2 (radon_open_measurable hr).
have hgm := real_total_scalar_measurable hm
  (measurable_total_borel_postcomposition hm hid (continuous_borel_function hg.1)).
have hfm := real_total_scalar_measurable hm
  (measurable_total_borel_postcomposition hm (daniell_decomposition_measurable hk)
    (continuous_borel_function (daniell_weak_evaluation_continuous hf))).
have hw := @measurable_total_scalar_product R X phi hm g (fun x => k x f) hgm hfm.
have hcount := finite_measurable_set_countably_measurable
  (measure_measurable_whole hm) (radon_compact_finite hr hX).
have hXY : compact (@setT (X*Y)%type).
  have he : (@setT X) `*` (@setT Y)=setT by apply/seteqP; split=> p _; split.
  rewrite -he; exact: compact_setX hX hY.
apply: (@regular_lattice_zero_pairing_almost_zero R X
  (@compactly_supported_continuous_functions R X)
  (@compactly_supported_continuous_functions_lattice R X) F phi hm
  (fun x => g x*k x f) hrep hreg hcount hw)=> theta ht.
pose a x := theta x*g x.
have ha := compact_support_continuous_multiplier ht.1 hg.
pose u (p : X*Y) := a p.1*f p.2.
have hu := compactly_supported_separated_product ha hf.
have hs : real_function_support u `<=` ~` compact_support_daniell_support mu.
  move=> [x y] hp; have [hx hy] := separated_function_support_subset hp.
  apply: hUV; split; last exact: hfV y hy.
  apply: hgU; exact: real_product_support_right hx.
have hz := @daniell_support_vanishing R (X*Y)%type hh
  (compact_space_locally_compact hXY) mu u hmu hu hs.
have hi := daniell_decomposition_integral hk hu.
rewrite hz in hi.
have he : (fun x => k x (fun y => u (x,y)))=(fun x => theta x*(g x*k x f)).
  apply: funext=> x; rewrite /u /a.
  by rewrite /= (daniell_compact_support_linear (daniell_decomposition_values hk x)).2 // mulrA.
by rewrite he in hi.
Qed.
